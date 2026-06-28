import IterTree.QuotientTrick
import Lean

namespace IterTree

section StateMachine

structure Effect : Type (e + 1) where
  In : Type e
  Out : In → Type e

instance : HOr Effect Effect Effect where
  hOr e₁ e₂ := {
    In := e₁.In ⊕ e₂.In
    Out := fun
      | .inl i => e₁.Out i
      | .inr i => e₂.Out i
  }

class Subeffect (E₁ E₂ : Effect) where
  incl_In : E₁.In → E₂.In
  incl_Out : ∀ {i : E₁.In}, E₁.Out i → E₂.Out (incl_In i)

@[grind cases]
inductive Obs (E : Effect.{e}) (R : Type v) (K : Type k) where
| ret : R → Obs E R K
| tau : K → Obs E R K
| vis : (eff : E.In) → (E.Out eff → K) → Obs E R K

variable {E : Effect.{e}}

@[simp, grind]
def Obs.mapState (f : α → β) : Obs E R α → Obs E R β
| .ret v => .ret v
| .tau st => .tau <| f st
| .vis ev k => .vis ev (fun x => f (k x))

@[simp, grind]
def Obs.bindVal (f : α → Obs E β K) : Obs E α K → Obs E β K
| .ret v => f v
| .tau st => .tau st
| .vis ev k => .vis ev k


structure iTree (E : Effect.{e}) (R : Type v) where
  {State : Type s}
  curr : State
  step : State → Obs E R State

/-

NOTE:

An alternate representation of this interface would be to have `curr : State` be the implementation of
an `iTree E R`, and assign to each `State` type a particular `step` function. This is closer to the
`Std.Iter` API I was originally inspired by.

-/

namespace iTree

variable {E : Effect.{e}} {R : Type v}

/-- The looping computation -/
def loop.{s} : iTree E R where
  curr : PUnit.{s+1} := ⟨⟩
  step _ := .tau .unit

instance : Inhabited (iTree E R) := ⟨loop⟩

abbrev currStep (it : iTree E R) : Obs E R (it.State) := it.step it.curr

def unfold (it : iTree E R) : Obs E R (iTree E R) :=
  match it.currStep with
  | .ret v => .ret v
  | .tau next => .tau {it with curr := next}
  | .vis ev k => .vis ev (fun x => {it with curr := (k x)})

/- theorem unfold_cases (it : iTree E R) : -/
/-     (∃ v, it.unfold = .ret v) ∨ -/
/-     (∃ (α : Type _) (ev : E α) (k : α → iTree E R), it.unfold = .vis ev k) ∨ -/
/-     (∃ it', it.unfold = .tau it') := -/
/-   match it.unfold with -/
/-   | .ret v => .inl ⟨v, rfl⟩ -/
/-   | .vis (A := α) ev k => .inr <| .inl ⟨α, ev, k, rfl⟩ -/
/-   | .tau next => .inr <| .inr ⟨next, rfl⟩ -/
/- grind_pattern unfold_cases => it.unfold -/

def ret.{s} (r : R) : iTree E R where
  curr : PUnit.{s+1} := ⟨⟩
  step _ := .ret r

def vis (ev : E.In) (k : E.Out ev → iTree E R) : iTree E R where
  curr : Unit ⊕ (inp : E.Out ev) × (k inp).State := .inl ⟨⟩
  step
  | .inl ⟨⟩ => .vis ev (fun a => .inr <| ⟨a, (k a).curr⟩)
  | .inr ⟨a, s⟩ => (k a).step s |>.mapState (.inr ⟨a, ·⟩)

def tau (it : iTree E R) : iTree E R where
  -- We basically generate an artificial prior element in the state.
  curr : Unit ⊕ it.State  := .inl ⟨⟩
  step
  | .inl ⟨⟩ => .tau <| .inr <| it.curr
  | .inr s => it.step s |>.mapState (.inr)

end iTree

@[coe]
abbrev Obs.toITree : Obs E R (iTree E R) → iTree E R
| .tau it => iTree.tau it
| .vis ev k => iTree.vis ev k
| .ret v => iTree.ret v

namespace iTree

/--
  After the computation of the interaction tree `it`, we simply continue with the
  computation given by `f`. We encode the information of the continuation in the
  closure, to dodge problems with termination.
-/
def bindLeft {α β} (f : α → iTree E β)(it : iTree E α) : iTree E β where
    curr : it.State ⊕ (a : α) × (f a).State := .inl it.curr
    step st :=
      match st with
      | .inl curr =>
        it.step curr
        |>.mapState .inl
        |>.bindVal
        -- TODO: Optimization and helps only requiring strong bisimulation
        -- for monad laws.
        /- fun v => (f v).currStep.mapState (.inr ⟨v, ·⟩) -/
        fun v => .tau <| .inr ⟨v, (f v).curr⟩
      | .inr ⟨a, st⟩ =>
        (f a).step st
        |>.mapState (.inr ⟨a, ·⟩)

instance : Bind (iTree E) := ⟨(·.bindLeft ·)⟩
instance : Pure (iTree E) := ⟨ret⟩
instance : Monad (iTree E) where

/- def iter {I} (step : I → iTree E (I ⊕ R)) (init : I) : iTree E R := -/
/-   (step init).bindLeft fun -/
/-   | .inl updated => .tau (iter step updated) -/
/-   | .inr res => .ret res -/
def iter {I} (f : I → iTree E (I ⊕ R)) (init : I) : iTree E R where
  curr : (i : I) × (f i).State := ⟨init, f init |>.curr⟩
  step
  | ⟨i, st⟩ =>
    (f i).step st
    |>.mapState (⟨i, ·⟩)
    |>.bindVal fun
    | .inl i' => .tau <| ⟨i', (f i').curr⟩
    | .inr res => .ret res

end iTree

section EqualitiesOverITrees

/-

There are actually many notions of equality that can be given to iTrees.

There's strict equality, which is not very useful. In particular, you have
to care about the internal state of your iTree.

Then there is an "extensional" equality, or "observational" equality, which
cares only for the observable behaviour of iTrees. In particular, it does
away with the details of the internal state, and only cares for the `Obs`
produced by the `step` function.

However, this is not the best notion of equality either. We also have
equivalences between iTrees which are equivalent in their observations if
we're allowed to skip a finite amount of `tau` steps from either `iTree`.
This notion is called "equivalence up to tau", and captures more faithfully
the concept of what a "computation" is.
-/

/-

To define the right notion, we have to define what is a weak bisimulation.
But before getting there, it might be usefl to warm up these definitions
on strong bisimulations first.

-/

section StrongBisimulation

local instance : Std.Refl (Eq (α := α)) where refl := .refl
local instance : Std.Symm (Eq (α := α)) where symm _ _:= .symm

variable {E : Effect.{e}}{R : Type ret}

/-

We define a weaker version of equality, observational equality,
which also corresponds with a strong bisimulation.

-/

-- NOTE: Names of things
-- lift (?). Maybe with postfix F? ObsRelF? `eqitF` maybe
-- coinduction template

-- TODO: Generalize `r` over `R₁` and `R₂`
-- TODO: Allow for relation over events as well
inductive RelOverObs (s : S₁ → S₂ → Prop) (r : R → R → Prop) :
    Obs E R S₁ → Obs E R S₂ → Prop where
  | ret (v₁ v₂ : R) : r v₁ v₂ → RelOverObs s r (.ret v₁) (.ret v₂)
  | tau (it₁ : S₁) (it₂ : S₂) : s it₁ it₂ → RelOverObs s r (.tau it₁) (.tau it₂)
  | vis (ev : E.In) (k₁ : E.Out ev → S₁) (k₂ : E.Out ev → S₂) :
    (∀ x, s (k₁ x) (k₂ x)) → RelOverObs s r (.vis ev k₁) (.vis ev k₂)

theorem RelOverObs.mono {s s' : S₁ → S₂ → Prop} {r r' : R → R → Prop} :
    (∀ {i i'}, s i i' → s' i i') →
    (∀ {v v'}, r v v' → r' v v') →
     ∀ {o} {o' : Obs E R S₂}, (RelOverObs s r) o o' → (RelOverObs s' r') o o' :=
  fun ss' rr' _ _ => fun
    | .ret v₁ v₂ h => .ret v₁ v₂ (rr' h)
    | .tau it₁ it₂ h => .tau _ _ (ss' h)
    | .vis ev k₁ k₂ h => .vis ev k₁ k₂ (ss' <| h ·)

theorem RelOverObs.flip._mp {s : S → S → Prop} {r : R → R → Prop} {o o' : Obs E R S} :
    RelOverObs s r o o' → flip (RelOverObs (flip s) (flip r)) o o'
  | .ret v₁ v₂ h => .ret v₂ v₁ h
  | .tau it₁ it₂ h => .tau it₂ it₁ h
  | .vis ev k₁ k₂ h => .vis ev k₂ k₁ h

theorem RelOverObs.flip._mpr {s : S → S → Prop} {r : R → R → Prop} {o o' : Obs E R S} :
    flip (RelOverObs (flip s) (flip r)) o o' → RelOverObs s r o o'
  | .ret v₁ v₂ h => .ret v₂ v₁ h
  | .tau it₁ it₂ h => .tau it₂ it₁ h
  | .vis ev k₁ k₂ h => .vis ev k₂ k₁ h

theorem RelOverObs.flip {s : S → S → Prop} {r : R → R → Prop} {o o' : Obs E R S} :
    flip (RelOverObs (flip s) (flip r)) o o' = RelOverObs s r o o' :=
  propext ⟨flip._mp, flip._mpr⟩

@[refl]
theorem RelOverObs.refl (s : S → S → Prop) (r : R → R → Prop) [Std.Refl s] [Std.Refl r] :
    ∀ (o : Obs E R S), (RelOverObs s r) o o
  | .ret v => .ret v v (Std.Refl.refl v)
  | .tau it => .tau it it (Std.Refl.refl it)
  | .vis ev k => .vis ev k k (Std.Refl.refl <| k ·)

instance [Std.Refl s][Std.Refl r] : Std.Refl (RelOverObs (E := E) (R := R) s r) where refl := .refl s r

@[symm]
theorem RelOverObs.symm (s : S → S → Prop) (r : R → R → Prop) [Std.Symm s] [Std.Symm r] {o o' : Obs E R S} :
    (RelOverObs s r) o o' → (RelOverObs s r) o' o
  | .ret v₁ v₂ h => .ret v₂ v₁ (Std.Symm.symm v₁ v₂ h)
  | .tau it₁ it₂ h => .tau it₂ it₁ (Std.Symm.symm it₁ it₂ h)
  | .vis ev k₁ k₂ h => .vis ev k₂ k₁ (Std.Symm.symm _ _ <| h ·)

instance [Std.Symm s][Std.Symm r] : Std.Symm (RelOverObs (E := E) (R := R) s r) where symm _ _ := .symm s r

theorem RelOverObs.trans
  {s₁₂ : S₁ → S₂ → Prop} {s₂₃ : S₂ → S₃ → Prop} {s₁₃ : S₁ → S₃ → Prop}
  {r : R → R → Prop}
  [Trans s₁₂ s₂₃ s₁₃] [Trans r r r] {o₁ o₂ o₃} :
    (RelOverObs (E := E) s₁₂ r) o₁ o₂ →
    (RelOverObs (E := E) s₂₃ r) o₂ o₃ →
    (RelOverObs (E := E) s₁₃ r) o₁ o₃
  | .ret v₁ v₂ h₁, .ret _ v₃ h₂ => .ret v₁ v₃ (Trans.trans h₁ h₂)
  | .tau it₁ it₂ h₁, .tau _ it₃ h₂ => .tau it₁ it₃ (Trans.trans h₁ h₂)
  | .vis ev k₁ k₂ h₁, .vis _ _ k₃ h₂  => .vis ev k₁ k₃ (λx↦ Trans.trans (h₁ x) (h₂ x))

instance [Trans r r r][Trans s₁₂ s₂₃ s₁₃] :
    Trans (RelOverObs (E := E) (R := R) s₁₂ r)
          (RelOverObs (E := E) (R := R) s₂₃ r)
          (RelOverObs (E := E) (R := R) s₁₃ r) where
  trans x y := .trans x y

-- Eqit (r : R → R → Prop) (l r : Bool) [i.e. eutt :0 Eqit (· = ·) true true]
abbrev StrongBisim (r : R → R → Prop) (it₁ it₂ : iTree E R)  : Prop :=
  RelOverObs (StrongBisim r) r it₁.unfold it₂.unfold
coinductive_fixpoint monotonicity
  fun _ _ Rimp _ _ H => RelOverObs.mono (Rimp _ _) id  H

namespace StrongBisim

def cases {it₁ it₂ : iTree E R} (h : StrongBisim r it₁ it₂) :
      ∃ obs₁ obs₂, it₁.unfold = obs₁ ∧ it₂.unfold = obs₂ ∧ RelOverObs (StrongBisim r) r obs₁ obs₂ :=
  ⟨_, _, rfl, rfl, StrongBisim.eq_def .. ▸ h⟩

@[refl]
theorem refl {it : iTree E R} [Std.Refl r]: StrongBisim r it it  := by
  apply coinduct r (pred := (· = ·)) ?progress _ _ rfl
  rintro it₁ it₂ rfl
  rfl

instance [Std.Refl r] : Std.Refl (StrongBisim (E := E) (R := R) r) where refl _ := StrongBisim.refl

/- #check Classical.indefiniteDescription -/ -- Why do I get this in the error message if I invoke `h.cases` as `StrongBisim.cases`?
-- UPDATE: No longer getting that error… Idk what was going on

@[symm]
theorem symm {it₁ it₂ : iTree E R} [Std.Symm r]: StrongBisim r it₁ it₂ → StrongBisim r it₂ it₁  := by
  intro start
  apply coinduct r (pred := λ x y ↦ StrongBisim r y x) ?_ _ _ start
  intro it₁ it₂ it₂it₁
  match it₂it₁.cases with
  | ⟨.ret v₁, .ret v₂, h₁, h₂, .ret _ _ h⟩ =>
    rw [h₁, h₂]; constructor; apply Std.Symm.symm _ _ h
  | ⟨.tau it₁, .tau it₂, h₁, h₂, .tau _ _ h⟩ =>
    rw [h₁, h₂]; constructor; exact h
  | ⟨.vis ev k₁, .vis _ k₂, h₁, h₂, .vis _ _ _ h⟩ =>
    rw [h₁, h₂]; constructor; exact h

theorem trans {it₁ it₂ it₃ : iTree E R} [Trans r r r]: StrongBisim r it₁ it₂ → StrongBisim r it₂ it₃ → StrongBisim r it₁ it₃ := by
  intro H₁ H₂
  apply coinduct r (pred := λ x z ↦ ∃ y, StrongBisim r x y ∧StrongBisim r y z) ?_ _ _ ⟨it₂, H₁, H₂⟩
  intro it₁ it₃ ⟨it₂, it₁it₂, it₂it₃⟩
  unfold StrongBisim at it₁it₂ it₂it₃
  generalize h₁ : it₁.unfold = obs₁ at *
  generalize h₂ : it₂.unfold = obs₂ at *
  generalize h₃ : it₃.unfold = obs₃ at *
  match it₁it₂, it₂it₃ with
  | .ret v₁ v₂ H₁, .ret _ v₃ H₂ =>
    constructor; exact Trans.trans H₁ H₂
  | .tau it₁ it₂ H₁, .tau _ it₃ H₂ =>
    constructor; exact ⟨it₂, H₁, H₂⟩
  | .vis ev k₁ k₂ H₁, .vis _ _ k₃ H₂ =>
    constructor; intro x; exact ⟨k₂ x, H₁ x, H₂ x⟩

instance [Trans r r r] : Trans (StrongBisim (E := E) (R := R) r) (StrongBisim (E := E) (R := R) r) (StrongBisim (E := E) (R := R) r) where trans := StrongBisim.trans

end StrongBisim

abbrev ObsEq : iTree E R → iTree E R → Prop := StrongBisim (· = ·)

instance : HasEquiv (iTree E R) where
  Equiv := ObsEq

def ObsEq.refl {it : iTree E R} : it ≈ it := StrongBisim.refl
def ObsEq.symm {it₁ it₂ : iTree E R} : it₁ ≈ it₂ → it₂ ≈ it₁ := StrongBisim.symm
def ObsEq.trans {it₁ it₂ it₃ : iTree E R} : it₁ ≈ it₂ → it₂ ≈ it₃  → it₁ ≈ it₃ := StrongBisim.trans
def ObsEq.cases {it₁ it₂ : iTree E R} (h : it₁ ≈ it₂) :
      ∃ obs₁ obs₂, it₁.unfold = obs₁ ∧ it₂.unfold = obs₂ ∧ RelOverObs (· ≈ ·) (· = ·) obs₁ obs₂ :=
  StrongBisim.cases h

instance : HasEquiv (Obs E R (iTree E R)) where
  Equiv := RelOverObs (· ≈ ·) (· = ·)

def ObsEq.coinduct
  {it₁ it₂ : iTree E R}
  (pred : iTree E R → iTree E R → Prop)
  (baseCase : pred it₁ it₂)
  (progress : ∀ (it₁ it₂ : iTree E R), pred it₁ it₂ → RelOverObs pred (· = ·) it₁.unfold it₂.unfold) :
    it₁ ≈ it₂ :=
  StrongBisim.coinduct (· = ·) pred progress _ _ baseCase

theorem obsEq_unfold {it it' : iTree E R} :
    it ≈ it' ↔ it.unfold ≈ it'.unfold :=
  ⟨(StrongBisim.eq_def .. |>.mp ·), (StrongBisim.eq_def .. |>.mpr ·)⟩

private def ObsEq.step_tau_obsEq_self (State : Type _)(curr : State)(step : State → Obs E R State) :
    {curr, step : iTree E R} ≈ { {curr, step : iTree E R}.tau with curr := .inr curr } := by
  apply ObsEq.coinduct (fun
    (iTree.mk (State := State₁) curr₁ step₁)
    (iTree.mk (State := State₂) curr₂ step₂) =>
    ∃ (mpr : (PUnit ⊕ State₁) → State₂),
    curr₂ = mpr (Sum.inr curr₁) ∧
    ∀ (s : State₁),
    step₂ (mpr (.inr s)) = (step₁ s).mapState (mpr <| .inr ·)
  )
  case baseCase =>
    simp
    exists id
    simp [Obs.mapState, iTree.tau]
  case progress =>
    intro it₁ it₂ ⟨H, HC, Hs⟩
    cases h : it₁.step it₁.curr <;> simp only [h, iTree.unfold, HC, Obs.mapState, Hs, iTree.currStep]
    case ret v =>
      constructor; rfl
    case tau it =>
      constructor
      exists H
    case vis ev k =>
      constructor
      intros
      exists H

theorem ObsEq.tau_congr {it₁ it₂ : iTree E R} : it₁ ≈ it₂ → (iTree.tau it₁) ≈ (iTree.tau it₂) := by
  intro h
  unfold StrongBisim
  simp [iTree.unfold, iTree.tau]
  constructor
  change ({ it₁.tau with curr := .inr it₁.curr } ≈ { it₂.tau with curr := .inr it₂.curr })
  calc { it₁.tau with curr := .inr it₁.curr }
    _ ≈ (it₁ : iTree E R) := (step_tau_obsEq_self ..).symm
    _ ≈ it₂ := h
    _ ≈ { it₂.tau with curr := .inr it₂.curr } := (step_tau_obsEq_self ..)

def ObsEq.step_vis_obsEq_self
     (ev : E.In) (k : E.Out ev → iTree E R) (a : E.Out ev) (curr : (k a).State) :
    { curr, step := (k a).step : iTree E R} ≈
    { (iTree.vis ev k) with curr := .inr ⟨a, curr⟩ } := by
  apply ObsEq.coinduct (fun
    (iTree.mk (State := State₁) curr₁ step₁)
    (iTree.mk (State := State₂) curr₂ step₂) =>
    ∃ (mpr : (PUnit ⊕ (_ : E.Out ev) × State₁) → State₂),
    curr₂ = mpr (Sum.inr ⟨a, curr₁⟩) ∧
    ∀ (s : State₁),
    step₂ (mpr (.inr ⟨a, s⟩)) = (step₁ s).mapState (mpr <| .inr ⟨a, ·⟩)
  )
  case baseCase =>
    exists fun
      | .inl () => .inl .unit
      | .inr ⟨_, curr⟩ => .inr ⟨a, curr⟩
    simp [iTree.vis]
  case progress =>
    rintro it₁ it₂ ⟨H, HC, Hs⟩
    cases h : it₁.step it₁.curr <;> simp only [h, iTree.unfold, HC, Hs, Obs.mapState, iTree.currStep]
    case ret v =>
      constructor; rfl
    case tau it =>
      constructor
      exists H
    case vis ev k =>
      constructor
      intros
      exists H

def ObsEq.vis_congr (ev : E.In) (k₁ k₂ : E.Out ev → iTree.{_,_,max e s} E R) :
    (∀ a, k₁ a ≈ k₂ a) → iTree.vis ev k₁ ≈ iTree.vis ev k₂ := by
  intro Hk
  unfold StrongBisim
  simp [iTree.vis, iTree.unfold]
  constructor
  intro a
  change ({ iTree.vis ev k₁ with curr := .inr ⟨a, (k₁ a).curr⟩ } ≈
          { iTree.vis ev k₂ with curr := .inr ⟨a, (k₂ a).curr⟩ })
  calc { iTree.vis ev k₁ with curr := .inr ⟨a, (k₁ a).curr⟩ }
    _ ≈ k₁ a := (step_vis_obsEq_self ..).symm
    _ ≈ k₂ a := Hk a
    _ ≈ { iTree.vis ev k₂ with curr := .inr ⟨a, (k₂ a).curr⟩ } := (step_vis_obsEq_self ..)

theorem ObsEq.obsEq_ret_of_unfold_ret {it : iTree E R} {v : R} : it.unfold = .ret v → it ≈ .ret v := by
  simp [iTree.unfold]
  cases h : it.step it.curr <;> simp [iTree.currStep, h]
  rintro rfl
  unfold StrongBisim
  simp only [h, iTree.unfold, iTree.ret]
  constructor; rfl

theorem ObsEq.obsEq_tau_of_unfold_tau {it it': iTree E R} : it.unfold = .tau it' → it ≈ .tau it' := by
  simp [iTree.unfold]
  cases h : it.step it.curr <;> simp [iTree.currStep, h]
  case tau st =>
    rintro rfl
    simp [iTree.tau] at *
    apply coinduct (fun
      (iTree.mk (State := State₁) curr₁ step₁)
      (iTree.mk (State := State₂) curr₂ step₂) =>
      ∃ (mpr : (PUnit ⊕ State₁) → State₂),
      step₂ curr₂ = (step₁ curr₁).mapState (mpr <| .inr ·) ∧
      ∀ (s : State₁),
      step₂ (mpr (.inr s)) = (step₁ s).mapState (mpr <| .inr ·)
    )
    case baseCase =>
      simp
      exists id
      simp only [id_eq, implies_true, and_true, h]
    case progress =>
      rintro it₁ it₂ ⟨H, Hc, Hs⟩
      cases h : it₁.step it₁.curr <;> simp only [h, iTree.unfold, Hc, Obs.mapState]
      case ret v =>
        constructor; rfl
      case tau it =>
        constructor
        exists H
        simp [Hs]
      case vis ev k =>
        constructor
        intros
        exists H
        simp [Hs]

theorem ObsEq.obsEq_vis_of_unfold_vis {it : iTree E R}{ev : E.In} {k}: it.unfold = .vis ev k → it ≈ .vis ev k := by
  simp only [iTree.unfold]
  cases h : it.step it.curr <;> simp [reduceCtorEq, false_implies, iTree.currStep, h]
  case vis ev kS =>
    rintro rfl rfl
    unfold StrongBisim
    simp only [iTree.unfold, h, iTree.vis]
    apply RelOverObs.vis _ _ _ ?_
    intro a
    apply coinduct (fun
      (iTree.mk (State := State₁) curr₁ step₁)
      (iTree.mk (State := State₂) curr₂ step₂) =>
      ∃ (mpr : PUnit ⊕ (_ : E.Out ev) × State₁ → State₂),
      curr₂ = mpr (Sum.inr ⟨a, curr₁⟩) ∧
      ∀ (s : State₁),
      step₂ (mpr (.inr ⟨a, s⟩)) = (step₁ s).mapState (mpr <| .inr ⟨a, ·⟩)
    )
    case baseCase =>
      exists id
      simp [Obs.mapState]
    case progress =>
      rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨H, HC, Hs⟩
      cases h : s₁ c₁ <;> simp only [h, iTree.unfold, HC, Hs, Obs.mapState, iTree.currStep]
      case ret v =>
        constructor; rfl
      case tau it =>
        constructor
        exists H
      case vis ev k =>
        constructor
        intros
        exists H

def iTree.obsEqElim {motive : iTree.{_,_,_} E R → Sort _}
  (inv : ∀ {it it'}, it ≈ it' → motive it' → motive it)
  -- NOTE: We would need to derive the proof of this ↑ automatically
  (ret : ∀ (v : R), motive (.ret v))
  (vis : ∀ (ev : E.In) (k : E.Out ev → iTree E R), motive (.vis ev k))
  (tau : ∀ (it : iTree E R), motive (.tau it)) :
    ∀ it, motive it := fun it => by
  match h : it.unfold with
  | .ret v =>
    exact inv (ObsEq.obsEq_ret_of_unfold_ret h) (ret ..)
  | .tau it' =>
    exact inv (ObsEq.obsEq_tau_of_unfold_tau h) (tau ..)
  | .vis ev k =>
    exact inv (ObsEq.obsEq_vis_of_unfold_vis h) (vis ..)

instance instEquiv  : Equivalence (fun (x y : iTree E R) => x ≈ y) where
  refl _ := StrongBisim.refl
  symm   := StrongBisim.symm
  trans  := StrongBisim.trans

instance instSetoid : Setoid (iTree E R) where
  r := ObsEq
  iseqv := instEquiv

def iTree' (E : Effect.{e}) (R : Type r) : Type _ := Quotient (instSetoid (E := E) (R := R))

namespace iTree'

def mk (it : iTree E R) : iTree' E R := Quotient.mk instSetoid it

def unfold (it' : iTree' E R) : Obs E R (iTree' E R) :=
  it'.lift (fun it =>
    it.unfold.mapState iTree'.mk
  ) (by
    intros it₁ it₂ it₁it₂
    match StrongBisim.cases <| it₁it₂ with
    | ⟨.ret v₁, .ret v₂, h₁, h₂, .ret _ _ h⟩ =>
      simp only [Obs.mapState, h₁, h₂, h]
    | ⟨.tau it₁, .tau it₂, h₁, h₂, .tau _ _ h⟩ =>
      simp only [Obs.mapState, Obs.tau.injEq, h₁, h₂]
      apply Quotient.sound h
    | ⟨.vis ev k₁, .vis _ k₂, h₁, h₂, .vis _ _ _ hK⟩ =>
      simp [*]
      ext a
      apply Quotient.sound (hK a)
  )

def ret (v : R) := iTree'.mk (.ret v : iTree E R)

theorem unfold_eq_ret (v : R) (it' : iTree' E R) :
    it'.unfold = .ret v → it' = iTree'.ret v := by
  apply it'.ind; intro it
  intros h
  simp [ret]
  apply Quotient.sound
  apply ObsEq.obsEq_ret_of_unfold_ret
  simp [unfold, Quotient.lift, Quotient.mk, Obs.mapState] at h
  cases h₂ : it.unfold <;> simp [h₂] at h
  simpa

def tau (it : iTree' E R) :=
    it.lift (Quotient.mk inferInstance <| iTree.tau ·) (by
      intros it it' heq; simp; apply Quotient.sound
      apply ObsEq.tau_congr heq
    )

theorem unfold_eq_tau (it' it'₂ : iTree' E R) :
    it'.unfold = .tau it'₂ →
    it' = iTree'.tau it'₂ := by
  apply it'.ind; intros it
  apply it'₂.ind; intro it₂
  intros h
  simp only [tau, Quotient.lift, Quotient.mk]
  apply Quotient.sound
  simp [unfold, Quotient.lift, Quotient.mk, Obs.mapState] at h
  cases h₂ : it.unfold <;> simp [h₂] at h
  case a.tau it₂ =>
    have h := Quotient.exact h
    refine .trans ?_ (ObsEq.tau_congr h)
    apply ObsEq.obsEq_tau_of_unfold_tau h₂

-- picks an element out of the quotient, but bumps up the universes
def out (it' : iTree' E R) : iTree E R where
    curr := it'
    step := iTree'.unfold

set_option pp.universes true in
def vis (ev : E.In) (k' : E.Out ev → iTree' E R) : iTree' E R :=
  iTree'.mk (iTree.vis ev (out ∘ k'))

/-
  I wonder if exploiting `Quotient.choice` to basically find a fixpoint is
  too powerful of an operation, and therefore likely to lead to problems in
  the future.
-/

theorem ret_eq_mk_ret (v : R) :
    iTree'.ret (E := E) v = iTree'.mk (iTree.ret v) := by
  apply Quotient.sound
  apply StrongBisim.refl

theorem tau_mk_eq_mk_tau (it : iTree E R) :
    iTree'.tau (.mk it) = iTree'.mk (iTree.tau it) := by
  apply Quotient.sound
  apply StrongBisim.refl

end iTree'

end StrongBisimulation

/-

Defining weak bisimulation is done similarly to how strong bisimulation
worked in our previous usecase. The only difference is in how we define
`RelOverObs`, which now skips over `tau` nodes.

One needs to be careful in how these tau nodes are skipped though. If
both `iTree`s being observed have `tau` nodes, then it's always safe to
skip then both. However, one must take care of only ever skipping a
finite number of `tau` nodes from the left or right iTrees before
processing a node of the other right or left iTree respectively.
Otherwise, one would be able to equate `iTree.loop` with `iTree.ret v`
by inifinitely skipping the `tau` nodes of `iTree.loop`.

-/

section WeakBisimulation

/-
  There's various ways in which to express the fact that in a weak
  bisimulation we allow skipping over a finite amount of tau nodes.

  One option is to define the relation inductively as we have done
  before.

  Another option is to, instead, define an order between `iTree`s
  which expresses that one is a "preffix" of the other. Then, we
  can express that a weak bisimulation can skip over a finite
  number of taus by relating, not the trees themselves, but trees
  which are themselves
-/

local instance : Std.Refl (Eq (α := α)) where refl := .refl
local instance : Std.Symm (Eq (α := α)) where symm _ _:= .symm

inductive τ (K : iTree E R → iTree E R → Prop) : iTree E R → iTree E R → Prop where
  | sync it₁ it₂ : K it₁ it₂ → τ K it₁ it₂
  | drop_left (it₁ it₂ it₁' : iTree E R) :
    it₁.unfold = .tau it₁' →
    τ K it₁' it₂ →
    τ K it₁ it₂
  | drop_right (it₁ it₂ it₂' : iTree E R) :
    it₂.unfold = .tau it₂' →
    τ K it₁ it₂' →
    τ K it₁ it₂

def τ.mono {K K' : iTree E R → iTree E R → Prop}
  (KK' : ∀{it it'}, K it it' → K' it it') {it it' : iTree E R} :
    τ K it it' → τ K' it it'
  | sync _ _ K₁₂ => sync _ _ (KK' K₁₂)
  | drop_left _ _ _ Htau₁ UTK₁'₂ => drop_left _ _ _ Htau₁ (UTK₁'₂.mono KK')
  | drop_right _ _ _ Htau₂ UTK₁₂' => drop_right _ _ _ Htau₂ (UTK₁₂'.mono KK')

def WeakBisim (it₁ it₂ : iTree E R ) : Prop :=
  -- ∃ it₁' it₂', it₁.IsDelayed it₁' ∧ it₂.IsDelayed it₂' ∧ RelOverObs WeakBisim Eq it₁'.unfold it₂'.unfold
  τ (RelOverObs WeakBisim Eq ·.unfold ·.unfold) it₁ it₂
coinductive_fixpoint monotonicity by
  intro WB WB' WBimp it₁ it₂ WB₁₂
  -- have : ⟨it₁', it₂', it₁it₁', it₂it₂', WB₁₂⟩ := WB₁₂
  -- refine ⟨it₁', it₂', it₁it₁', it₂it₂', (RelOverObs.mono (WBimp _ _) id) WB₁₂⟩
  exact WB₁₂.mono (RelOverObs.mono (WBimp _ _) id)

notation a " ∼ʷᵇ∼ " b => WeakBisim a b
notation a " ≣WB≣ " b => RelOverObs WeakBisim Eq a b

namespace WeakBisim

def fold : τ (RelOverObs WeakBisim Eq ·.unfold ·.unfold) it₁ it₂ → WeakBisim it₁ it₂ :=
  (WeakBisim.eq_1 .. ▸ ·)

def unfold : WeakBisim it₁ it₂ → τ (RelOverObs WeakBisim Eq ·.unfold ·.unfold) it₁ it₂ :=
  (WeakBisim.eq_1 .. ▸ ·)

@[match_pattern]
def sync{it₁ it₂ : iTree E R} (H : RelOverObs WeakBisim Eq it₁.unfold it₂.unfold) : WeakBisim it₁ it₂ :=
  .fold <| .sync _ _ H

@[match_pattern]
def drop_left{it₁ it₂ it₁': iTree E R} (Htau₁ : it₁.unfold = .tau it₁')(H : WeakBisim it₁' it₂) : WeakBisim it₁ it₂ :=
  .fold <| .drop_left _ _ _ Htau₁ H.unfold

@[match_pattern]
def drop_right{it₁ it₂ it₂' : iTree E R} (Htau₂ : it₂.unfold = .tau it₂')(H : WeakBisim it₁ it₂') : WeakBisim it₁ it₂ :=
  .fold <| .drop_right _ _ _ Htau₂ H.unfold

@[induction_eliminator]
def WeakBisim.rec {it₁ it₂ : iTree E R} (h : WeakBisim it₁ it₂)
  {motive : ∀ it₁ it₂, WeakBisim it₁ it₂ → Prop}
  (sync : ∀ it₁ it₂, (h : RelOverObs WeakBisim Eq it₁.unfold it₂.unfold) → motive it₁ it₂ (.sync h))
  (drop_left : ∀ it₁ it₂ it₁' Htau₁ H, motive it₁' it₂ H → motive it₁ it₂ (.drop_left Htau₁ H))
  (drop_right : ∀ it₁ it₂ it₂' Htau₂ H, motive it₁ it₂' H → motive it₁ it₂ (.drop_right Htau₂ H)) :
    motive it₁ it₂ h := by
  unfold WeakBisim at *
  induction h with
  | sync it₁ it₂ H =>
    apply sync _ _ H
  | drop_left it₁ it₂ it₁' Htau₁ H IH =>
    apply drop_left _ _ _ Htau₁ H (IH _)
  | drop_right it₁ it₂ it₂' Htau₂ H IH =>
    apply drop_right _ _ _ Htau₂ H (IH _)

@[refl]
def refl (it : iTree E R) : WeakBisim it it := by
  apply WeakBisim.coinduct (pred := (· = ·)) _ _ _ rfl
  intro it _ rfl
  apply τ.sync
  apply Std.Refl.refl _

@[symm]
def symm (it₁ it₂ : iTree E R) : WeakBisim it₁ it₂ → WeakBisim it₂ it₁ := by
  intro H
  apply WeakBisim.coinduct (pred := flip WeakBisim) _ _ _ H
  clear H it₁ it₂
  intro it₁ it₂ H
  unfold flip at H ⊢
  induction H with
  | sync it₁ it₂ H =>
    apply τ.sync
    generalize h₁ : it₁.unfold = obs₁ at *
    generalize h₂ : it₂.unfold = obs₂ at *
    cases H <;> open RelOverObs in
      grind [ret, tau, vis]
  | drop_left it₁ it₂ it₁' Htau₁ UTT₁'₂ IH =>
    exact τ.drop_right _ _ _ Htau₁ IH
  | drop_right it₁ it₂ it₂' Htau₂ UTT₁₂' IH =>
    exact τ.drop_left _ _ _ Htau₂ IH

/-

 a  ∼ʷᵇ∼  b  ∼ʷᵇ∼  c
 ↓       ↓ ↓       ↓
 ↓       ↓ ↓       ↓
 ↓       ↓ ↓       ↓
 a' ≣WB≣ b₁↓       ↓
           ↓       ↓
           ↓       ↓
          b₂ ≣WB≣ c'
-/

-- NOTE: Can't really prove this separately, since we need regular transitivity for the `tau` case.
-- def pushLeft {b c a : iTree E R} : RelOverObs WeakBisim Eq a.unfold b.unfold → WeakBisim b c → WeakBisim a c := by

def extendLeft {b b' c : iTree E R}: b.unfold = .tau b' → (b ∼ʷᵇ∼ c) → b' ∼ʷᵇ∼ c := by
  intro b_unfold b_WB_c
  induction b_WB_c with
  | sync b c b_RO_c =>
    simp [b_unfold] at b_RO_c
    generalize c_unfold : c.unfold = obs at *
    rcases b_RO_c with (_ | ⟨_, c', b'_WB_c'⟩| _)
    apply drop_right c_unfold
    assumption
  | drop_left b c b'' b_unfold =>
    obtain rfl : b' = b'' := by grind
    assumption
  | drop_right b c c' c_unfold _ IH =>
    apply drop_right c_unfold
    apply IH b_unfold

def trans (a b c : iTree E R) : WeakBisim a b → WeakBisim b c → WeakBisim a c := by
  intro a_WB_b b_WB_c
  let pred := (∃ b : iTree E R, WeakBisim · b ∧ WeakBisim b ·)
  apply WeakBisim.coinduct (pred := pred) _ _ _ ⟨_, a_WB_b, b_WB_c⟩; clear a b c a_WB_b b_WB_c; intro a c ⟨b, a_WB_b, b_WB_c⟩
  induction a_WB_b generalizing c with
  | sync a b a_RO_b =>
    rename_i old_a old_b; clear old_a old_b
    induction b_WB_c generalizing a with
    | sync b c b_RO_c =>
      rename_i old_b old_c; clear old_c old_b
      generalize a_unfold : a.unfold = obs₁ at *
      generalize b_unfold : b.unfold = obs₂ at *
      generalize c_unfold : c.unfold = obs₃ at *
      apply τ.sync
      cases a_RO_b <;> cases b_RO_c <;> open RelOverObs in
        grind [tau, ret, vis]
    | drop_left b c b' b_unfold b'_WB_c IH =>
      rename_i old_b old_c; clear old_c old_b
      -- Because of `b_unfold` we have that `a_RO_b` is over `tau`
      generalize a_unfold : a.unfold = obs₁ at a_RO_b
      simp only [b_unfold] at a_RO_b
      cases a_RO_b with
      | tau a' _ a'_WB_b' =>
        /-
          a  ≣WB≣  b  ∼ʷᵇ∼  c
          ↓        ↓
          a' ∼ʷᵇ∼  b'
        -/
        --
        -- We proceed by induction on `a'  ∼WB∼  b'` and
        -- try to find the syncrhonization point with c
        -- TODO: Why do we require that `x ≣WB≣ b'`? This is not necessarily
        -- what we want
        apply τ.drop_left _ _ _ a_unfold
        induction a'_WB_b' generalizing b a with
        | sync a' b' a'_RO_b' =>
          rename_i old_a' old_b'; clear old_a' old_b'
          apply IH _ a'_RO_b'
        | drop_left a' b' a'' a'_unfold a''_WB_b' IH₂ =>
          rename_i old_a' old_b'; clear old_a' old_b'
          apply τ.drop_left _ _ _ a'_unfold
          apply IH₂ _ b_unfold b'_WB_c IH _ a'_unfold
        | drop_right a' b' b'' b'_unfold a'_WB_b'' IH₂ =>
          rename_i old_a' old_b'; clear old_a' old_b'
          -- obtain rfl : b' = b'' := by grind
          -- clear a a_unfold b b_unfold
          /-
            a  ≣WB≣  b  ∼ʷᵇ∼  c
            ↓        ↓
            a' ∼ʷᵇ∼  b'
                     ↓
                     b''
          -/
          generalize a'_unfold : a'.unfold = obs at *
          match obs with
          | .tau a'' =>
            -- We can show `a' ≣WB≣ b'`
            apply IH; clear IH
            simp [b'_unfold, a'_unfold]
            constructor
            apply extendLeft a'_unfold
            assumption
          | .ret va =>
            -- We conclude
            -- have := pushLeft_unfold_ret a'_unfold
            clear b b_unfold a a_unfold
            have b''_WB_c := (extendLeft b'_unfold b'_WB_c)
            clear b'_WB_c
            clear IH IH₂
            induction a'_WB_b'' generalizing b' with
            | sync a' b'' a'_RO_b'' =>
              simp only [a'_unfold] at a'_RO_b''
              generalize b''_unfold : b''.unfold = obs at *
              rcases a'_RO_b'' with ⟨_, _, rfl⟩ | _ | _
              induction b''_WB_c with
              | sync b'' c b''_RO_c =>
                simp only [b''_unfold] at *
                generalize c_unfold : c.unfold = obs at *
                rcases b''_RO_c with ⟨_, _, rfl⟩ | _ | _
                apply τ.sync
                simp [*]
                constructor; grind
              | drop_left => grind
              | drop_right b'' c c' c_unfold _ IH =>
                apply τ.drop_right _ _ _ c_unfold
                apply IH <;> assumption
            | drop_left => grind
            | drop_right a' b'' b''' b''_unfold a'_WB_b''' IH =>
              specialize IH _ b''_unfold  a'_unfold (extendLeft b''_unfold b''_WB_c)
              apply IH
          | .vis e k =>
            -- We conclude
            clear b b_unfold a a_unfold
            have b''_WB_c := (extendLeft b'_unfold b'_WB_c)
            clear b'_WB_c
            clear IH IH₂
            induction a'_WB_b'' generalizing b' with
            | sync a' b'' a'_RO_b'' =>
              simp only [a'_unfold] at a'_RO_b''
              generalize b''_unfold : b''.unfold = obs at *
              rcases a'_RO_b'' with ⟨_, _, rfl⟩ | _ | _
              induction b''_WB_c with
              | sync b'' c b''_RO_c =>
                simp only [b''_unfold] at *
                generalize c_unfold : c.unfold = obs at *
                rcases b''_RO_c with ⟨_, _, rfl⟩ | _ | _
                apply τ.sync
                simp [*]
                constructor; grind
              | drop_left => grind
              | drop_right b'' c c' c_unfold _ IH =>
                apply τ.drop_right _ _ _ c_unfold
                apply IH <;> assumption
            | drop_left => grind
            | drop_right a' b'' b''' b''_unfold a'_WB_b''' IH =>
              specialize IH _ b''_unfold  a'_unfold (extendLeft b''_unfold b''_WB_c)
              apply IH
    | drop_right b c c' Htau₃ H₂₃' IH =>
      rename_i old_b old_c; clear old_c old_b
      apply τ.drop_right _ _ _ Htau₃
      apply IH _ a_RO_b
  | drop_left a b a' a_unfold H₁'₂ IH =>
    rename_i old_a old_b; clear old_a old_b
    apply τ.drop_left _ _ _ a_unfold
    apply IH _ b_WB_c
  | drop_right a b b' b_unfold H₁₂' IH =>
    rename_i old_a old_b; clear old_a old_b
    induction b_WB_c with
    | sync b c b_RO_c =>
      rename_i old_b old_c; clear old_b old_c
      generalize c_unfold : c.unfold = obs at b_RO_c
      simp only [b_unfold] at b_RO_c
      cases b_RO_c with
      | tau _ c' b'_WB_c' =>
        apply τ.drop_right _ _ _ c_unfold
        apply IH _ b'_WB_c'
    | drop_left b c b'' b_unfold₂ b'_WB_c IH₂ =>
      rename_i old_b old_c; clear old_b old_c
      clear IH₂
      obtain rfl : b' = b'' := by grind
      apply IH
      assumption
    | drop_right b c c' c_unfold b_WB_c' IH₂ =>
      rename_i old_b old_c; clear old_b old_c
      apply τ.drop_right _ _ _ c_unfold
      apply IH₂ b_unfold


end WeakBisim

instance : Equivalence (WeakBisim (E := E) (R := R)) where
  refl := .refl
  symm := .symm _ _
  trans := .trans _ _ _

end WeakBisimulation

end EqualitiesOverITrees

end StateMachine
