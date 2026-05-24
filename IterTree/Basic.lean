import IterTree.QuotientTrick
import Lean

namespace IterTree

/-

# What is an iTree?

An iTree represents a computation. A computation can be represented by an infinitely
branching tree, which give rise to the different possible traces.

The type of an iTree is parametrized by two types:
 - R, the type of values returned by the computation
 - E, the possible events raised by the computation before it concludes. Data may be
   requested by the computation before it can resume, and the event is allowed to
   depend on the type of this data.

We would write this as

    coinductive iTree (E : Type → Type) (R : Type) where
    | ret : R → iTree E R
    | tau : iTree E R → iTree E R
    | vis : ∀ A, E A → (A → iTree E R) → iTree E R

However, in Lean we don't have coinductive data!

We could talk about a finite version of iTrees though, if we just make the definition
inductive.

-/

namespace Finite

inductive iTree (E : Type q → Type r) (R : Type v) : Type _ where
| ret : R → iTree E R
| tau : iTree E R → iTree E R
| vis {A : Type q} : E A → (A → iTree E R) → iTree E R

/-

Then, we can define a bunch of interesting operations over trees!

-/

namespace iTree

variable {E : Type q → Type r}

def bindLeft {α β} (f : α → iTree E β) : iTree E α → iTree E β
| .ret v    => f v
| .tau it   => .tau (it.bindLeft f)
| .vis ev k => .vis ev (fun a => (k a).bindLeft f)

instance : Bind (iTree E) := ⟨(·.bindLeft ·)⟩
instance : Pure (iTree E) := ⟨.ret⟩
instance : Monad (iTree E) where
instance  : LawfulMonad (iTree E) := .mk'
   (id_map     := by intros α it; simp only [Functor.map, bind, pure, Function.comp_id]; induction it <;> simp [bindLeft, *] )
   (pure_bind  := by intros α β it f; simp only [bind, bindLeft])
   (bind_assoc := by intros α β γ it f g; simp only [bind]; induction it <;> simp [bindLeft, *])

-- Defined as an inductive proposition, since we cannot test for equality of types (for the `vis`-`vis` case)
inductive eqUpToTau : iTree E R → iTree E R → Prop where
| of_ret (r : R) : (iTree.ret r).eqUpToTau (.ret r)
| of_vis {A : Type q}(ev : E A) (k₁ k₂ : A → iTree E R) : (∀ a : A, (k₁ a).eqUpToTau (k₂ a)) → (iTree.vis ev k₁).eqUpToTau (.vis ev k₂)
| of_tau (it₁ it₂ : iTree E R) : it₁.eqUpToTau it₂ → (iTree.tau it₁).eqUpToTau (.tau it₂)
| of_left_tau (it₁ it₂ : iTree E R) : it₁.eqUpToTau it₂ → (iTree.tau it₁).eqUpToTau it₂
| of_right_tau (it₁ it₂ : iTree E R) : it₁.eqUpToTau it₂ →  it₁.eqUpToTau (.tau it₂)

/-

The issue with this definition is that it cannot be used to capture most computations
we're interested in. Without looking further, we cannot represent any computation which
is infinite, like `loop {}`!

Furthermore, the `tau` constructor in this definition is useless. It can always be
stripped! In particular, our `eqUpToTau` predicate is equivalent to `Eq` if we run
the iTrees we're comparing through our stripping function first.

-/

def stripTau : iTree E R → iTree E R
| .ret v => .ret v
| .tau it => it.stripTau
| .vis ev k => .vis ev (fun it => (k it).stripTau)

theorem eqUpToTau_of_stripTau_eq_stripTau {it₁ it₂ : iTree E R} : (it₁.stripTau = it₂.stripTau) → it₁.eqUpToTau it₂ := by
  intros hyp
  induction it₁ generalizing it₂ with
  | ret v₁ =>
    induction it₂ with
    | ret v₂ =>
      grind [eqUpToTau, stripTau]
    | tau it₂ =>
      grind [stripTau, eqUpToTau]
    | vis ev₂ k₂ =>
      simp [stripTau] at hyp
  | tau it₁ IH =>
    grind [stripTau, eqUpToTau]
  | vis ev₁ k₁ IH₁ =>
    induction it₂ with
    | ret v₂ =>
      grind [eqUpToTau, stripTau]
    | tau it₂ =>
      grind [stripTau, eqUpToTau]
    | vis ev₂ k₂ IH₂ =>
      simp [stripTau] at hyp
      obtain ⟨rfl, rfl, hyp⟩ :=  hyp
      simp only [heq_eq_eq] at hyp
      replace hyp := fun a => congrFun hyp a
      constructor
      intros a
      apply IH₁
      grind

theorem eqUpToTau_iff_stripTau_eq_stripTau {it₁ it₂ : iTree E R} : it₁.eqUpToTau it₂ ↔ (it₁.stripTau = it₂.stripTau) := by
  constructor <;> intros hyp
  · induction hyp <;> grind [stripTau]
  · apply eqUpToTau_of_stripTau_eq_stripTau hyp

end iTree

end Finite


/-

Therefore, we look to give a different presentation of iTrees, which does not have this problem, but also
allows definining the same operations as the finite case.

-/

section StateMachine

/-

The first attempt I want to try is to give an encoding in terms of a state machine. Basically, we have a
"current state" and a "step function" which tells us to what state to go next.

The issue with this representation is that a single, fixed state is not enough to express all we want out
of iTrees (Is this actually true?).

Inspired by Lean's Std.Iter APIs, we can attack a specific state with the ability to say it represents
some `iTree`. In a sense, this means that we generalize over implementations of the `iTree`, to remain
only with its interface, which is what we do theorems againsts.

-/


@[grind cases]
inductive Obs (E : Type q → Type r) (R : Type v) (K : Type k) where
| ret : R → Obs E R K
| tau : K → Obs E R K
| vis {A : Type q} : E A → (A → K) → Obs E R K

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


structure iTree (E : Type q → Type r) (R : Type v) where
  {State : Type s}
  curr : State
  step : State → Obs E R State

/-

An alternate representation of this interface would be to have `curr : State` be the implementation of
an `iTree E R`, and assign to each `State` type a particular `step` function.

-/

namespace iTree

variable {E : Type q → Type r} {R : Type v}

/-- The looping computation -/
def loop.{s} : iTree E R where
  State := PUnit.{s+1}
  curr := .unit
  step _ := .tau .unit

instance : Inhabited (iTree E R) := ⟨loop⟩

def unfold (it : iTree E R) : Obs E R (iTree E R) :=
  match it.step it.curr with
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
  curr : PUnit.{s+1} := .unit
  step _ := .ret r

def vis.{s} {α : Type q} (ev : E α) (k : α → iTree.{_,_,_,s} E R) : iTree E R where
  curr : Unit ⊕ (a : α) × (k a ).State := .inl .unit
  step
  | .inl ⟨⟩ => .vis ev (fun a => .inr <| ⟨a, (k a).curr⟩)
  | .inr ⟨a, s⟩ => (k a).step s |>.mapState (.inr ⟨a, ·⟩)

def tau.{s} (it : iTree.{_,_,_,s} E R) : iTree E R where
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
        |>.bindVal (fun a => .tau <| .inr ⟨a, (f a).curr⟩)
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

variable {E : Type quest → Type resp}{R : Type ret}

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
  | vis (A : Type _) (ev : E A) (k₁ : A → S₁) (k₂ : A → S₂) :
    (∀ x, s (k₁ x) (k₂ x)) → RelOverObs s r (.vis ev k₁) (.vis ev k₂)

/- @[simp] -/
/- abbrev relOverObs (s : iTree E R → iTree E R → Prop) (r : R → R → Prop) : Obs E R (iTree E R) → Obs E R (iTree E R) → Prop -/
/- | .ret v₁, .ret v₂ => r v₁ v₂ -/
/- | .tau it₁', .tau it₂' => s it₁' it₂' -/
/- | .vis (A := A₁) ev₁ k₁, .vis (A := A₂) ev₂ k₂ => -/
/-     ∃ (h : A₁ = A₂), ev₁ = h ▸ ev₂ ∧ ∀ s₁, -/
/-       s (k₁ s₁) (k₂ (h ▸ s₁)) -/
/- | _, _ => False -/

theorem RelOverObs.mono {s s' : S₁ → S₂ → Prop} {r r' : R → R → Prop} :
    (∀ {i i'}, s i i' → s' i i') →
    (∀ {v v'}, r v v' → r' v v') →
     ∀ {o} {o' : Obs E R S₂}, (RelOverObs s r) o o' → (RelOverObs s' r') o o' :=
  fun ss' rr' _ _ => fun
    | .ret v₁ v₂ h => .ret v₁ v₂ (rr' h)
    | .tau it₁ it₂ h => .tau _ _ (ss' h)
    | .vis A ev k₁ k₂ h => .vis A ev k₁ k₂ (ss' <| h ·)

theorem RelOverObs.flip._mp {s : S → S → Prop} {r : R → R → Prop} {o o' : Obs E R S} :
    RelOverObs s r o o' → flip (RelOverObs (flip s) (flip r)) o o'
  | .ret v₁ v₂ h => .ret v₂ v₁ h
  | .tau it₁ it₂ h => .tau it₂ it₁ h
  | .vis A ev k₁ k₂ h => .vis A ev k₂ k₁ h

theorem RelOverObs.flip._mpr {s : S → S → Prop} {r : R → R → Prop} {o o' : Obs E R S} :
    flip (RelOverObs (flip s) (flip r)) o o' → RelOverObs s r o o'
  | .ret v₁ v₂ h => .ret v₂ v₁ h
  | .tau it₁ it₂ h => .tau it₂ it₁ h
  | .vis A ev k₁ k₂ h => .vis A ev k₂ k₁ h

theorem RelOverObs.flip {s : S → S → Prop} {r : R → R → Prop} {o o' : Obs E R S} :
    flip (RelOverObs (flip s) (flip r)) o o' = RelOverObs s r o o' :=
  propext ⟨flip._mp, flip._mpr⟩

@[refl]
theorem RelOverObs.refl (s : S → S → Prop) (r : R → R → Prop) [Std.Refl s] [Std.Refl r] :
    ∀ (o : Obs E R S), (RelOverObs s r) o o
  | .ret v => .ret v v (Std.Refl.refl v)
  | .tau it => .tau it it (Std.Refl.refl it)
  | .vis ev k => .vis _ ev k k (Std.Refl.refl <| k ·)

instance [Std.Refl s][Std.Refl r] : Std.Refl (RelOverObs (E := E) (R := R) s r) where refl := .refl s r

@[symm]
theorem RelOverObs.symm (s : S → S → Prop) (r : R → R → Prop) [Std.Symm s] [Std.Symm r] {o o' : Obs E R S} :
    (RelOverObs s r) o o' → (RelOverObs s r) o' o
  | .ret v₁ v₂ h => .ret v₂ v₁ (Std.Symm.symm v₁ v₂ h)
  | .tau it₁ it₂ h => .tau it₂ it₁ (Std.Symm.symm it₁ it₂ h)
  | .vis A ev k₁ k₂ h => .vis _ ev k₂ k₁ (Std.Symm.symm _ _ <| h ·)

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
  | .vis _ ev k₁ k₂ h₁, .vis _ _ _ k₃ h₂  => .vis _ ev k₁ k₃ (λx↦ Trans.trans (h₁ x) (h₂ x))

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
  | ⟨.vis ev k₁, .vis _ k₂, h₁, h₂, .vis _ _ _ _ h⟩ =>
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
  | .vis A ev k₁ k₂ H₁, .vis _ _ _ k₃ H₂ =>
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
    cases h : it₁.step it₁.curr <;> simp only [h, iTree.unfold, HC, Obs.mapState, Hs]
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
     (ev : E A) (k : A → iTree E R) (a : A) (curr : (k a).State) :
    { curr, step := (k a).step : iTree E R} ≈
    { (iTree.vis ev k) with curr := .inr ⟨a, curr⟩ } := by
  apply ObsEq.coinduct (fun
    (iTree.mk (State := State₁) curr₁ step₁)
    (iTree.mk (State := State₂) curr₂ step₂) =>
    ∃ (mpr : (PUnit ⊕ (_ : A) × State₁) → State₂),
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
    cases h : it₁.step it₁.curr <;> simp only [h, iTree.unfold, HC, Hs, Obs.mapState]
    case ret v =>
      constructor; rfl
    case tau it =>
      constructor
      exists H
    case vis ev k =>
      constructor
      intros
      exists H

-- TODO: Must restrict the universe of inputs to the universe of states for this
-- lemma to make sense. I guess it's a fine simplification to make to assume that
-- our states are in the same universe as our inputs? At worst one can just bump
-- the universe levels.
def ObsEq.vis_congr {A : Type _} (ev : E A) (k₁ k₂ : A → iTree.{_,_,_,quest} E R) :
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
  cases h : it.step it.curr <;> simp
  rintro rfl
  unfold StrongBisim
  simp only [h, iTree.unfold, iTree.ret]
  constructor; rfl

theorem ObsEq.obsEq_tau_of_unfold_tau {it it': iTree E R} : it.unfold = .tau it' → it ≈ .tau it' := by
  simp [iTree.unfold]
  cases h : it.step it.curr <;> simp
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

theorem ObsEq.obsEq_vis_of_unfold_vis {it : iTree E R}{ev : E A} {k}: it.unfold = .vis ev k → it ≈ .vis ev k := by
  simp only [iTree.unfold]
  cases h : it.step it.curr <;> simp [reduceCtorEq, false_implies]
  case vis A ev kS =>
    rintro rfl rfl rfl
    unfold StrongBisim
    simp only [iTree.unfold, h, iTree.vis]
    apply RelOverObs.vis _ _ _ _ ?_
    intro a
    apply coinduct (fun
      (iTree.mk (State := State₁) curr₁ step₁)
      (iTree.mk (State := State₂) curr₂ step₂) =>
      ∃ (mpr : PUnit ⊕ (_ : A) × State₁ → State₂),
      curr₂ = mpr (Sum.inr ⟨a, curr₁⟩) ∧
      ∀ (s : State₁),
      step₂ (mpr (.inr ⟨a, s⟩)) = (step₁ s).mapState (mpr <| .inr ⟨a, ·⟩)
    )
    case baseCase =>
      exists id
      simp [Obs.mapState]
    case progress =>
      rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨H, HC, Hs⟩
      cases h : s₁ c₁ <;> simp only [h, iTree.unfold, HC, Hs, Obs.mapState]
      case ret v =>
        constructor; rfl
      case tau it =>
        constructor
        exists H
      case vis ev k =>
        constructor
        intros
        exists H

def iTree.obsEqElim {motive : iTree.{_,_,_,quest} E R → Sort _}
  (inv : ∀ {it it'}, it ≈ it' → motive it' → motive it)
  (ret : ∀ (v : R), motive (.ret v))
  (vis : ∀ (A : Type _) (ev : E A) (k : A → iTree E R), motive (.vis ev k))
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

def iTree'.{a,e,r} (E : Type a → Type e) (R : Type r) : Type _ := Quotient (instSetoid (E := E) (R := R))

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
    | ⟨.vis ev k₁, .vis _ k₂, h₁, h₂, .vis _ _ _ _ hK⟩ =>
      simp [*]
      ext a
      apply Quotient.sound (hK a)
  )

def ret {R : Type _} (v : R){E : Type _ → Type _} := iTree'.mk (.ret v : iTree E R)

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

def tau {R : Type _} {E : Type _ → Type _} (it : iTree' E R) :=
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

/-
  In the following section, we use an unsafe computable implementation of
  `Quotient.choice` to be able to define `Quotient.bubbleUp`. I believe
  that this implementation is safe, since the unsafe operation happens
  inside the creation of another quotient, and therefore cannot be
  exploited. This claim has not been checked.
-/
section doubious

-- def vis {A : Type a} {R : Type _}{E : Type a → Type _} (ev : E A) (k' : A → iTree' E R) : iTree' E R :=
--   (Dubious.Quotient.bubbleUp k').lift (.mk <| iTree.vis ev ·) (
--     fun k₁ k₂ k₁k₂ =>
--     Quotient.sound <| ObsEq.vis_congr _ _ _ <| fun a => by apply k₁k₂ a
--   )

end doubious

/-
  A less dubious `vis` definition can be achieved by using the `iTree'`
  itself as the state of an `iTree`. While elegant, this solution has
  the issue that it bumps the universe levels, and therefore doesn't
  seem to be usable to define a custom eliminator for `iTree'`.
-/
section LessDoubiousVisDefinition
-- picks an element out of the quotient, but bumps up the universes
def out (it' : iTree' E R) : iTree E R where
    curr := it'
    step := iTree'.unfold

set_option pp.universes true in
def vis {A : Type a} {R : Type v}{E : Type a → Type r} (ev : E A) (k' : A → iTree' E R) : iTree' E R :=
  iTree'.mk (iTree.vis ev (out ∘ k'))

end LessDoubiousVisDefinition

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

-- theorem vis_mk_eq_mk_vis (ev : E A) (k : A → iTree E R) :
--     iTree'.vis ev (.mk ∘ k) = iTree'.mk (iTree.vis ev k) := by
--   refine Quotient.sound ?_
--   apply ObsEq.vis_congr
--   intro a
--   apply Quotient.exact
--   simp [Quotient.mk, Quot.out_eq, iTree'.mk]

-- -- Custom eliminator for `iTree'` in `Prop`
-- @[cases_eliminator]
-- def ind {R : Type r}{E : Type a → Type e} {motive : iTree' E R → Prop}
--   (ret : (v : R) → motive (.ret v))
--   (vis : ∀ {A : Type a} (ev : E A) (k : A → iTree' E R), motive (iTree'.vis ev k))
--   (tau : (it : iTree' E R) → motive (.tau it)) :
--     ∀ (it' : iTree' E R), motive it' := fun it' => by
--   apply Quotient.ind (q := it'); intro it
--   change motive (iTree'.mk it)
--   apply it.obsEqElim
--   case inv =>
--     intro it₁ it₂ it₁it₂ mit₂
--     unfold mk
--     exact Quotient.sound it₁it₂ ▸ mit₂
--   case ret =>
--     intro v
--     simp [←ret_eq_mk_ret]
--     apply ret
--   case tau =>
--     intro it₂
--     simp [←tau_mk_eq_mk_tau it₂]
--     apply tau
--   case vis ev k =>
--     intro A ev k
--     simp [←vis_mk_eq_mk_vis ev k]
--     apply vis

-- -- Could we define this elimination principle on motives not in `Prop`?
-- def elim {R : Type r}{E : Type a → Type e} {motive : iTree' E R → Type _}
--   (ret : (v : R) → motive (.ret v))
--   (vis : ∀ {A : Type a} (ev : E A) (k : A → iTree' E R), motive (iTree'.vis ev k))
--   (tau : (it : iTree' E R) → motive (.tau it)) :
--     ∀ (it' : iTree' E R), motive it' := fun it' => by
--   apply it'.rec (s := (instSetoid (E := E) (R := R))) (motive := motive)
--   case f =>
--     intro it
--     apply it.obsEqElim
--     case inv =>
--       intro it₁ it₂ it₁it₂ mit₂
--       exact Quotient.sound it₁it₂ ▸ mit₂
--     case ret =>
--       intro v
--       sorry
--     case tau =>
--       sorry
--     case vis =>
--       sorry
--   case h =>
--     intro it₁ it₂ it₁it₂
--     simp
--     sorry

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

variable {E : Type quest → Type resp} {R : Type ret}

/-- The `IsDelayed` relation induces an order on `iTree`s which
  share a common finite preffix of `tau` nodes.  -/
inductive iTree.IsDelayedBy (it : iTree E R) : Nat → iTree E R → Prop where
  | refl : IsDelayedBy it 0 it
  | tau n it'' : IsDelayedBy it n it'' → it''.unfold = .tau it' → IsDelayedBy it (n+1) it'

namespace iTree.IsDelayedBy

theorem add {a b c : iTree E R} : a.IsDelayedBy n b → b.IsDelayedBy m c → a.IsDelayedBy (n+m) c
  | H, .refl => H
  | H₁, tau _ b' Hrest Hstep =>
    tau _ b' (add H₁ Hrest) Hstep

theorem split {a c : iTree E R} : a.IsDelayedBy (n + m) c → ∃ b, a.IsDelayedBy n b ∧ b.IsDelayedBy m c := by
  intro h
  induction m generalizing n a c with
  | zero =>
    refine ⟨c, h, .refl⟩
  | succ m IH =>
    simp [←Nat.add_assoc] at h
    cases h with
    | tau _ b' Hrest Hstep =>
      obtain ⟨b, Hfirst, Hthen⟩ := IH Hrest
      refine ⟨b, Hfirst, tau m b' Hthen Hstep⟩

theorem inj_right {a b c : iTree E R} : a.IsDelayedBy n b → a.IsDelayedBy n c → b = c
  | .refl, .refl => rfl
  | .tau _ _ Hrest Hstep, .tau _ _ Hrest₂ Hstep₂ =>
    let h := inj_right Hrest Hrest₂
    Obs.tau.inj (R := R) (E := E) <| Hstep ▸ Hstep₂ ▸ congrArg _ h

-- theorem uat n {it it' : iTree E R} it'' : it.unfold = .tau it'' →  it''.IsDelayedBy n it' → it.IsDelayedBy (1 + n) it' :=
--   fun Hstep Hrest => add (.tau 0 it (.refl) Hstep) Hrest

-- theorem revRec {motive : ∀ {it it' : iTree E R} {n}, it.IsDelayedBy n it' → Prop}
--   (refl : ∀ it, motive (.refl (it := it)))
--   (uat : ∀ (it it'' : iTree E R) n it' (Hstep : it.unfold = .tau it'') (Hrest : it''.IsDelayedBy n it'), motive (.uat n _ Hstep Hrest))
--   {it it' : iTree E R} {n} (h : it.IsDelayedBy n it') :
--     motive h :=
--   match n with
--   | 0 =>
--     let .refl := h
--     refl _
--   | n+1 =>
--     have ⟨_, .tau _ _ .refl Hstep , Hrest⟩ := split <| Nat.add_comm n 1 ▸ h
--     let res := uat _ _ n _ Hstep Hrest
--     by simpa only [Nat.add_comm 1 n] using res

theorem sub (n_m : n ≤ m) {a b c : iTree E R} : a.IsDelayedBy n b → a.IsDelayedBy m c → b.IsDelayedBy (m-n) c := by
  intro Hab Hac
  generalize h : m - n = x
  obtain rfl := Nat.add_comm .. ▸ Nat.eq_add_of_sub_eq n_m h
  have ⟨b', Hab', Hb'c⟩ := split Hac
  let .refl _ := inj_right Hab Hab'
  exact Hb'c

-- theorem min {a b c : iTree E R} : a.IsDelayedBy n b → a.IsDelayedBy m c → ∃ d, (d = b ∨ d = c) ∧ a.IsDelayedBy (n.min m) d := by
--   grind

end iTree.IsDelayedBy

-- def iTree.IsDelayed (it it' : iTree E R) := ∃ n, it.IsDelayedBy n it'
inductive iTree.IsDelayed : iTree E R → iTree E R → Prop where
  | refl {it : iTree E R}: IsDelayed it it
  | tau {it it' it'' : iTree E R} : it.unfold = .tau it' → it'.IsDelayed it'' → it.IsDelayed it''

namespace iTree.IsDelayed

def min {it it₁ it₂ : iTree E R} : it.IsDelayed it₁ → it.IsDelayed it₂ → it₁.IsDelayed it₂ ∨ it₂.IsDelayed it₁
  | .refl, h => .inl h
  | h, .refl => .inr h
  | tau (it' := it₁') Hstep Hrest, .tau (it' := it₂') Hstep' Hrest' =>
    have h : it₁' = it₂' := by grind only
    min Hrest (h ▸ Hrest')

end iTree.IsDelayed


inductive UpToFiniteTau (K : iTree E R → iTree E R → Prop) : iTree E R → iTree E R → Prop where
  | sync it₁ it₂ : K it₁ it₂ → UpToFiniteTau K it₁ it₂
  | drop_left (it₁ it₂ it₁' : iTree E R) :
    it₁.unfold = .tau it₁' →
    UpToFiniteTau K it₁' it₂ →
    UpToFiniteTau K it₁ it₂
  | drop_right (it₁ it₂ it₂' : iTree E R) :
    it₂.unfold = .tau it₂' →
    UpToFiniteTau K it₁ it₂' →
    UpToFiniteTau K it₁ it₂

def UpToFiniteTau.mono {K K' : iTree E R → iTree E R → Prop}
  (KK' : ∀{it it'}, K it it' → K' it it') {it it' : iTree E R} :
    UpToFiniteTau K it it' → UpToFiniteTau K' it it'
  | sync _ _ K₁₂ => sync _ _ (KK' K₁₂)
  | drop_left _ _ _ Htau₁ UTK₁'₂ => drop_left _ _ _ Htau₁ (UTK₁'₂.mono KK')
  | drop_right _ _ _ Htau₂ UTK₁₂' => drop_right _ _ _ Htau₂ (UTK₁₂'.mono KK')

def WeakBisim (it₁ it₂ : iTree E R ) : Prop :=
  -- ∃ it₁' it₂', it₁.IsDelayed it₁' ∧ it₂.IsDelayed it₂' ∧ RelOverObs WeakBisim Eq it₁'.unfold it₂'.unfold
  UpToFiniteTau (RelOverObs WeakBisim Eq ·.unfold ·.unfold) it₁ it₂
coinductive_fixpoint monotonicity by
  intro WB WB' WBimp it₁ it₂ WB₁₂
  -- have : ⟨it₁', it₂', it₁it₁', it₂it₂', WB₁₂⟩ := WB₁₂
  -- refine ⟨it₁', it₂', it₁it₁', it₂it₂', (RelOverObs.mono (WBimp _ _) id) WB₁₂⟩
  exact WB₁₂.mono (RelOverObs.mono (WBimp _ _) id)

namespace WeakBisim

@[refl]
def refl (it : iTree E R) : WeakBisim it it := by
  apply WeakBisim.coinduct (pred := (· = ·)) _ _ _ rfl
  intro it _ rfl
  apply UpToFiniteTau.sync
  apply Std.Refl.refl _

@[symm]
def symm (it₁ it₂ : iTree E R) : WeakBisim it₁ it₂ → WeakBisim it₂ it₁ := by
  intro H
  apply WeakBisim.coinduct (pred := flip WeakBisim) _ _ _ H
  clear H it₁ it₂
  intro it₁ it₂ H
  unfold flip WeakBisim at H
  -- have ⟨it₂', it₁', H₂, H₁, H⟩ := H
  -- exists it₁', it₂', H₁, H₂
  induction H with
  | sync it₁ it₂ H =>
    apply UpToFiniteTau.sync
    generalize h₁ : it₁.unfold = obs₁ at *
    generalize h₂ : it₂.unfold = obs₂ at *
    match H with
    | .ret _ _ H =>
      constructor; exact H.symm
    | .tau _ _ H =>
      constructor; exact H
    | .vis _ _ _ _ H =>
      constructor; exact H
  | drop_left it₁ it₂ it₁' Htau₁ UTT₁'₂ IH =>
    exact UpToFiniteTau.drop_right _ _ _ Htau₁ IH
  | drop_right it₁ it₂ it₂' Htau₂ UTT₁₂' IH =>
    exact UpToFiniteTau.drop_left _ _ _ Htau₂ IH

/--

  (RelOverObs WeakBisim Eq) it₁ it₂ →
  it₂.IsDelayed it₂  →
  ∃ it₁', it₁.IsDelayed it₁' ∧
  (RelOverObs WeakBisim Eq) it₁' it₂'

  -- Basically, we know `it₂` is a bunch of
  -- taus and it's

-/

-- def cases₂ {it₁ it₂ it₃ : iTree E R} : WeakBisim it₁ it₂ → WeakBisim it₂ it₃ →
--     ∃ (it₁' it₂' it₃' : iTree E R),
--     it₁.IsDelayed it₁' ∧
--     it₂.IsDelayed it₂' ∧
--     it₃.IsDelayed it₃' ∧
--     (RelOverObs WeakBisim Eq) it₁'.unfold it₂'.unfold ∧
--     (RelOverObs WeakBisim Eq) it₂'.unfold it₃'.unfold := by
--   intro H₁ H₂
--   unfold WeakBisim at *
--   have ⟨it₁', a, Hdel₁, Ha, H₁⟩ := H₁
--   have ⟨b, it₃', Hb, Hdel₃, H₂⟩ := H₂
--   suffices ∃ it₂', it₂.IsDelayed it₂' ∧
--       (RelOverObs WeakBisim Eq) it₁'.unfold it₂'.unfold ∧
--       (RelOverObs WeakBisim Eq) it₂'.unfold it₃'.unfold by grind
--   match Ha, Hb with
--   | .refl, .refl =>
--     refine ⟨it₂, .refl, H₁, H₂⟩
--   | .refl, .tau _ Hb =>
--     sorry
--   | .tau _ Ha, .refl =>
--     sorry
--   | .tau _ Ha, .tau _ Hb =>
--     sorry

def trans (it₁ it₂ it₃ : iTree E R) : WeakBisim it₁ it₂ → WeakBisim it₂ it₃ → WeakBisim it₁ it₃ := by
  intro H₁ H₂
  apply WeakBisim.coinduct (pred := fun x z => ∃ y , WeakBisim x y ∧ WeakBisim y z) _ _ _ ⟨_, H₁, H₂⟩
  clear H₁ H₂ it₁ it₂ it₃
  intro it₁ it₃ ⟨it₂, H₁, H₂⟩
  unfold WeakBisim at H₁ H₂
  induction H₁ with
  | sync it₁ it₂ RO₁₂ =>
    -- From `RO₁₂` we can deduce that the other relation must
    -- either also be sync, or that it has a `tau` on `it₂`
    generalize Hobs₁ : it₁.unfold = obs₁ at *
    generalize Hobs₂ : it₂.unfold = obs₁ at *
    match RO₁₂ with
    | .ret v₁ v₂ H =>
      -- We deduce that H₂ must also be a `.sync.ret`
      induction H₂ with
      | sync it₂ it₃ R₂₃ =>
        rw [Hobs₂] at R₂₃
        generalize Hobs₃ : it₃.unfold = obs₃ at *
        cases R₂₃
        apply UpToFiniteTau.sync
        rw [Hobs₁, Hobs₃]
        constructor
        grind
      | drop_right it₂ it₃ it₂' Htau₂ H₂ IH =>
        apply UpToFiniteTau.drop_right _ _ _ Htau₂
        apply IH; assumption
      | drop_left it₂ it₃ it₂' Htau₂ H₂ => grind
    | .vis A ev k₁ k₂ H =>
      -- We deduce that H₂ must also be a `.sync.vis`
      induction H₂ with
      | sync it₂ it₃ R₂₃ =>
        rw [Hobs₂] at R₂₃
        generalize Hobs₃ : it₃.unfold = obs₃ at *
        cases R₂₃
        apply UpToFiniteTau.sync
        rw [Hobs₁, Hobs₃]
        constructor
        grind
      | drop_right it₂ it₃ it₂' Htau₂ H₂ IH =>
        apply UpToFiniteTau.drop_right _ _ _ Htau₂
        apply IH; assumption
      | drop_left it₂ it₃ it₂' Htau₂ H₂ => grind
    | .tau it₁' it₂' H =>
      -- This is the tricky case. It doesn't really tell us much about
      -- the second relation, only that it must be of some `tau`.
      induction H₂ with
      | sync it₂ it₃ R₂₃ =>
        -- We are able to deduce that it₃ is `tau`.
        rw [Hobs₂] at R₂₃
        generalize Hobs₃ : it₃.unfold = obs₃ at *
        rcases R₂₃ with (_ | _ | it₃')
        apply UpToFiniteTau.sync
        rw [Hobs₁, Hobs₃]
        apply RelOverObs.tau
        exists it₂'
      | drop_left it₂ it₃ it₂'' Htau₂ H₂ IH =>
        obtain rfl : it₂' = it₂'' := by grind
        clear IH
        -- This really tells us nothing. We proceed
        -- by induction again, since at some point
        -- we must exhaust this case.
        induction H₂ with
        | sync it₂' it₃ R₂₃ =>
          generalize Hobs₂' : it₂'.unfold = obs₂' at *
          generalize Hobs₃ : it₃.unfold = obs₃ at *
          cases R₂₃ with
          | ret v₂ v₃ H =>
            sorry
          | vis A ev k₂ k₃ H =>
            sorry
          | tau it₂'' it₃' H' =>
            apply UpToFiniteTau.sync
            simp only [*]
            constructor
            refine ⟨it₂', H, ?_⟩
            unfold WeakBisim
            apply UpToFiniteTau.drop_left _ _ _ Hobs₂'
            unfold WeakBisim at H'
            assumption
        | drop_left it₂ it₃ it₂' Htau₂' R₂₃ IH =>
          sorry
        | drop_right it₂ it₃ it₃' Htau₃ R₂₃ IH =>
          sorry
      | drop_right it₂ it₃ it₃' Htau₃ H₂ IH =>
        -- rw [Hobs₁, Htau₃]
        apply UpToFiniteTau.drop_right _ _ _ Htau₃
        apply IH
        assumption
  | drop_left it₁ it₂ it₁' Htau₁ RO₁'₂ IH =>
    -- Proceed simply by induction
    apply UpToFiniteTau.drop_left _ _ _ Htau₁
    apply IH H₂
  | drop_right it₁ it₂ RO₁₂ =>
    sorry

  -- replace ⟨it₁', it₂', h₁, h₂, H₁'₂'⟩ := H₁
  -- replace ⟨it₂'', it₃', h₂', h₃, H₂''₁'⟩ := H₂
  -- have := iTree.IsDelayed.min h₂ h₂'
  -- -- We need to use `induction` since we need to use the recursor of `UpToFiniteTau`.
  -- generalize Hobs₁ : it₁'.unfold = obs₁ at *
  -- generalize Hobs₂ : it₂'.unfold = obs₂ at *
  -- generalize Hobs₂' : it₂'.unfold = obs₂ at *
  -- generalize Hobs₃ : it₃'.unfold = obs₃ at *
  -- match H₁'₂', H₁''₂' with
  -- | .ret v₁ v₂ H₁, .ret _ v₃ H₂ =>
  --   sorry
  -- | .tau jt₁ jt₂ H₁, .tau _ jt₂
  -- | tau it
  -- -- | @sync it₁ it₂ RO₁₂ =>
  -- --   rename_i aux2 aux; clear aux2 aux
  -- --   generalize Hobs₁ : it₁.unfold = obs₁ at *
  -- --   generalize Hobs₂ : it₂.unfold = obs₂ at *
  -- --   -- generalize Hobs₃ : it₃.unfold = obs₃ at *
  -- --   match RO₁₂ with
  -- --   | .tau it₁' it₂' H =>
  -- --     apply UpToFiniteTau.drop_left _ Hobs₁
  -- --     induction H₂ generalizing it₁' with
  -- --     | @sync it₂ it₃ RO₂₃ =>
  -- --       rename_i aux aux2; clear aux aux2
  -- --       sorry
  -- --     | @drop_left it₂ it₃ it₂' Htau₂ UTT₂'₃ IH =>
  -- --       rename_i aux aux2; clear aux aux2
  -- --       sorry
  -- --     | @drop_right it₂ it₃ it₂' Htau₂ UTT₂'₃ IH =>
  -- --       rename_i aux aux2; clear aux aux2
  -- --       sorry
  -- --   | .ret _ _ H =>
  -- --     sorry
  -- --   | .vis _ _ _ _ H =>
  -- --     sorry

    induction H₂ generalizing it₁ with
    | @sync it₂ it₃ RO₂₃ =>
      rename_i aux aux2; clear aux aux2
      apply UpToFiniteTau.sync
      generalize Hobs₁ : it₁.unfold = obs₁ at *
      generalize Hobs₂ : it₂.unfold = obs₂ at *
      generalize Hobs₃ : it₃.unfold = obs₃ at *
      match RO₁₂, RO₂₃ with
      | .ret v₁ v₂ H₁, .ret _ v₃ H₂ =>
        constructor; exact H₁.trans H₂
      | .tau it₁ it₂ H₁, .tau _ it₃ H₂ =>
        constructor; exists it₂
      | .vis A ev k₁ k₂ H₁, .vis _ _ _ k₃ H₂ =>
        constructor; intro x; exists k₂ x; simp [*]
    | @drop_left it₂ it₃ it₂' Htau₂ UTT₂'₃ IH =>
      rename_i aux aux2; clear aux aux2
      rw [Htau₂] at RO₁₂
      generalize Hobs₁ : it₁.unfold = obs₁ at *
      cases RO₁₂
      case tau it₁' RO₁'₂' =>
        apply UpToFiniteTau.drop_left it₁' Hobs₁
        apply IH
        apply UpToFiniteTau.sync
        rw [Hobs₁]
        sorry
    | @drop_right _ _ it₃' Htau₃ UTT₂'₃ IH =>
      rename_i aux
      apply UpToFiniteTau.drop_right it₃' Htau₃
      apply IH
      assumption
  | @drop_left it₁ it₁' it₂ Htau₁ UTT₁'₂ IH =>
    -- apply UpToFiniteTau.drop_left _ _ _ Htau₁
    -- apply UpToFiniteTau.sync
    -- rename_i aux₁ aux₂ aux₃; clear H₁ H₂ aux₁ aux₂ aux₃
    sorry
  | @drop_right it₁ it₂ it₂' Htau₂ UTT₁₂' IH =>
    -- rename_i aux₁ aux₂ aux₃; clear H₁ H₂ aux₁ aux₂ aux₃
    sorry
  -- match H₁, H₂ with
  -- | .sync it₁ it₂ RO₁₂, .sync _ it₃ RO₂₃ =>
  --   clear H₁ H₂
  --   apply UpToFiniteTau.sync
  --   generalize h₁ : it₁.unfold = obs₁ at *
  --   generalize h₂ : it₂.unfold = obs₂ at *
  --   generalize h₃ : it₃.unfold = obs₃ at *
  --   match RO₁₂, RO₂₃ with
  --   | .ret v₁ v₂ H₁, .ret _ v₃ H₂ =>
  --     constructor; exact Trans.trans H₁ H₂
  --   | .tau it₁ it₂ H₁, .tau _ it₃ H₂ =>
  --     constructor; exact ⟨it₂, H₁, H₂⟩
  --   | .vis A ev k₁ k₂ H₁, .vis _ _ _ k₃ H₂ =>
  --     constructor; intro x; exact ⟨k₂ x, H₁ x, H₂ x⟩
  -- | .sync it₁ it₂ RO₁₂, .drop_left _ it₂' it₃ Htau₂ UTT₂'₃ =>
  --   rename_i aux₁ aux₂ aux₃; clear H₁ H₂ aux₁ aux₂ aux₃
  --   rw [Htau₂] at RO₁₂
  --   generalize Htau₁ : it₁.unfold = obs₁ at *
  --   cases RO₁₂
  --   case tau it₁' RO₁'₂' =>
  --     have h := trans it₁' it₃ (UpToFiniteTau.sync _ _ RO₁'₂') UTT₂'₃
  --     sorry
  -- | .sync it₁ it₂ RO₁₂, .drop_right _ it₂' it₃ Htau₂ UTT₂'₃ =>
  --   rename_i aux₁ aux₂ aux₃; clear H₁ H₂ aux₁ aux₂ aux₃
  --   sorry
  -- | .drop_left it₁ it₁' it₂ Htau₁ UTT₁'₂, H₂ =>
  --   rename_i aux₁ aux₂ aux₃; clear H₁ H₂ aux₁ aux₂ aux₃
  --   sorry
  -- | .drop_right it₁ it₂ it₂' Htau₂ UTT₁₂', H₂ =>
  --   rename_i aux₁ aux₂ aux₃; clear H₁ H₂ aux₁ aux₂ aux₃
  --   sorry

  -- | .inr UTT₁₂, .inl RO₂₃ =>
  --   clear H₁ H₂
  --   apply Or.inl
  --   induction UTT₁₂ with
  --   | sync it₁ it₂ Hs₁₂ =>
  --     sorry
  --   | drop_left it₁ it₁' it₂ Htau₁ UTT₁'₂ =>
  --     sorry
  --   | drop_right it₁ it₂ it₂' Htau₂ UTT₁₂' =>
  --     sorry
  -- | .inl RO₁₂, .inr UTT₂₃ =>
  --   sorry
  -- | .inr UTT₁₂, .inr UTT₂₃ =>
  --   clear H₁ H₂
  --   apply Or.inr
  --   -- TODO:
  --   -- I would like to say that we concat UT₁₂ and UT₂₃,
  --   -- but actually we can't because WeakBisim is not
  --   -- guaranteed to be transitive yet... So we need to
  --   -- replay the `trans` proof again. Room to factorize
  --   -- maybe?
  --   sorry


end WeakBisim

end WeakBisimulation

end EqualitiesOverITrees

end StateMachine
