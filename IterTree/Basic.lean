import IterTree.QuotientTrick

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

theorem RelOverObs.mono (s s' : S₁ → S₂ → Prop) (r r' : R → R → Prop) : 
    (∀ {i i'}, s i i' → s' i i') →
    (∀ {v v'}, r v v' → r' v v') →
     ∀ o (o' : Obs E R S₂), (RelOverObs s r) o o' → (RelOverObs s' r') o o' := 
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
  fun Rel Rel' Rimp it₁ it₂ H =>
  RelOverObs.mono Rel' Rel _ _ (Rimp _ _) id it₁.unfold it₂.unfold H

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

local instance : Std.Refl (Eq (α := α)) where refl := .refl
local instance : Std.Symm (Eq (α := α)) where symm _ _:= .symm

variable {E : Type quest → Type resp} {R : Type ret}

/-
  NOTE: For `drop_left` and `drop_right` to work nicely, we need to be
  able to confuse `Obs E R (iTree E R)` and `iTree E R`. In the end,
  we want to postulate
      RelOverObsUpToTau s r it₁ it₂ → RelOverObsUpToTau s r (.tau it₁) it₂
      RelOverObsUpToTau s r it₁ it₂ → RelOverObsUpToTau s r it₁ (.tau it₂)
  But then we have `it₂ : Obs E R (iTree E R)` from the hypothesis and 
  `it₂ : iTree E R` from the `.tau` application.

  This wouldn't be an issue if we used `iTree'`, since then we can drop `Obs`
  altogether and just use the custom eliminator we just defined. However, I
  would like to keep from using that for now since I'm not convinced on how
  `Quotient.bubbleUp` was defined.

  We can circunvent this by explicitly calling `unfold` in the recursive call.
  This is leaking a bit the abstraction of our `WeakBisim`, which is just a
  call to `.unfold` of a `RelOverObsUpToTau` using `WeakBisim` itself 
  coinductively, but we can revisit the formalization later to clean it up.
-/

inductive UpToFiniteTau (s : iTree E R → iTree E R →  Prop) :
    iTree E R → iTree E R → Prop where
  | sync it₁ it₂ : s it₁ it₂ → UpToFiniteTau s it₁ it₂
  | drop_left it₁ it₁' it₂ :
    it₁.unfold = .tau it₁' →
    UpToFiniteTau s it₁' it₂ →
    UpToFiniteTau s it₁ it₂
  | drop_right it₁ it₂ it₂' :
    it₂.unfold = .tau it₂' →
    UpToFiniteTau s it₁ it₂' →
    UpToFiniteTau s it₁ it₂

def UpToFiniteTau.mono {s s' : iTree E R → iTree E R →  Prop}
  (ss' : ∀{it₁ it₂}, s it₁ it₂ → s' it₁ it₂) {it₁ it₂ : iTree E R} :
    UpToFiniteTau s it₁ it₂ → UpToFiniteTau s' it₁ it₂
  | sync it₁ it₂ Hs =>
    sync it₁ it₂ (ss' Hs)
  | drop_left it₁ it₁' it₂ Htau₁ UTT₁'₂ =>
    drop_left it₁ it₁' it₂ Htau₁ (mono ss' UTT₁'₂)
  | drop_right it₁ it₂ it₂' Htau₂ UTT₁₂' =>
    drop_right it₁ it₂ it₂' Htau₂ (mono ss' UTT₁₂')

-- Useful if combined with `obsEqElim`
theorem UpToFiniteTau.sb_inv
  (s_inv : ∀ {it₁ it₂ it₁' it₂' : iTree E R}, s it₁ it₂ → s it₁' it₂')
  {it₁ it₂ jt₁ jt₂ : iTree E R} :
    it₁ ≈ jt₁ →
    it₂ ≈ jt₂ →
    UpToFiniteTau s it₁ it₂ →
    UpToFiniteTau s jt₁ jt₂ := by
  intro H₁ H₂ ovfts₁₂
  induction ovfts₁₂ generalizing jt₁ jt₂ with
  | sync it₁ it₂ Hs =>
    apply sync
    apply s_inv Hs
  | @drop_left it₁ it₁' it₂ Htau Hrec IH =>
    match H₁.cases with
    | ⟨.tau it₁'', .tau jt₁', Htau', Hjtau, .tau _ _ H ⟩ =>
      have H₁' : it₁' ≈ jt₁' := by grind only
      apply drop_left _ _ _ Hjtau
      apply IH H₁' H₂
    | ⟨.vis .., _, H, _, _⟩
    | ⟨.ret .., _, H, _, _⟩ =>
      grind only
  | @drop_right it₁ it₂ it₂' Htau Hrec IH =>
    match H₂.cases with
    | ⟨.tau it₂'', .tau jt₂', Htau', Hjtau, .tau _ _ H ⟩ =>
      have H₂' : it₂' ≈ jt₂' := by grind only
      apply drop_right _ _ _ Hjtau
      apply IH H₁ H₂'
    | ⟨.vis .., _, H, _, _⟩
    | ⟨.ret .., _, H, _, _⟩ =>
      grind only

@[refl]
theorem UpToFiniteTau.refl [Std.Refl s](it : iTree E R) : UpToFiniteTau s it it :=
  .sync _ _ (Std.Refl.refl _)

@[symm]
theorem UpToFiniteTau.symm [Std.Symm s]{it₁ it₂ : iTree E R} : UpToFiniteTau s it₁ it₂ → UpToFiniteTau s it₂ it₁
  | sync _ _ H => sync _ _ (Std.Symm.symm _ _ H)
  | drop_left _ _ _ Htau UTTl => drop_right _ _ _ Htau UTTl.symm
  | drop_right _ _ _ Htau UTTr => drop_left _ _ _ Htau UTTr.symm

theorem UpToFiniteTau.pushFront [Trans s s s]
  -- (s_inv_left : ∀ {it₁ it₁' it₂}, s it₁ it₂ → it₁.unfold = .tau it₁' → ∃ it₂', it₂.unfold = .tau it₂' ∧ s it₁' it₂' )
  (s_inv_right : ∀ {it₁ it₂ it₂'}, s it₁ it₂ → it₂.unfold = .tau it₂' → ∃ it₁', it₁.unfold = .tau it₁' ∧ s it₁' it₂' )
  {it₁ it₂ it₃ : iTree E R} :
    s it₁ it₂ → UpToFiniteTau s it₂ it₃ → UpToFiniteTau s it₁ it₃
  | Hs₁, sync _ _ Hs₂ => sync _ _ (Trans.trans Hs₁ Hs₂)
  | Hs₁, drop_left _ _it₂' _ Htau UTTl =>
    let ⟨it₁', Htau₁, Hs₁'⟩ := s_inv_right Hs₁ Htau
    let Hrec := UTTl.pushFront s_inv_right Hs₁'
    drop_left it₁ it₁' it₃ Htau₁ Hrec
  | Hs₁, drop_right _ _ it₃'  Htau UTTr =>
    let Hrec := UTTr.pushFront s_inv_right Hs₁
    drop_right _ _ it₃' Htau Hrec

theorem UpToFiniteTau.pushBack [Trans s s s]
  (s_inv_left : ∀ {it₁ it₁' it₂}, s it₁ it₂ → it₁.unfold = .tau it₁' → ∃ it₂', it₂.unfold = .tau it₂' ∧ s it₁' it₂' )
  -- (s_inv_right : ∀ {it₁ it₂ it₂'}, s it₁ it₂ → it₂.unfold = .tau it₂' → ∃ it₁', it₁.unfold = .tau it₁' ∧ s it₁' it₂' )
  {it₁ it₂ it₃ : iTree E R} :
    UpToFiniteTau s it₁ it₂ → s it₂ it₃ → UpToFiniteTau s it₁ it₃
  | sync _ _ Hs₁, Hs₂ => sync _ _ (Trans.trans Hs₁ Hs₂)
  | drop_left _ it₁' _ Htau UTTl, Hs₂ =>
    let Hrec := UTTl.pushBack s_inv_left Hs₂
    drop_left _ it₁' _ Htau Hrec
  | drop_right _ _ _it₂'  Htau UTTr, Hs₂=>
    let ⟨it₃', Htau₂, Hs₂'⟩ := s_inv_left Hs₂ Htau
    let Hrec := UTTr.pushBack s_inv_left Hs₂'
    drop_right _ _ it₃' Htau₂ Hrec

theorem UpToFiniteTau.inv_right [Trans s s s]
  -- (s_inv_left : ∀ {it₁ it₁' it₂}, s it₁ it₂ → it₁.unfold = .tau it₁' → ∃ it₂', it₂.unfold = .tau it₂' ∧ s it₁' it₂' )
  (s_inv_right : ∀ {it₁ it₂ it₂'}, s it₁ it₂ → it₂.unfold = .tau it₂' → ∃ it₁', it₁.unfold = .tau it₁' ∧ s it₁' it₂' )
  {it₁ it₂ it₂' : iTree E R} :
    UpToFiniteTau s it₁ it₂ → it₂.unfold = .tau it₂' → UpToFiniteTau s it₁ it₂'
  | sync _ _ Hs, Htau₂ =>
    let ⟨_it₁', Htau₁, Hs'⟩ := s_inv_right Hs Htau₂
    drop_left _ _ _ Htau₁ (sync _ _ Hs')
  | drop_left it₁ _it₁' it₂ Htau₁ UTTl, Htau₂ =>
    drop_left _ _ _ Htau₁ (UTTl.inv_right s_inv_right Htau₂)
  | drop_right it₁ _ it₂'' Htau₂' UTTr, Htau₂ =>
    have Heq : it₂'' = it₂' := Obs.tau.inj (E := E) (R := R) (Htau₂ ▸ Htau₂' ▸ rfl)
    Heq ▸ UTTr

theorem UpToFiniteTau.inv_left [Trans s s s]
  (s_inv_left : ∀ {it₁ it₁' it₂}, s it₁ it₂ → it₁.unfold = .tau it₁' → ∃ it₂', it₂.unfold = .tau it₂' ∧ s it₁' it₂' )
  -- (s_inv_right : ∀ {it₁ it₂ it₂'}, s it₁ it₂ → it₂.unfold = .tau it₂' → ∃ it₁', it₁.unfold = .tau it₁' ∧ s it₁' it₂' )
  {it₁ it₁' it₂ : iTree E R} :
    UpToFiniteTau s it₁ it₂ → it₁.unfold = .tau it₁' → UpToFiniteTau s it₁' it₂
  | sync _ _ Hs, Htau₁ =>
    let ⟨_it₂', Htau₂, Hs'⟩ := s_inv_left Hs Htau₁
    drop_right _ _ _ Htau₂ (sync _ _ Hs')
  | drop_left it₁ it₁'' it₂ Htau₁' UTTl, Htau₁ =>
    have Heq : it₁'' = it₁' := Obs.tau.inj (E := E) (R := R) (Htau₁ ▸ Htau₁' ▸ rfl)
    Heq ▸ UTTl
  | drop_right it₁ _ _it₂' Htau₂ UTTr, Htau₁ =>
    drop_right _ _ _ Htau₂ (UTTr.inv_left s_inv_left Htau₁)

theorem UpToFiniteTau.trans [Trans s s s]
  -- TOOD: Are the `s_inv` lemmas what we want?
  (s_inv_left : ∀ {it₁ it₁' it₂}, s it₁ it₂ → it₁.unfold = .tau it₁' → ∃ it₂', it₂.unfold = .tau it₂' ∧ s it₁' it₂' )
  (s_inv_right : ∀ {it₁ it₂ it₂'}, s it₁ it₂ → it₂.unfold = .tau it₂' → ∃ it₁', it₁.unfold = .tau it₁' ∧ s it₁' it₂' )
  {it₁ it₂ it₃ : iTree E R} :
    UpToFiniteTau s it₁ it₂ → UpToFiniteTau s it₂ it₃ → UpToFiniteTau s it₁ it₃ := by
  intro UTT₁₂ UTT₂₃
  induction UTT₁₂ generalizing it₃ with
  | sync _ _ Hs₁ =>
    exact UTT₂₃.pushFront s_inv_right Hs₁
  | drop_left it₁ it₁' it₂ Htau₁ UTT₁'₂ IH =>
    specialize IH UTT₂₃
    apply drop_left _ _ _ Htau₁ IH
  | drop_right it₁ it₂ it₂' Htau₂ UTT₁₂' IH =>
    cases UTT₂₃ with
    | sync _ _ Hs₂ =>
      exact (UpToFiniteTau.drop_right it₁ it₂ it₂' Htau₂ UTT₁₂').pushBack s_inv_left Hs₂
    | drop_left it₂ it₂'' it₃ Htau₂ UTT₂'₃ =>
      obtain rfl : it₂' = it₂'' := by grind only
      apply IH UTT₂'₃
    | drop_right it₂ it₃ it₃' Htau₃ UTT₂₃' =>
      let UTT₂'₃' := UTT₂₃'.inv_left s_inv_left Htau₂
      have := IH UTT₂'₃'
      apply drop_right it₁ it₃ it₃' Htau₃ this

/-

  Now, to obtain weak bisimulation, we just need to interleave StrongBisim and UpToFiniteTau

-/

def WeakBisim (it₁ it₂ : iTree E R ) : Prop :=
  RelOverObs WeakBisim (· = ·) it₁.unfold it₂.unfold
  ∨ UpToFiniteTau WeakBisim it₁ it₂
coinductive_fixpoint monotonicity by
  intro WB WB' WBimp it₁ it₂ WB₁₂
  match WB₁₂ with
  | .inl RO₁₂ =>
    exact Or.inl <| RelOverObs.mono (WBimp _ _) id RO₁₂
  | .inr UTT₁₂ =>
    exact Or.inr <| UpToFiniteTau.mono (WBimp _ _) UTT₁₂

namespace WeakBisim

@[refl]
def refl (it : iTree E R) : WeakBisim it it := by
  apply WeakBisim.coinduct (pred := (· = ·)) _ _ _ rfl
  intro it₁ it₂ rfl
  apply Or.inl <| Std.Refl.refl _

@[symm]
def symm (it₁ it₂ : iTree E R) : WeakBisim it₁ it₂ → WeakBisim it₂ it₁ := by
  intro H
  apply WeakBisim.coinduct (pred := flip WeakBisim) _ _ _ H
  intro it₁ it₂ H
  unfold flip WeakBisim at H
  match H with
  | .inl RO₁₂ =>
    apply Or.inl
    -- Can't apply RelOverObs.flip for some reason?
    generalize h₁ : it₁.unfold = obs₁
    generalize h₂ : it₂.unfold = obs₂
    rewrite [h₁, h₂] at RO₁₂
    match RO₁₂ with
    | .ret v₁ v₂ H =>
      constructor; exact H.symm
    | .tau it₁ it₂ H =>
      constructor; exact H
    | .vis A ev k₁ k₂ H =>
      constructor; exact (H ·)
  | .inr UTT₁₂ =>
    apply Or.inr
    clear H
    -- TODO: I would like to extract this proof into what is now `UpToFiniteTau.symm`
    induction UTT₁₂ with
    | sync _ _ H =>
      exact UpToFiniteTau.sync _ _ H
    | drop_left _ _ _ Htau _ IH =>
      exact .drop_right _ _ _ Htau IH
    | drop_right _ _ _ Htau _ IH =>
      exact .drop_left _ _ _ Htau IH

def trans (it₁ it₂ : iTree E R) : WeakBisim it₁ it₂ → WeakBisim it₂ it₃ → WeakBisim it₁ it₃ := by
  intro H₁ H₂
  apply WeakBisim.coinduct (pred := fun x z => ∃ y , WeakBisim x y ∧ WeakBisim y z) _ _ _ ⟨_, H₁, H₂⟩
  intro it₁ it₃ ⟨it₂, H₁, H₂⟩
  unfold WeakBisim at H₁ H₂
  match H₁, H₂ with
  | .inl RO₁₂, .inl RO₂₃ =>
    -- I would like to say `.inl <| RO₁₂.trans RO₂₃`, but actually I can't because we haven't proven that the
    -- relation is transitive (that's what we're proving rn)
    -- Maybe if I actually provide a relation that **is** transitive, and which allows me to prove this, it
    -- would be enough. Might be reason to revisit `TransGen`, `SymmGen` and `ReflGen`.
    sorry
  | .inr UTT₁₂, .inl RO₂₃ =>
    sorry
  | .inl RO₁₂, .inr UTT₂₃ =>
    sorry
  | .inr UTT₁₂, .inr UTT₂₃ =>
    sorry

end WeakBisim

end WeakBisimulation

end EqualitiesOverITrees

end StateMachine
