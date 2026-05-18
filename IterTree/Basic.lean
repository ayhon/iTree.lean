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

namespace StateMachine

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
  curr : PUnit.{s+1}  := .unit
  step _ := .ret r

def vis.{s} {α : Type q} (ev : E α) (k : α → iTree.{_,_,_,s} E R) : iTree E R where
  curr : PUnit.{max q s +1} ⊕ (a : α) × (k a ).State := .inl .unit
  step
  | .inl .unit => .vis ev (fun a => .inr <| ⟨a, (k a).curr⟩)
  | .inr ⟨a, s⟩ => (k a).step s |>.mapState (.inr ⟨a, ·⟩)

def tau.{s} (it : iTree.{_,_,_,s} E R) : iTree E R where
  -- We basically generate an artificial prior element in the state.
  curr : PUnit.{s+1} ⊕ it.State  := .inl .unit
  step
  | .inl .unit => .tau <| .inr <| it.curr
  | .inr s => it.step s |>.mapState (.inr)

end iTree

def Obs.toITree : Obs E R (iTree E R) → iTree E R
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

namespace WrongEq

/--
  This is the wrong notion of equality!

  It allows one to identify `fun _ => .ret 0` with `.skip`!
-/
def eq {α} (it₁ it₂ : iTree E α) : Prop :=
  match it₁.unfold, it₂.unfold with
  | .ret v₁, .ret v₂ => v₁ = v₂
  | @Obs.vis _ _ _ A₁ ev₁ k₁, @Obs.vis _ _ _ A₂ ev₂ k₂ =>
    ∃ (h : A₁ = A₂), ev₁ ≍ ev₂ ∧ ∀ a, eq (k₁ a) (k₂ (h.mp a))
  | .tau it₁, _
  | _, .tau it₂ => eq it₁ it₂
  | _, _ => False
coinductive_fixpoint monotonicity fun f f' himp => by
  intro it₁ it₂
  match h : it₁.unfold with
  | .ret v₁ =>
    simp only [h]
    match it₂.unfold with
    | .ret v₁ =>
      simp only
      intro h; exact h
    | @Obs.vis _ _ _ A₁ ev₁ k₁ =>
      simp only
      intro h; exact h
    | .tau it₁ =>
      simp only
      intro h
      apply himp
      exact h
  | @Obs.vis _ _ _ A₁ ev₁ k₁ =>
    simp only [h]
    match h : it₂.unfold with
    | .ret v₁ =>
      simp only
      intro h; exact h
    | @Obs.vis _ _ _ A₁ ev₁ k₁ =>
      simp only
      rintro ⟨rfl, rfl, hk⟩
      refine ⟨rfl, ?_⟩
      refine ⟨.rfl, ?_⟩
      intro a
      specialize hk a
      apply himp
      exact hk
    | .tau it₁ =>
      simp only
      intro h
      apply himp
      exact h
  | .tau it₁ =>
    simp only [h]
    match it₂.unfold with
    | .ret v₁ =>
      intro h
      apply himp
      exact h
    | @Obs.vis _ _ _ A₁ ev₁ k₁ =>
      intro h
      apply himp
      exact h
    | .tau it₁ =>
      intro h
      apply himp
      exact h

end WrongEq

/-

To define the right notion, we have to define what is a weak bisimulation.

-/

namespace FirstTry

inductive wb (r : iTree E V → iTree E V → Prop) : iTree E V → iTree E V → Prop where
| ret  : ∀ v : V,                  wb r (.ret v) (.ret v)
| sync : ∀ it₁ it₂,    r it₁ it₂ → wb r (.tau it₁) (.tau it₂)
| tauL : ∀ it₁ it₂, wb r it₁ it₂ → wb r (.tau it₁) it₂
| tauR : ∀ it₁ it₂, wb r it₁ it₂ → wb r (.tau it₁) it₂
| vis  : ∀ ev₁ k₁ ev₂ k₂, ev₁ = ev₂ → (∀ a, r (k₁ a) (k₂ a)) → wb r (.vis ev₁ k₁) (.vis ev₂ k₂)
-- Does this work? We can't really pattern match on `it`.

-- Maybe we can fix it with this?
public def wb' (r : iTree E V → iTree E V → Prop) (it₁ it₂ : iTree E V) : Prop :=
   wb r it₁.unfold.toITree it₂.unfold.toITree

def bisimulation : iTree E V → iTree E V → Prop := wb bisimulation
coinductive_fixpoint monotonicity fun r r' himp => by
  intro it₁ it₂ H
  induction H with
  | ret v =>  constructor
  | sync it₁ it₂ R =>
    constructor; apply himp; assumption
  | vis ev k =>
    constructor
    · assumption
    · intros; apply himp; grind only
  | tauL it₁ it₂ _ IH =>
    constructor; assumption
  | tauR it₁ it₂ _ IH =>
    constructor; assumption

/-

However, this definition doesn't work because we can't identify every possible
iTree in terms of construction of `.tau`, `.vis` and `.ret`. We have no destructor
for `iTree`!

-/

end FirstTry

namespace SecondTry

public inductive wb (r : iTree E V → iTree E V → Prop) : iTree E V → iTree E V → Prop where
| ret {it₁ it₂}  : ∀ v : V,
    it₁.unfold = .ret v → it₂.unfold = .ret v →
    wb r it₁ it₂
| vis  {it₁ it₂} : ∀ ev₁ k₁ ev₂ k₂,
    it₁.unfold = .vis ev₁ k₁ → it₂.unfold = .vis ev₂ k₂ → -- Maybe even these equalities are a bit much…
    ev₁ = ev₂ → (∀ a, r (k₁ a) (k₂ a)) →
    wb r it₁ it₂
| sync {it₁ it₂} : ∀ it₁' it₂',
    it₁.unfold = .tau it₁' → it₂.unfold = .tau it₂' →
    r it₁' it₂' →
    wb r it₁ it₂
| tauL {it₁ it₂} : ∀ it₁',
    it₁.unfold = .tau it₁' →
    wb r it₁' it₂ →
    wb r it₁ it₂
| tauR {it₁ it₂} : ∀ it₂',
    it₂.unfold = .tau it₂' →
    wb r it₁ it₂ → wb r it₁ it₂

def eq : iTree E V → iTree E V → Prop := wb eq
coinductive_fixpoint monotonicity fun r r' himp => by
  intro it₁ it₂ H
  induction H with
  | ret v h₁ h₂ =>
    apply wb.ret v h₁ h₂
  | sync it₁ it₂ h₁ h₂ R =>
    apply wb.sync it₁ it₂ h₁ h₂
    apply himp; assumption
  | vis ev₁ k₁ ev₂ k₂ h₁ h₂ hev IH =>
    apply wb.vis ev₁ k₁ ev₂ k₂ h₁ h₂ hev
    intros; apply himp; grind
  | tauL it₁' h₁ _ IH =>
    apply wb.tauL it₁' h₁ IH
  | tauR it₂' h₂ _ IH =>
    apply wb.tauR it₂' h₂ IH
-- TODO: Is this the correct notion of equality?
-- TODO: Is this equivalent to `FirstTry.bisimulation`?
--       Or what's equivalent, is `FirstTry.wb'` equivalent to `wb` here?

end SecondTry

namespace ThirdTry

local instance : Std.Refl (Eq (α := α)) where refl := .refl 
local instance : Std.Symm (Eq (α := α)) where symm _ _:= .symm

variable {E : Type quest → Type resp}{R : Type ret}

/-

We define a weaker version of equality, observational

-/

--- lift (?). Maybe with `postFix`? ObsRelF? `eqitF` maybe
-- coinduction template

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

@[symm]
theorem symm {it₁ it₂ : iTree E R} [Std.Symm r]: StrongBisim r it₁ it₂ → StrongBisim r it₂ it₁  := by
  intro start
  apply coinduct r (pred := λ x y ↦ StrongBisim r y x) ?_ _ _ start
  intro it₁ it₂ it₂it₁
  have ⟨obs₁, obs₂, h₁, h₂, cases⟩ := StrongBisim.cases it₂it₁
  match cases with 
  | .ret v₁ v₂ h => 
    rw [h₁, h₂]; constructor; apply Std.Symm.symm _ _ h
  | .tau it₁ it₂ h => 
    rw [h₁, h₂]; constructor; exact h
  | .vis A ev k₁ k₂ h => 
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

instance : HasEquiv (Obs E R (iTree E R)) where
  Equiv := RelOverObs (· ≈ ·) (· = ·)

def ObsEq.coinductOn
  {it₁ it₂ : iTree E R} 
  (pred : iTree E R → iTree E R → Prop)
  (baseCase : pred it₁ it₂)
  (progress : ∀ (it₁ it₂ : iTree E R), pred it₁ it₂ → RelOverObs pred (· = ·) it₁.unfold it₂.unfold) :
    it₁ ≈ it₂ := 
  StrongBisim.coinduct (· = ·) pred progress _ _ baseCase

theorem obsEq_unfold {it it' : iTree E R} : 
    it ≈ it' ↔ it.unfold ≈ it'.unfold :=
  ⟨(StrongBisim.eq_def .. |>.mp ·), (StrongBisim.eq_def .. |>.mpr ·)⟩

def ObsEq.step_tau_obsEq_self (it : iTree E R) (s : it.State) c :
    {it with curr := s} ≈ { {it with curr := c}.tau with curr := .inr s } := by
  apply coinductOn (fun
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
    simp [tau, Obs.mapState]
  case progress =>
    intro it₁ it₂ ⟨H, HC, Hs⟩
    cases h : it₁.step it₁.curr <;> simp only [h, unfold, HC, Obs.mapState, Hs]
    case ret v => 
      constructor; rfl
    case tau it => 
      constructor
      exists H
    case vis ev k => 
      constructor
      intros
      exists H

def ObsEq.step_vis_obsEq_self (it : iTree E R) (ev : E A) (kS : A → it.State) (a : A) :
    { curr := kS a, step := it.step : iTree E R} ≈
    { curr : Unit ⊕ (_ : A) × it.State := Sum.inr ⟨a, kS a⟩,
        step := fun x =>
          match x with
          | Sum.inl PUnit.unit => Obs.vis ev fun a => Sum.inr ⟨a, kS a⟩
          | Sum.inr ⟨a, s⟩ => Obs.mapState (fun x => Sum.inr ⟨a, x⟩) (it.step s) } := by
  apply coinductOn (fun
    (iTree.mk (State := State₁) curr₁ step₁)
    (iTree.mk (State := State₂) curr₂ step₂) =>
    ∃ (mpr : (PUnit ⊕ (_ : A) × State₁) → State₂),
    curr₂ = mpr (Sum.inr ⟨a, curr₁⟩) ∧
    ∀ (s : State₁),
    step₂ (mpr (.inr ⟨a, s⟩)) = (step₁ s).mapState (mpr <| .inr ⟨a, ·⟩)
  )
  case baseCase =>
    exists id
    simp [Obs.mapState]
  case progress =>
    rintro it₁ it₂ ⟨H, HC, Hs⟩
    cases h : it₁.step it₁.curr <;> simp only [h, unfold, HC, Hs, Obs.mapState]
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
  simp [unfold, tau]
  constructor
  change ({ it₁.tau with curr := .inr it₁.curr } ≈ { it₂.tau with curr := .inr it₂.curr })
  calc { it₁.tau with curr := .inr it₁.curr }
    _ ≈ (it₁ : iTree E R) := (step_tau_obsEq_self ..).symm
    _ ≈ it₂ := h
    _ ≈ { it₂.tau with curr := .inr it₂.curr } := (step_tau_obsEq_self ..)

theorem ObsEq.unfold_vis (ev : E A) (k : A → iTree E R) :
    (iTree.vis ev k).unfold ≈ (Obs.vis ev k) := by
  simp [unfold, iTree.vis]
  refine RelOverObs.vis _ _ _ _ ?_
  intro a
  apply coinductOn (fun
    (iTree.mk (State := State₂) curr₂ step₂)
    (iTree.mk (State := State₁) curr₁ step₁) =>
    ∃ (mpr : (Unit ⊕ (_ : A) × State₁) → State₂),
    curr₂ = mpr (Sum.inr ⟨a, curr₁⟩) ∧
    ∀ (s : State₁),
    step₂ (mpr (.inr ⟨a, s⟩)) = (step₁ s).mapState (mpr <| .inr ⟨a, ·⟩)
  )
  case baseCase =>
    simp
    exists (fun | .inl .unit => .inl .unit
                | .inr ⟨_, st⟩ => .inr ⟨a, st⟩ )
    simp only [implies_true, and_self]
  case progress =>
    rintro it₁ it₂ ⟨H, HC, Hs⟩
    cases h : it₂.step it₂.curr <;> simp only [h, unfold, HC, Hs, Obs.mapState]
    case ret v => 
      constructor; rfl
    case tau it => 
      constructor
      exists H
    case vis ev k => 
      constructor
      intros
      exists H

      
theorem ObsEq.obsEq_ret_of_unfold_ret {it : iTree E R} {v : R} : it.unfold = .ret v → it ≈ .ret v := by
  simp [unfold]
  cases h : it.step it.curr <;> simp
  rintro rfl
  unfold StrongBisim
  simp only [h, unfold, ret]
  constructor; rfl

theorem ObsEq.obsEq_tau_of_unfold_tau {it it': iTree E R} : it.unfold = .tau it' → it ≈ .tau it' := by
  simp [unfold]
  cases h : it.step it.curr <;> simp
  case tau st =>
    rintro rfl
    simp [tau] at *
    apply coinductOn (fun
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
      cases h : it₁.step it₁.curr <;> simp only [h, unfold, Hc, Obs.mapState]
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
  simp only [unfold]
  cases h : it.step it.curr <;> simp [reduceCtorEq, false_implies]
  case vis A ev kS =>
    rintro rfl rfl rfl
    unfold StrongBisim
    simp only [unfold, h, vis]
    apply RelOverObs.vis _ _ _ _ ?_
    intro a
    apply ObsEq.coinductOn (fun
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
      cases h : s₁ c₁ <;> simp only [h, unfold, HC, Hs, Obs.mapState]
      case ret v => 
        constructor; rfl
      case tau it => 
        constructor
        exists H
      case vis ev k => 
        constructor
        intros
        exists H

def iTree.obsEqElim {motive : iTree E R → Type _}
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

#check Quotient.mk
#check Quotient.lift
#check Quotient.sound

namespace iTree'

def mk (it : iTree E R)  := Quotient.mk instSetoid it

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

-- picks an element out of the quotient, but bumps up the universes
def out (it' : iTree' E R) : iTree E R where
    curr := it'
    step := iTree'.unfold

/- theorem unfold_out (it' : iTree' E R) : -/
/-     ObsRel (·=·) (it'.unfold.mapState (·.out)) (it'.out.unfold) := -/
  -- Basically, we can unfold either in the quotient our outside of it
    /- sorry -/
/-   apply it'.ind -/
/-   intros it -/
/-   cases h: it.unfold <;> -/
/-   simp [h, unfold, Quotient.lift, Quotient.mk, out, Obs.mapState] -/
/-   sorry -/

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

-- def vis {A : Type a} {R : Type _}{E : Type a → Type _} (ev : E A) (k' : A → iTree' E R) : iTree' E R :=
--   let k := fun a =>
--     (k' a).out
--   iTree'.mk (.vis ev k)

-- /- set_option pp.universes true in -/
-- -- TODO: The issue here is that we're comparing things at different universe levels.
-- -- In a sense, this is allowing us to `shrink` the universes.
-- theorem unfold_eq_vis (it' : iTree'.{quest,resp,ret,s} E R) (ev : E A) (k' : A → iTree'.{quest,resp,ret,s} E R) :
--     it'.unfold = .vis ev k' →
--     it' = iTree'.vis ev k'
--     := by
--   apply it'.ind; intros it
--   intros h
--   simp [tau, Quotient.lift, Quotient.mk]
--   apply Quotient.sound
--   simp [unfold, Quotient.lift, Quotient.mk, Obs.mapState] at h
--   cases h₂ : it.unfold <;> simp [h₂] at h
--   case a.tau it₂ =>
--     have h := Quotient.exact h
--     apply ObsEq.obsEq_tau_of_obsEq_unfold_tau h₂ h

section doubious

instance piSetoid {ι : Sort _} {α : ι → Sort _} [∀ i, Setoid (α i)] : Setoid (∀ i, α i) where
  r a b := ∀ i, a i ≈ b i
  iseqv := ⟨fun _ _ ↦ Setoid.refl _,
            fun h _ ↦ Setoid.symm (h _),
            fun h₁ h₂ _ ↦ Setoid.trans (h₁ _) (h₂ _)⟩

unsafe def _root_.Quot.unquot {r : α → α → Prop} : Quot r → α :=
  cast lcProof

unsafe
def Quotient.bubbleUpUnsafe {X A : Type _}{s : Setoid X}(f : A → Quotient s) : Quotient (piSetoid : Setoid (A → X)) :=
  .mk (_) (fun i ↦ (f i).unquot)

noncomputable def _root_.Quot.out {r : α → α → Prop} (q : Quot r) : α :=
  Classical.choose (Quot.exists_rep q)

noncomputable def _root_.Quotient.choice {ι : Type _} {α : ι → Type _} {S : ∀ i, Setoid (α i)}
    (f : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) (by infer_instance) :=
  .mk _ (fun i ↦ (f i).out)

@[implemented_by Quotient.bubbleUpUnsafe]
noncomputable
def _root_.Quotient.bubbleUp{X A : Type _}{s : Setoid X}(f : A → Quotient s) : Quotient (piSetoid : Setoid (A → X)) :=
  Quotient.choice (ι := A) (α := λ_↦X) (S := λ_↦s) f

end doubious



def vis {A : Type a} {R : Type _}{E : Type a → Type _} (ev : E A) (k' : A → iTree' E R) : iTree' E R :=
  (Quotient.bubbleUp k').lift (.mk <| iTree.vis ev ·) (
    fun k₁ k₂ k₁k₂ =>
    Quotient.sound <| by
    -- I need some kind of congruence lemma for `iTree.tau`
    sorry -- TODO: Put it all together, may need to define symm and trans for `ObsRel`.
  )

def elim {R : Type r}{E : Type a → Type e} {motive : iTree' E R → Type _}
  (ret : (v : R) → motive (.ret v))
  (vis : ∀ {A : Type a} (ev : E A) (k : A → iTree' E R), motive (iTree'.vis ev k))
  (tau : (it : iTree' E R) → motive (.tau it)) :
    ∀ (it' : iTree' E R), motive it' := fun it => by
  sorry

end iTree'

end ThirdTry

end EqualitiesOverITrees

end iTree

end StateMachine
