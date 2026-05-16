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

def Obs.mapState (f : α → β) : Obs E R α → Obs E R β
| .ret v => .ret v
| .tau st => .tau <| f st
| .vis ev k => .vis ev (fun x => f (k x))

def Obs.bindVal (f : α → Obs E β K) : Obs E α K → Obs E β K
| .ret v => f v
| .tau st => .tau st
| .vis ev k => .vis ev k


/- class IsITreeImpl (State : Type s) (E : Type q → Type r) (R : Type v) where -/
/-     step : State → Obs E R State -/

structure iTree (E : Type q → Type r) (R : Type v) where
  {State : Type s} -- TODO: Maybe rename to MetaState
  curr : State
  /- [stepImpl : IsITreeImpl State E R] -/
  step : State → Obs E R State

  -- Why not have it give observations on just `State`?
  -- I think it's not possible, because we must be able to change
  -- the state type at some point in the execution.
  --
  -- However, how do you define the infinitely looping
  -- computation with `State → Obs E R (iTree E R)`?
  -- You can't, you'd need to reference back to the think you're
  -- defining, but at that point it's no longer a fixpoint!

  -- In short, it can't be State → Obs E R (iTree E R) because
  -- then one can't really give an infinitely looping computation
  -- It also can't be `State → Obs E R State` because one should
  -- be able to encode that the state changes from one computation
  -- to another. Or can't it?
  --
  -- The issue with doing this encoding is that one must fix the
  -- type of the state of the final computation, but it's not
  -- trivial to define. For instance, one would like to say that
  -- when doing a `bind` with `f`, the state will originally be
  -- that of the interaction tree being executed, until it gives
  -- a value `a`, at which point one switches to the state of the
  -- `iTree` resulting from applying `f` to `a`. However, this
  -- cannot be expressed directly as a type.
  -- One could, however, express this as an invariant of the
  -- structure, which leads us back to the `IsPlausibleStep` of
  -- `Std.Iter`.
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

theorem unfold_cases (it : iTree E R) :
    (∃ v, it.unfold = .ret v) ∨
    (∃ (α : Type _) (ev : E α) (k : α → iTree E R), it.unfold = .vis ev k) ∨
    (∃ it', it.unfold = .tau it') :=
  match it.unfold with
  | .ret v => .inl ⟨v, rfl⟩
  | .vis (A := α) ev k => .inr <| .inl ⟨α, ev, k, rfl⟩
  | .tau next => .inr <| .inr ⟨next, rfl⟩
/- grind_pattern unfold_cases => it.unfold -/
-- NOTE: It might be enough with [grind cases] on `Obs`.

-- Maybe this can be defined later, once we have equality over unfoldings.
/- def recUnfold {motive : iTree E R → Prop} -/
/-   (onRet : (v : R) → motive (.ret v)) -/
/-   (onTau : (it iTree E R → -/

def ret.{s} (r : R) : iTree E R where
  curr : PUnit.{s+1}  := .unit
  step _ := .ret r

def vis.{s} {α : Type q} (ev : E α) (k : α → iTree.{_,_,_,s} E R) : iTree E R where
  curr : PUnit.{max q s +1} ⊕ (a : α) × (k a ).State := .inl .unit
  step
  | .inl .unit => .vis ev (fun a => .inr <| ⟨a, (k a).curr⟩)
  | .inr ⟨a, s⟩ => (k a).step s |>.mapState (.inr ⟨a, ·⟩)
  -- TODO: I could probably generalize this structure of
  -- "stay in inl until something, then inr always", and
  -- prove some generic lemmas about it, to reduce the proof
  -- burden.
  -- Would also be cool to state that "once a is chosen, it
  -- doesn't change"

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
variable {E : Type quest → Type resp}{R : Type ret}


/-

We define a weaker version of equality, observational

-/

-- TODO: Maybe it'd be cool to define it as a mutually recursive relation.
-- where we have relatiosn between Obs E R (iTree E R) and iTree E R defined
-- in terms of one another.
-- Might be useful for grind lemmas.

mutual
  -- Eqit (r : R → R → Prop) (l r : Bool) [i.e. eutt :0 Eqit (· = ·) true true]
  abbrev Rel (r : R → R → Prop) (it₁ it₂ : iTree E R)  : Prop := ObsRel r it₁.unfold it₂.unfold
  coinductive_fixpoint monotonicity by
    rintro Rel Rel' ⟨_, Obsimp⟩ it₁ it₂ H
    apply Obsimp
    assumption

  def ObsRel (r : R → R → Prop) : Obs E R (iTree E R) → Obs E R (iTree E R) → Prop
  | .ret v₁, .ret v₂ =>
      r v₁ v₂
  | .vis (A := A₁) ev₁ k₁, .vis (A := A₂) ev₂ k₂ =>
      ∃ (h : A₁ = A₂), ev₁ = h ▸ ev₂ ∧ ∀ s₁,
        Rel r (k₁ s₁) (k₂ (h ▸ s₁))
  | .tau it₁', .tau it₂' =>
      Rel r it₁' it₂'
  | _, _ => False
  coinductive_fixpoint monotonicity by
    rintro ⟨Rel, Obs⟩ ⟨Rel', Obs'⟩ ⟨Rimp, _⟩ obs₁ obs₂ H
    match h₁ : obs₁ with
    | .ret v₁ =>
        cases h₂ : obs₂ <;> grind
    | .vis (A := A₁) ev₁ k₁ =>
        match obs₂ with
        | .ret v₂ => grind
        | .tau it₂ => grind
        | .vis (A := A₂) ev₂ k₂ =>
          obtain ⟨h, rfl, ext⟩ := H
          simp only [Lean.Order.PartialOrder.rel, true_and, h, exists_true_left] at *
          intros; apply Rimp; apply ext
    | .tau it₁ =>
        match  obs₂ with
        | .ret v₂ => grind
        | .vis (A := A₂) ev₂ k₂ => grind
        | .tau it₂ =>
          apply Rimp
          assumption

end


--- lift (?). Maybe with `postFix`? ObsRelF? `eqitF` maybe
-- coinduction template
abbrev ObsRel.func (s : iTree E R → iTree E R → Prop) (r : R → R → Prop) : Obs E R (iTree E R) → Obs E R (iTree E R) → Prop
| .ret v₁, .ret v₂ =>
    r v₁ v₂
| .vis (A := A₁) ev₁ k₁, .vis (A := A₂) ev₂ k₂ =>
    ∃ (h : A₁ = A₂), ev₁ = h ▸ ev₂ ∧ ∀ s₁,
      s (k₁ s₁) (k₂ (h ▸ s₁))
| .tau it₁', .tau it₂' =>
    s it₁' it₂'
| _, _ => False

/- def ObsRel (r : R → R → Prop)(it₁ it₂ : iTree E R) : Prop := -/
/-   match it₁.unfold, it₂.unfold with -/
/-   | .ret v₁, .ret v₂ => -/
/-       r v₁ v₂ -/
/-   | .vis (A := A₁) ev₁ k₁, .vis (A := A₂) ev₂ k₂ => -/
/-       ∃ (h : A₁ = A₂), ev₁ = h ▸ ev₂ ∧ ∀ s₁, -/
/-         ObsRel r (k₁ s₁) (k₂ (h ▸ s₁)) -/
/-   | .tau it₁', .tau it₂' => -/
/-       ObsRel r it₁' it₂' -/
/-   | _, _ => False -/
/- coinductive_fixpoint monotonicity fun ObsRel ObsRel' Himp it₁ it₂ H => by -/
/-   dsimp at H ⊢ -/
/-   match h₁ :  it₁.unfold with -/
/-   | .ret v₁ => -/
/-       simp [h₁] at H ⊢ -/
/-       cases h₂ : it₂.unfold <;> grind -/
/-   | .vis (A := A₁) ev₁ k₁ => -/
/-       simp [h₁] at H ⊢ -/
/-       match h₂ : it₂.unfold with -/
/-       | .ret v₂ => grind -/
/-       | .tau it₂ => grind -/
/-       | .vis (A := A₂) ev₂ k₂ => -/
/-         simp [h₂] at H ⊢ -/
/-         obtain ⟨h, rfl, ext⟩ := H -/
/-         subst h -/
/-         simp -/
/-         intros -/
/-         apply Himp -/
/-         apply ext -/
/-   | .tau it₁ => -/
/-       simp [h₁] at H ⊢ -/
/-       match h₂ : it₂.unfold with -/
/-       | .ret v₂ => grind -/
/-       | .vis (A := A₂) ev₂ k₂ => grind -/
/-       | .tau it₂ => -/
/-         simp [h₂] at H ⊢ -/
/-         apply Himp -/
/-         assumption -/

abbrev ObsEq (it₁ it₂ : iTree E R) := Rel (· = ·) it₁ it₂

abbrev ObsEq.func s (obs₁ obs₂ : Obs E R (iTree E R)) := ObsRel.func s (·=·) obs₁ obs₂

instance {E : Type _ → Type _} : HasEquiv (iTree E R) where
  Equiv := ObsEq

/- @[grind →] -/
/- theorem ObsEq.cases (it₁ it₂ : iTree E R) : -/
/-     it₁ ≈ it₂ → -/
/-     (∃ v₁, it₁.unfold = .ret v₁) ∧ (∃ v₂, it₂.unfold = .ret v₂) ∨ -/
/-     (∃ (A₁ : Type) (ev₁ : E A₁) (k₁ : A₁ → iTree E R), it₁.unfold = .vis ev₁ k₁) ∧ -/
/-     (∃ (A₂ : Type) (ev₂ : E A₂) (k₂ : A₂ → iTree E R), it₂.unfold = .vis ev₂ k₂) ∨ -/
/-     (∃ it₁', it₁.unfold = .tau it₁') ∧ (∃ it₂', it₂.unfold = .tau it₂') := fun h => -/
/-   match h₁ : it₁.unfold, h₂ : it₂.unfold with -/
/-   | .ret v₁, .ret v₂ => by grind -/
/-   | .vis (A := A₁) ev₁ k₁, .vis (A := A₂) ev₂ k₂ => by grind -/
/-   | .tau it₁', .tau it₂' => by grind -/
/-   | .ret .., .tau .. -/
/-   | .ret .., .vis .. -/
/-   | .vis .., .ret .. -/
/-   | .vis .., .tau .. -/
/-   | .tau .., .vis .. -/
/-   | .tau .., .ret .. => by simp only [h₁, h₂, ObsRel] at h -/

@[grind →]
theorem ObsEq.obsEq_unfold_eq_ret {it₁ it₂ : iTree E R} :
    it₁.unfold = .ret v₁ →
    it₁ ≈ it₂ →
    ∃ v₂, it₂.unfold = .ret v₂ := fun h₁ h => by
  unfold Rel at h
  cases h₂ : it₂.unfold <;> simp [h₁, h₂, ObsRel] at h
  case ret v₂ => exists v₂

@[grind →]
theorem ObsEq.obsEq_unfold_eq_vis {it₁ it₂ : iTree E R} {ev₁ : E A₁} {k₁} :
    it₁.unfold = .vis ev₁ k₁ →
    it₁ ≈ it₂ →
    ∃ (A₂ : Type _) (ev₂ : E A₂) (k₂ : A₂ → iTree E R), it₂.unfold = .vis ev₂ k₂ := fun h₁ h => by
  unfold Rel at h
  cases h₂ : it₂.unfold <;> simp [h₁, h₂, ObsRel] at h
  case vis A₂ ev₂ k₂ => exists A₂, ev₂, k₂

@[grind →] -- Inversion lemmas (`_inv`)
theorem ObsEq.obsEq_unfold_eq_tau {it₁ it₂ it₁' : iTree E R} :
    it₁.unfold = .tau it₁' →
    it₁ ≈ it₂ →
    ∃ it₂', it₂.unfold = .tau it₂' := fun h₁ h => by
  unfold Rel at h
  cases h₂ : it₂.unfold <;> simp [h₁, h₂, ObsRel] at h
  case tau it₂ => exists it₂

theorem ObsEq.unfold_eq_ret {it₁ it₂ : iTree E R} {v₁ : R} {v₂ : R} :
    it₁.unfold = .ret v₁ →
    it₂.unfold = .ret v₂ →
    it₁ ≈ it₂ →
    v₁ = v₂ := fun h₁ h₂ h => by
  unfold Rel at h
  simpa [h₁, h₂, ObsRel] using h

theorem ObsEq.unfold_eq_vis {it₁ it₂ : iTree E R} {ev₁ : E A₁} {ev₂ : E A₂} {k₁ k₂} :
    it₁.unfold = .vis ev₁ k₁ →
    it₂.unfold = .vis ev₂ k₂ →
    it₁ ≈ it₂ →
    ∃ (h : A₁ = A₂), ev₁ = h ▸ ev₂ ∧ ∀ s₁,
      (k₁ s₁) ≈ (k₂ (h ▸ s₁)) := fun h₁ h₂ h => by
  unfold Rel at h
  simpa [h₁, h₂, ObsRel] using h

theorem ObsEq.unfold_eq_tau {it₁ it₂ it₁' : iTree E R} :
    it₁.unfold = .tau it₁' →
    it₂.unfold = .tau it₂' →
    it₁ ≈ it₂ →
    it₁' ≈ it₂' := fun h₁ h₂ h => by
  unfold Rel at h
  simpa [h₁, h₂, ObsRel] using h

@[grind =, grind =_]
theorem ObsRel.iff_rel {it₁ it₂ : iTree E R} :
    it₁ ≈ it₂ ↔ ObsRel (·=·) it₁.unfold it₂.unfold := by
  unfold Rel
  exact ⟨id, id⟩

#check Rel.coinduct
#print ObsRel.func

-- parametrized coinduction (what rocq-paco does, actually)
def ObsEq.coinductWith
  (pred : iTree E R → iTree E R → Prop)
  {it₁ it₂ : iTree E R}
  (baseCase : pred it₁ it₂)
  (progress :
    ∀ (it₁ it₂ : iTree E R),
      pred it₁ it₂ → ObsEq.func pred it₁.unfold it₂.unfold) :
    ObsEq it₁ it₂ := by
  apply Rel.coinduct (·=·) (pred_1 := pred) (pred_2 := ObsEq.func pred) _ _ _ _ baseCase
  all_goals grind only

@[refl]
theorem ObsEq.refl {it : iTree E R} : it ≈ it := by
  apply ObsEq.coinductWith (·=·) rfl
  grind only

 @[symm]
theorem ObsEq.symm {it₁ it₂ : iTree E R} : it₁ ≈ it₂ → it₂ ≈ it₁ := by
  intro h
  apply ObsEq.coinductWith (pred := fun x y => y ≈ x) h
  intros it₁ it₂ hyp
  match h₁ : it₁.unfold, h₂ : it₂.unfold with
  | Obs.ret _, Obs.ret _ =>
    grind [ObsEq.unfold_eq_ret]
  | Obs.vis (A := A₁) ev₁ k₁, Obs.vis (A := A₂) ev₂ k₂ =>
    grind [ObsEq.unfold_eq_vis]
  | Obs.tau it₁', Obs.tau it₂' =>
    grind [ObsEq.unfold_eq_tau]
  | .ret .., .tau ..
  | .ret .., .vis ..
  | .vis .., .ret ..
  | .vis .., .tau ..
  | .tau .., .vis ..
  | .tau .., .ret .. =>
    unfold Rel at hyp
    simp [h₁, h₂,  ObsRel] at hyp

theorem ObsEq.trans {it₁ it₂ it₃ : iTree E R} : it₁ ≈ it₂ → it₂ ≈ it₃ → it₁ ≈ it₃ := by
  intro it12 it23
  apply ObsEq.coinductWith (pred := fun x z => ∃ y, x ≈ y ∧ y ≈ z) ⟨it₂, it12, it23⟩
  rintro it₁ it₃ ⟨it₂, it12, it23⟩
  match h₁ : it₁.unfold, h₃ : it₃.unfold with
  | Obs.ret _, Obs.ret _ =>
    grind [ObsEq.unfold_eq_ret]
  | Obs.vis (A := A₁) ev₁ k₁, Obs.vis (A := A₃) ev₃ k₃ =>
    grind [ObsEq.unfold_eq_vis]
  | Obs.tau it₁', Obs.tau it₃' =>
    unfold func ObsRel.func
    have ⟨it₂', h₂⟩ := ObsEq.obsEq_unfold_eq_tau h₁ it12
    have it'12 := ObsEq.unfold_eq_tau h₁ h₂ it12
    have it'23 := ObsEq.unfold_eq_tau h₂ h₃ it23
    exists it₂'
  | .ret .., .tau ..
  | .ret .., .vis ..
  | .vis .., .ret ..
  | .vis .., .tau ..
  | .tau .., .vis ..
  | .tau .., .ret .. =>
    have oit12 := ObsRel.iff_rel.1 it12
    have oit23 := ObsRel.iff_rel.1 it23
    grind

instance : Std.Refl (@ObsEq E R) where refl _ := ObsEq.refl
instance : Std.Symm (@ObsEq E R) where symm _ _ := ObsEq.symm
instance : Trans (@ObsEq E R) (@ObsEq E R) (@ObsEq E R) where trans := ObsEq.trans

def ObsEq.step_tau_obsEq_self (it : iTree E R) (s : it.State) c :
    { {it with curr := c}.tau with curr := .inr s } ≈ {it with curr := s} := by
  apply ObsEq.coinductWith (fun
    (iTree.mk (State := State₁) curr₁ step₁)
    (iTree.mk (State := State₂) curr₂ step₂) =>
    ∃ (H : State₁ = (PUnit ⊕ State₂)),
    curr₁ = H.mpr (Sum.inr curr₂) ∧
    ∀ (s : State₂),
    step₁ (H ▸ (.inr s)) = H.symm ▸ (step₂ s).mapState .inr
  )
  case baseCase =>
    simp [tau, Obs.mapState]
  case progress =>
    unfold func ObsRel.func unfold
    rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨rfl, HC, Hs⟩
    cases _ : s₁ c₁ <;>
    cases _ : s₂ c₂ <;>
    simp [*, Obs.mapState]

def ObsEq.step_vis_obsEq_self (it : iTree E R) (ev : E A) (kS : A → it.State) (a : A) :
    { curr := kS a, step := it.step : iTree E R} ≈
    { curr : Unit ⊕ (_ : A) × it.State := Sum.inr ⟨a, kS a⟩,
        step := fun x =>
          match x with
          | Sum.inl PUnit.unit => Obs.vis ev fun a => Sum.inr ⟨a, kS a⟩
          | Sum.inr ⟨a, s⟩ => Obs.mapState (fun x => Sum.inr ⟨a, x⟩) (it.step s) } := by
  apply ObsEq.coinductWith (fun
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
    rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨h, HC, Hs⟩
    unfold ObsEq.func ObsRel.func unfold
    cases _ : s₁ c₁ <;>
    cases _ : s₂ c₂ <;>
    simp [*, Obs.mapState]
    all_goals (intros; exists h)

/- def ObsEq.step_vis_obsEq_self {E : Type _ → Type _}(ev : E A) (k : A → S) (a : A) (s : S) c : -/
    /- { iTree.vis ev (fun a => ⟨c, k a⟩) with curr := .inr ⟨a, s⟩ } ≈ {it with curr := s} := by -/
  /- apply ObsEq.coinductWith (fun -/
  /-   (iTree.mk (State := State₁) curr₁ step₁) -/
  /-   (iTree.mk (State := State₂) curr₂ step₂) => -/
  /-   ∃ (H : State₁ = (Unit ⊕ State₂)), -/
  /-   curr₁ = H.mpr (Sum.inr curr₂) ∧ -/
  /-   ∀ (s : State₂), -/
  /-   step₁ (H ▸ (.inr s)) = H.symm ▸ (step₂ s).mapState .inr -/
  /- ) -/
  /- case baseCase => -/
  /-   simp [tau, Obs.mapState] -/
  /- case progress => -/
  /-   unfold func ObsRel.func unfold -/
  /-   rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨rfl, HC, Hs⟩ -/
  /-   cases _ : s₁ c₁ <;> -/
  /-   cases _ : s₂ c₂ <;> -/
  /-   simp [*, Obs.mapState] -/

theorem ObsEq.tau_congr {it₁ it₂ : iTree E R} : it₁ ≈ it₂ → (iTree.tau it₁) ≈ (iTree.tau it₂) := by
  intro h
  unfold Rel
  simp [unfold, tau, ObsRel]
  change ({ it₁.tau with curr := .inr it₁.curr } ≈ { it₂.tau with curr := .inr it₂.curr })
  calc { it₁.tau with curr := .inr it₁.curr }
    _ ≈ (it₁ : iTree E R) := step_tau_obsEq_self ..
    _ ≈ it₂ := h
    _ ≈ { it₂.tau with curr := .inr it₂.curr } := (step_tau_obsEq_self ..).symm

theorem ObsEq.obsEq_ret_of_unfold_ret {it : iTree E R} {v : R} : it.unfold = .ret v → it ≈ .ret v := by
  simp [unfold]
  cases h : it.step it.curr <;> simp
  rintro rfl
  unfold Rel ObsRel unfold
  simp [h, ret]

theorem ObsEq.obsEq_tau_of_unfold_tau {it it': iTree E R} : it.unfold = .tau it' → it ≈ .tau it' := by
  simp [unfold]
  cases h : it.step it.curr <;> simp
  case tau st =>
    rintro rfl
    unfold Rel ObsRel unfold
    have := step_tau_obsEq_self it st st |>.symm
    simpa [tau, h]

theorem ObsEq.obsEq_tau_of_obsEq_unfold_tau {it it'₁ it'₂ : iTree E R} :
    it.unfold = .tau it'₁ →
    it'₁ ≈ it'₂ →
    it ≈ .tau it'₂ := by
  simp [unfold]
  cases h : it.step it.curr <;> simp
  case tau st =>
  rintro rfl heq
  have := ObsEq.tau_congr heq
  refine ObsEq.trans ?_ this
  unfold Rel ObsRel unfold
  simpa [*, tau] using ObsEq.step_tau_obsEq_self it st st |>.symm

theorem ObsEq.obsEq_vis_of_unfold_vis {it : iTree E R}{ev : E A} {k}: it.unfold = .vis ev k → it ≈ .vis ev k := by
  simp [unfold]
  cases h : it.step it.curr <;> simp
  case vis A ev kS =>
    rintro rfl rfl rfl
    unfold Rel ObsRel unfold
    simp [vis, h]
    intros a
    /- have := ObsEq.step_vis_obsEq_self it ev kS a -/
    /- dsimp [HasEquiv.Equiv, instHasEquiv, ObsEq] at this -/
    /- assumption -/
    -- TODO: Idk why I can't conclude with the previous, so I just copy-paste the proof
    -- of `ObsEq.step_vis_obsEq_self`
    apply ObsEq.coinductWith (fun
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
      rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨h, HC, Hs⟩
      unfold ObsEq.func ObsRel.func unfold
      cases _ : s₁ c₁ <;>
      cases _ : s₂ c₂ <;>
      simp [*, Obs.mapState]
      all_goals (intros; exists h)

theorem ObsEq.unfold_vis (ev : E A) (k : A → iTree E R) :
    ObsRel (·=·) (iTree.vis ev k).unfold (Obs.vis ev k) := by
  simp [unfold, iTree.vis, ObsRel]
  intro a
  apply ObsEq.coinductWith (fun
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
    simp [Obs.mapState]
  case progress =>
    rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨h, HC, Hs⟩-- ⟨h, HC, Hs⟩
    unfold ObsEq.func ObsRel.func unfold
    cases h₁ : s₁ c₁ <;>
    cases h₂ : s₂ c₂ <;>
    simp [*, Obs.mapState]
    all_goals (intros; exists h)


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
  refl  := Std.Refl.refl
  symm  := Std.Symm.symm _ _
  trans := Trans.trans

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
    intros it₁ it₂ heq
    match h₁ : it₁.unfold, h₂ : it₂.unfold with
    | Obs.ret _, Obs.ret _ =>
      simp [h₁, h₂]
      grind only [ObsEq.unfold_eq_ret]
    | Obs.vis (A := A₁) ev₁ k₁, Obs.vis (A := A₂) ev₂ k₂ =>
      simp [*, Obs.mapState]
      obtain ⟨rfl, rfl, ih⟩:= ObsEq.unfold_eq_vis h₁ h₂ heq
      simp only [heq_eq_eq, true_and]
      ext
      apply Quotient.sound
      apply ih
    | Obs.tau it₁', Obs.tau it₃' =>
      simp [*, Obs.mapState]
      apply Quotient.sound
      apply ObsEq.unfold_eq_tau h₁ h₂ heq
    | .ret .., .tau ..
    | .ret .., .vis ..
    | .vis .., .ret ..
    | .vis .., .tau ..
    | .tau .., .vis ..
    | .tau .., .ret .. =>
      grind)

def out (it' : iTree' E R) : iTree E R where
    curr := it'
    step := iTree'.unfold

theorem unfold_out (it' : iTree' E R) :
    ObsRel (·=·) (it'.unfold.mapState (·.out)) (it'.out.unfold) :=
  -- Basically, we can unfold either in the quotient our outside of it
    sorry
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
  simp [tau, Quotient.lift, Quotient.mk]
  apply Quotient.sound
  simp [unfold, Quotient.lift, Quotient.mk, Obs.mapState] at h
  cases h₂ : it.unfold <;> simp [h₂] at h
  case a.tau it₂ =>
    have h := Quotient.exact h
    apply ObsEq.obsEq_tau_of_obsEq_unfold_tau h₂ h

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



def vis {A : Type a} {R : Type _}{E : Type a → Type _} (ev : E A) (k' : A → iTree' E R) : iTree' E R :=
  (Quotient.bubbleUp k').lift (.mk <| iTree.vis ev ·) (
    fun k₁ k₂ k₁k₂ =>
    Quotient.sound <| by
    change ObsEq (iTree.vis ev k₁) (iTree.vis ev k₂)
    unfold ObsEq Rel
    have h₁ := ObsEq.unfold_vis ev k₁
    have h₂ := ObsEq.unfold_vis ev k₂
    have : ObsRel (·=·) (Obs.vis ev k₁) (Obs.vis ev k₂) := by
      unfold ObsRel
      exists rfl
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

export SecondTry (eq wb wb.ret wb.vis wb.tauL wb.tauR wb.sync)

end EqualitiesOverITrees

@[simp, grind]
instance : HasEquiv (iTree E R) where Equiv := SecondTry.eq

-- This definition doesn't satisfy the monad laws up to equality, but it does
-- follow then up to tau equality.

/- theorem bindLeft_ret : it.unfold = .ret v → bindLeft f it = sorry := by -/
/-   intros h -/
/-   unfold bindLeft -/
/-   sorry -/


theorem id_map {α : Type} (it : iTree E α) : bindLeft pure it ≈ it := by
  dsimp [HasEquiv.Equiv]
  unfold eq
  match h : it.unfold with
  | .ret v₁ =>
    cases h₂ : it.step it.curr <;> (try simp [h₂, unfold] at h; done)
    apply wb.tauL ?_ ?unfold ?next
    case unfold =>
      simp [unfold, bindLeft, h₂, Obs.bindVal, Obs.mapState]
      rfl
    apply wb.ret v₁ _ h
    simp [unfold, pure, ret]
    simp [unfold, h₂] at h
    assumption
  | .vis ev₁ k₁ =>
    cases h₂ : it.step it.curr <;> (try simp [h₂, unfold] at h; done)
    case vis A ev₁ k₁ =>
    /- have := h -/
    simp [h₂, unfold] at h
    have ⟨rfl, h⟩ := h
    simp at h
    have ⟨h, h'⟩:= h
    subst h h'
    simp [bindLeft,  Obs.bindVal, Obs.mapState]
    apply wb.vis ev₁ _ ev₁ _ ?left ?right
    case left =>
      simp [unfold, h₂, pure, ret]
      sorry
    all_goals sorry
  | .tau it₁ =>
    sorry

instance  : LawfulMonad (iTree E) := .mk'
   (id_map     := by
      simp only [Functor.map, bind, Pure.pure, Function.comp_id]
      intros α it
      have {State, curr, step} := it
      simp [bindLeft, *]
      sorry
      /- induction it <;> simp [bindLeft, *] -/
    )
   (pure_bind  := by intros α β it f; simp only [bind, bindLeft])
   (bind_assoc := by intros α β γ it f g; simp only [bind]; induction it <;> simp [bindLeft, *])

end iTree

end StateMachine
