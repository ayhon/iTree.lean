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


inductive Obs (E : Type q → Type r) (R : Type v) (K : Type k) where
| ret : R → Obs E R K
| tau : K → Obs E R K
| vis {A : Type q} : E A → (A → K) → Obs E R K

/- class IsITreeImpl (State : Type s) (E : Type q → Type r) (R : Type v) where -/
/-     step : State → Obs E R State -/

structure iTree (E : Type q → Type r) (R : Type v) where
  {State : Type s}
  curr : State
  /- [stepImpl : IsITreeImpl State E R] -/
  step : State → Obs E R (iTree E R)
  -- Why not have it give observations on just `State`?
  -- I think it's not possible, because we must be able to change
  -- the state type at some point in the execution.
  -- 
  -- However, how do you define the infinitely looping
  -- computation with `State → Obs E R (iTree E R)`?
  -- You can't, you'd need to reference back to the think you're
  -- defining, but at that point it's no longer a fixpoint!

instance : Inhabited (iTree E R) where
  default := {
    State := Unit
    curr := ()
    step := fun _ => .tau 
  }

variable {E : Type q → Type r}{R : Type v}
  

def iTree.unfold (it : iTree E R) : Obs E R (iTree E R) := it.step it.curr 

/-

An alternate representation of this interface would be to have `curr : State` be the implementation of
an `iTree E R`, and assign to each `State` type a particular `step` function.

-/

namespace iTree

variable {E : Type q → Type r}

/- instance : Inhabited ({E : Type q → Type r} → {α : Type u_1} → {β : Type u_2} → (α → iTree E β) → iTree E α → iTree E β) where -/
/-   default f it := { -/
    
/-   } -/

/--
  After the computation of the interaction tree `it`, we simply continue with the
  computation given by `f`. We encode the information of the continuation in the 
  closure, to dodge problems with termination.
-/
partial
def bindLeft {α β} (f : α → iTree E β)(it : iTree E α) : iTree E β :=
  {
    State := it.State
    curr := it.curr
    step st := match it.step st with
      | .ret r => .tau (f r)
      | .tau it => .tau (it.bindLeft f)
      | .vis ev k => 
        .vis ev (fun a => (k a).bindLeft f)
  }

/- instance : Bind (iTree E) := ⟨(·.bindLeft ·)⟩ -/
/- instance : Pure (iTree E) := ⟨.ret⟩ -/
/- instance : Monad (iTree E) where -/
/- instance  : LawfulMonad (iTree E) := .mk' -/
/-    (id_map     := by intros α it; simp only [Functor.map, bind, pure, Function.comp_id]; induction it <;> simp [bindLeft, *] ) -/
/-    (pure_bind  := by intros α β it f; simp only [bind, bindLeft]) -/
/-    (bind_assoc := by intros α β γ it f g; simp only [bind]; induction it <;> simp [bindLeft, *]) -/

end iTree

end StateMachine
