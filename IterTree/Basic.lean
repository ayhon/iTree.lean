namespace IterTree

/-- iTree equivalent of Std.IterM -/
structure iTree {σ : Type σ} («?» : Type r → Type q) (ρ : Type ρ) :
    Type σ where
  /-- I'm becoming more and more certian that this `iTree` definition
  can be understood as a mapping between some program σ and both its
  return type ρ and effects «?». These effects may depend on some type.-/
  internalState : σ

/-
The issue I see with our current API is that the internal program type is
represented in our iTree interface, since its part of its type signature.
This prevents us from having `iTree` have a nice monoidal interface, since
an operation may transform the type of the internal state σ.

For instance, we would like to implement the `return` combinator in our
implementation, but this is represented by taking a new type `Return`,
which can then be used by the typeclass resolution system to decide what
the `exec` method is for our combinator. In a sense, we're defining a new
instruction and giving its operational semantics through the `exec` method.
-/

-- NOTE: We have that ι = σ

/-- iTree equivalent of Std.IterStep 

These are the observable behaviours of an iTree of effects «?» and values ρ.
We can also think about it as the possible ways to express the operational
semantics of our program. It's either taking a step (given by `skip`), 
producing a value (given by `done`), or asking for an interaction before it
can proceed (given by `ask`). Or, in other words, executing some effect.
-/
inductive Observation («?» : Type ι → Type q) (ρ : Type ρ) : Type _ where
  | ask {α : Type ι}{σ : Type ι → Type ι} (ev : «?» α) (k : α → @iTree (σ α) «?» ρ) 
  -- For now I allow our programs to depend on the type of events. 
  | skip {σ : Type ι}(it : @iTree σ «?» ρ) 
  | done (v : ρ) 

/-- iTree equivalent of Std.Iterator 

It links implementations σ with iTrees of effects «?» and values ρ.
-/
class Executable (σ : Type ι)
  («?» : Type σ → Type q)
  (ρ : Type ρ)
where
  IsPlausibleObservation : iTree (σ := σ) «?» ρ → Observation «?» ρ → Prop
  exec : (it : iTree (σ := σ) «?» ρ) →
    {obs : Observation «?» ρ // IsPlausibleObservation it obs}
