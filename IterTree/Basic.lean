namespace IterTree

---------------------------

structure IterM {α : Type w} (m : Type w → Type w') (β : Type w) where
  internalState : α

inductive IterStep (α β) where
  | yield : (it : α) → (out : β) → IterStep α β
  | skip : (it : α) → IterStep α β
  | done : IterStep α β

class Iterator (α : Type w) (m : Type w → Type w') (β : outParam (Type w)) where
  IsPlausibleStep : IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop
  step : (it : IterM (α := α) m β) → m (Subtype <| IsPlausibleStep it)
#check Std.Iterator

---------------------------

#check ULift

#print Std.IterM
structure iTree {σ : Type σ} («?» : Type r → Type q) (m : Type m₁ → Type m₂) : Type σ where
  internalState : σ

-- NOTE: We have that ι = σ

#print Std.IterStep
inductive Observation' (ι : Type ι)(«?» : Type r → Type q) where
  | ask {α : Type r} (ev : «?» α)(it : α → ι)
--                          ↑↑↑↑↑ q     ↑↑↑↑↑ (r ⇒ ι) = max r ι
  | skip (it : ι)
  | done

-- NOTE: It makes ense to require r = ι

inductive Observation (ι : Type ι)(«?» : Type ι → Type q) : Type (max (ι+1) q) where
  | ask {α : Type ι} (ev : «?» α)(it : α → ι)
-- The problem with universes occurs here, in the ask function, since you may be asked for
-- an element of some type, for the same universe as our iterators
  | skip (it : ι)
  | done

#print Std.Iterator
class Exec' (σ : Type σ)(«?» : Type σ → Type q)(m : Type (max (σ+1) q) → Type (max (σ+1) q)) 
where
  IsPlausibleObservation : iTree (σ := σ) «?» m → Observation (iTree (σ := σ) «?» m) «?» → Prop
  exec : (it : iTree (σ := σ) «?» m) →
    m {obs : Observation (iTree (σ := σ) «?» m) «?» // IsPlausibleObservation it obs}


