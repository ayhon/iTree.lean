namespace IterTree

/-- iTree equivalent of Std.IterM -/
structure iTree {σ : Type σ} («?» : Type r → Type q) (m : Type m₁ → Type m₂) : Type σ where
  internalState : σ

-- NOTE: We have that ι = σ

/-- iTree equivalent of Std.IterStep -/
inductive Observation (ι : Type ι)(«?» : Type ι → Type q) : Type (max (ι+1) q) where
  | ask {α : Type ι} (ev : «?» α) (it : α → ι) : Observation ι «?»
  | skip (it : ι) : Observation ι «?»
  | done : Observation ι «?»

/-- iTree equivalent of Std.Iterator -/
class Executable (σ : Type σ)
  («?» : Type σ → Type q)
  (m : Type (max (σ+1) q) → Type (max (σ+1) q)) 
where
  IsPlausibleObservation : iTree (σ := σ) «?» m → Observation (iTree (σ := σ) «?» m) «?» → Prop
  exec : (it : iTree (σ := σ) «?» m) →
    m {obs : Observation (iTree (σ := σ) «?» m) «?» // IsPlausibleObservation it obs}
