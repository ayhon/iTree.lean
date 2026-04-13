namespace IterTree

/-- iTree equivalent of Std.IterM -/
structure iTree {σ : Type σ} («?» : Type r → Type q) (ν : Type ν) :
    Type σ where
  internalState : σ

-- NOTE: We have that ι = σ

/-- iTree equivalent of Std.IterStep -/
inductive Observation (ι : Type ι)(«?» : Type ι → Type q) (ν : Type ν) : Type _ where
  | ask {α : Type ι} (ev : «?» α) (it : α → ι) : Observation ι «?» ν
  | skip (it : ι) : Observation ι «?» ν
  | done (v : ν) : Observation ι «?» ν

/-- iTree equivalent of Std.Iterator -/
class Executable (σ : Type σ)
  («?» : Type σ → Type q)
  (ν : Type ν)
where
  IsPlausibleObservation : iTree (σ := σ) «?» ν → Observation (iTree (σ := σ) «?» ν) «?» ν → Prop
  exec : (it : iTree (σ := σ) «?» ν) →
    {obs : Observation (iTree (σ := σ) «?» ν) «?» ν // IsPlausibleObservation it obs}
