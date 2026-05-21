/-
  In the following section, we use an unsafe computable implementation of
  `Quotient.choice` to be able to define `Quotient.bubbleUp`. I believe
  that this implementation is safe, since the unsafe operation happens
  inside the creation of another quotient, and therefore cannot be
  exploited. This claim has not been checked.
-/

-- Taken from Mathlib
instance piSetoid {ι : Sort _} {α : ι → Sort _} [∀ i, Setoid (α i)] : Setoid (∀ i, α i) where
  r a b := ∀ i, a i ≈ b i
  iseqv := ⟨fun _ _ ↦ Setoid.refl _,
            fun h _ ↦ Setoid.symm (h _),
            fun h₁ h₂ _ ↦ Setoid.trans (h₁ _) (h₂ _)⟩

-- Taken from Mathlib
unsafe def Quot.unquot {r : α → α → Prop} : Quot r → α :=
  cast lcProof

-- Taken from Mathlib
noncomputable def Quot.out {r : α → α → Prop} (q : Quot r) : α :=
  Classical.choose (Quot.exists_rep q)

-- Taken from Mathlib
@[simp]
theorem Quot.out_eq {r : α → α → Prop} (q : Quot r) :
    Quot.mk r q.out = q :=
  Classical.choose_spec (Quot.exists_rep q)

-- Taken from Mathlib
noncomputable def Quotient.choice {ι : Type _} {α : ι → Type _} {S : ∀ i, Setoid (α i)}
  (f : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) (by infer_instance) :=
  .mk _ <| fun i ↦ (f i).out

unsafe
def Quotient.bubbleUpUnsafe {X A : Type _}{s : Setoid X}(f : A → Quotient s) : Quotient (piSetoid : Setoid (A → X)) :=
  .mk _ <| fun i ↦ (f i).unquot

@[implemented_by Quotient.bubbleUpUnsafe]
def Dubious.Quotient.bubbleUp{X A : Type _}{s : Setoid X}(f : A → Quotient s) :
    Quotient (piSetoid : Setoid (A → X)) :=
  Quotient.choice (ι := A) (α := λ_↦X) (S := λ_↦s) f

-- THAT WAS A REALLY BAD IDEA! (credit: Aaron Liu)

/-- Always-true relation as a `Setoid`.

Note that in later files the preferred spelling is `⊤ : Setoid α`. -/
@[implicit_reducible]
def trueSetoid : Setoid α :=
  ⟨_, equivalence_true α⟩

/-- `Trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `Nonempty α`, but unlike `Nonempty α`, `Trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
def Trunc.{u} (α : Sort u) : Sort u :=
  @Quotient α trueSetoid

namespace Trunc

def mk {α : Sort u}(a : α) : Trunc α := Quotient.mk trueSetoid a

instance [Inhabited α] : Inhabited (Trunc α) :=
  ⟨.mk default⟩

@[elab_as_elim]
protected theorem induction_on {β : Trunc α → Prop} (q : Trunc α) (h : ∀ a, β (mk a)) : β q :=
  Quot.ind h q

@[elab_as_elim]
protected theorem induction_on₂ {C : Trunc α → Trunc β → Prop} (q₁ : Trunc α) (q₂ : Trunc β)
    (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
  Trunc.induction_on q₁ fun a₁ ↦ Trunc.induction_on q₂ (h a₁)

protected theorem eq (a b : Trunc α) : a = b :=
  Trunc.induction_on₂ a b fun _ _ ↦ Quot.sound trivial

instance instSubsingletonTrunc : Subsingleton (Trunc α) :=
  ⟨Trunc.eq⟩

end Trunc

def Dubious.badDecidableTrue : Decidable True :=
  -- we use `Quotient.recOnSubsingleton` to bypass
  -- the `Quotient.mk` that's protecting `Quotient.unquot`
  Quotient.recOnSubsingleton (Quotient.bubbleUp (@id (Trunc Bool))) fun f => by
    -- `f : Trunc Bool → Bool` was obtained by lifting `id : Trunc Bool → Trunc Bool`
    -- its implementation is `Quotient.unquot`,
    -- so it should distinguish between `Trunc.mk true` and `Trunc.mk false`
    -- of course, any normal function would not distinguish these
    apply decidable_of_iff (a := f (.mk true) = f (.mk false))
    apply iff_true_intro
    apply congrArg
    apply Subsingleton.elim _ _

-- `True` is false!
#eval @decide True Dubious.badDecidableTrue

set_option pp.proofs true in
#print Quot.recOnSubsingleton
#print Quot.recOnSubsingleton._proof_1

def recOnSubsingleton'
  {α : Sort _}
  {s : Setoid α}
  {motive : Quotient s → Sort v}
  [h : (a : α) → Subsingleton (motive (Quotient.mk s a))]
  (q : Quotient s)
  (f : (a : α) → motive (Quotient.mk s a)) :
    motive q :=
  Quot.rec f (fun _ _ _ => Subsingleton.elim _ (f _)) q


@[implemented_by Quot.unquot]
def Quot.UNSAFE_unquot {r : α → α → Prop} (q : Quot r) : α := q.out
