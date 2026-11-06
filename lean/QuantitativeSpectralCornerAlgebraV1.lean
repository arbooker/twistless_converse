module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Idempotents

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralCornerAlgebra

variable {A : Type*} [CStarAlgebra A] (p : A)

/-- The concrete two-sided corner, with the ambient operations and norm. -/
@[nolint unusedArguments]
def cornerSubalgebra (_hi : IsIdempotentElem p) (hp : IsSelfAdjoint p) : NonUnitalStarSubalgebra ℂ A where
  __ := NonUnitalRing.corner p
  smul_mem' c a ha := by
    obtain ⟨b, rfl⟩ := ha
    exact ⟨c • b, by simp⟩
  star_mem' {a} ha := by
    obtain ⟨b, rfl⟩ := ha
    exact ⟨star b, by simp [star_mul, hp.star_eq, mul_assoc]⟩

theorem corner_isClosed (hi : IsIdempotentElem p) (hp : IsSelfAdjoint p) :
    IsClosed (cornerSubalgebra p hi hp : Set A) := by
  have he : (cornerSubalgebra p hi hp : Set A) = {a | p*a=a ∧ a*p=a} := by
    ext a
    exact Subsemigroup.mem_corner_iff hi
  rw [he]
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

noncomputable instance cornerComplete (hi : IsIdempotentElem p) (hp : IsSelfAdjoint p) :
    CompleteSpace (cornerSubalgebra p hi hp) := (corner_isClosed p hi hp).completeSpace_coe

noncomputable instance cornerNonUnitalCStar (hi : IsIdempotentElem p)
    (hp : IsSelfAdjoint p) : NonUnitalCStarAlgebra (cornerSubalgebra p hi hp) := by
  letI := cornerComplete p hi hp
  exact {
    norm_mul_self_le := fun x => (CStarRing.norm_star_mul_self (x := (x : A))).symm.le }

noncomputable instance cornerRing (hi : IsIdempotentElem p) (hp : IsSelfAdjoint p) :
    Ring (cornerSubalgebra p hi hp) := inferInstanceAs (Ring hi.Corner)

noncomputable instance cornerNormedRing (hi : IsIdempotentElem p) (hp : IsSelfAdjoint p) :
    NormedRing (cornerSubalgebra p hi hp) := by
  letI := cornerRing p hi hp
  letI := cornerNonUnitalCStar p hi hp
  exact { toRing := cornerRing p hi hp, dist_eq := dist_eq_norm_neg_add, norm_mul_le := norm_mul_le }

noncomputable instance cornerAlgebra (hi : IsIdempotentElem p) (hp : IsSelfAdjoint p) :
    Algebra ℂ (cornerSubalgebra p hi hp) := by
  letI := cornerRing p hi hp
  exact Algebra.ofModule smul_mul_assoc mul_smul_comm

noncomputable instance cornerCStar (hi : IsIdempotentElem p) (hp : IsSelfAdjoint p) :
    CStarAlgebra (cornerSubalgebra p hi hp) := by
  letI := cornerNonUnitalCStar p hi hp
  letI := cornerNormedRing p hi hp
  letI := cornerAlgebra p hi hp
  exact { toNormedRing := cornerNormedRing p hi hp
          toStarRing := inferInstance
          toCompleteSpace := cornerComplete p hi hp
          toCStarRing := inferInstance
          toNormedAlgebra := { toAlgebra := cornerAlgebra p hi hp, norm_smul_le := norm_smul_le }
          toStarModule := inferInstance }

#print axioms cornerCStar

end QuantitativeSpectralCornerAlgebra
