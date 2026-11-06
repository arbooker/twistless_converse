module

public import AsymptoticClassicalOldIntersectionGroupsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane ConjAct AsymptoticCongruenceStrip AsymptoticClassicalCosets
open scoped ModularForm Pointwise

/-- Honest matrix and projective congruence groups have the same relative index. -/
theorem level_relIndex (N M : ℕ) :
    (level N).relIndex (level M) = (gamma N).relIndex (gamma M) :=
  Nat.card_congr (traceEquiv N M)

/-- The index of the Fricke old group agrees with the ordinary lower-level index. -/
theorem frickeOldLevel_relIndex (N M : ℕ) (hN : 0 < N) :
    (level N).relIndex (frickeOldLevel N M hN) = (level N).relIndex (level M) := by
  change (level N).relIndex ((level M).map (MulAut.conj (frickeReal N hN)).toMonoidHom) = _
  have he : (level N).map (MulAut.conj (frickeReal N hN)).toMonoidHom = level N :=
    frickeOldLevel_self N hN
  conv_lhs => rw [← he]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (frickeReal N hN)).injective

/-- Dilation preserves relative indices among its translated levels. -/
theorem dilationLevel_relIndex (M L p : ℕ) (hp : 0 < p) :
    (dilationLevel M p hp).relIndex (dilationLevel L p hp) =
      (level M).relIndex (level L) :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (dilationReal p hp)⁻¹).injective

/-- The ordinary old direction has the same index in the common translated
 overgroup as its lower level has in the two-step lower level. -/
theorem lower_dilationLevel_index (L p : ℕ) (hL : 0 < L) (hp : 0 < p) :
    (level (p * L)).relIndex (dilationLevel L p hp) =
      (level (p * L)).relIndex (level L) := by
  have hpL := Nat.mul_pos hp hL
  have hi : (level (p * (p * L))).relIndex (level (p * L)) = p := by
    rw [level_relIndex]
    exact AsymptoticRamifiedCosets.projective_index (p * L) p hpL hp (Nat.dvd_mul_right p L)
  have hi' : (level (p * (p * L))).relIndex (dilationLevel (p * L) p hp) = p := by
    rw [← frickeOldLevel_eq_dilationLevel (p * L) p hpL hp, frickeOldLevel_relIndex, hi]
  have hfirst := Subgroup.relIndex_mul_relIndex
    (level (p * (p * L))) (dilationLevel (p * L) p hp) (dilationLevel L p hp)
    (level_le_dilation_conjugate (p * L) p hp)
    (dilationLevel_mono hp (Nat.dvd_mul_left L p))
  have hsecond := Subgroup.relIndex_mul_relIndex
    (level (p * (p * L))) (level (p * L)) (dilationLevel L p hp)
    (level_antitone (Nat.dvd_mul_left (p * L) p))
    (level_le_dilation_conjugate L p hp)
  rw [hi', dilationLevel_relIndex] at hfirst
  rw [hi] at hsecond
  exact Nat.eq_of_mul_eq_mul_left hp (hsecond.trans hfirst.symm)

#print axioms level_relIndex
#print axioms frickeOldLevel_relIndex
#print axioms dilationLevel_relIndex
#print axioms lower_dilationLevel_index

end AsymptoticClassicalCusp
