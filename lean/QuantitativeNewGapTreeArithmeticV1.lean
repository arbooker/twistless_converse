module

public import AsymptoticLocalOldGroupsV1
public import AsymptoticFrickeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticLocalCongruence
open AsymptoticFreshMatrices
open scoped MatrixGroups

/-- Two determinant-one representatives of the same projective element
have equal entries up to sign. This retains the congruence information
that mere integrality of the rational representative would lose. -/
theorem projective_det_one_entry_eq_or_neg (R : GL (Fin 2) ℚ)
    (hR : R.val.det = 1) (A : SL(2, ℤ))
    (he : rationalMap R = rationalMap (rationalGL A)) (i j : Fin 2) :
    R.val i j = (A.val i j : ℚ) ∨ R.val i j = -(A.val i j : ℚ) := by
  change ProjGenLinGroup.mk (realMatrix R) =
    ProjGenLinGroup.mk (realMatrix (rationalGL A)) at he
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  have hR' : (realMatrix R).val.det = 1 := by
    change (R.val.map (fun r : ℚ => (r : ℝ))).det = 1
    rw [← Rat.cast_det, hR, Rat.cast_one]
  have hA' : (realMatrix (rationalGL A)).val.det = 1 := by
    change (A.val.map (fun a : ℤ => (a : ℝ))).det = 1
    rw [← Int.cast_det, A.property, Int.cast_one]
  have hd := congrArg (fun B : GL (Fin 2) ℝ => B.val.det) hu
  change ((realMatrix R).val * (GeneralLinearGroup.scalar (Fin 2) u).val).det = _ at hd
  rw [Matrix.det_mul, hR', one_mul] at hd
  have hu2 : (u : ℝ)^2 = 1 := by
    simpa [GeneralLinearGroup.scalar, Matrix.scalar, Matrix.det_fin_two, hA'] using hd
  have hij := congrArg (fun B : GL (Fin 2) ℝ => B.val i j) hu
  change ((realMatrix R).val * (GeneralLinearGroup.scalar (Fin 2) u).val) i j =
    (A.val i j : ℝ) at hij
  have hij' : (R.val i j : ℝ) * (u : ℝ) = (A.val i j : ℝ) := by
    simpa [realMatrix, GeneralLinearGroup.map, GeneralLinearGroup.scalar,
      Matrix.scalar, Matrix.mul_diagonal] using hij
  rcases sq_eq_one_iff.mp hu2 with h | h
  · left
    rw [h, mul_one] at hij'
    exact_mod_cast hij'
  · right
    rw [h, mul_neg_one] at hij'
    have hh : (R.val i j : ℝ) = -(A.val i j : ℝ) := by linarith
    exact_mod_cast hh

/-- The literal two old overgroups meet in exactly the raised congruence
level. Valid for every positive dilation factor, without primality. -/
theorem gamma_inf_degeneracyGroup (M p : ℕ) (hM : 0 < M) (hp : 0 < p) :
    gamma M ⊓ degeneracyGroup M p hp = gamma (p*M) := by
  apply le_antisymm
  · rintro g ⟨⟨A, hA, rfl⟩, hK⟩
    obtain ⟨b, ⟨B, hB, rfl⟩, he⟩ := hK
    have hlabel : rationalSLLabel (dilationConjugateSL p hp B) = integralLabel A := by
      rw [dilationConjugateSL_label]
      change (dilationLabel p hp)⁻¹ * integralLabel B * ((dilationLabel p hp)⁻¹)⁻¹ = _ at he
      simpa only [inv_inv] using he
    have hproj : rationalMap (SpecialLinearGroup.toGL (dilationConjugateSL p hp B)) =
        rationalMap (rationalGL A) :=
      congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) hlabel
    have hl := projective_det_one_entry_eq_or_neg
      (SpecialLinearGroup.toGL (dilationConjugateSL p hp B))
      (dilationConjugateSL p hp B).property A hproj 1 0
    change (p : ℚ) * (B.val 1 0 : ℚ) = (A.val 1 0 : ℚ) ∨
      (p : ℚ) * (B.val 1 0 : ℚ) = -(A.val 1 0 : ℚ) at hl
    rw [integralLabel_mem_gamma_iff, gamma0_mem_dvd]
    obtain ⟨c, hc⟩ := (gamma0_mem_dvd M B).mp hB
    rcases hl with hl | hl
    · have hz : (p : ℤ) * B.val 1 0 = A.val 1 0 := by exact_mod_cast hl
      refine ⟨c, ?_⟩
      rw [← hz, hc, Nat.cast_mul]
      ring
    · have hz : (p : ℤ) * B.val 1 0 = -A.val 1 0 := by exact_mod_cast hl
      refine ⟨-c, ?_⟩
      rw [Nat.cast_mul]
      rw [hc] at hz
      nlinarith
  · exact le_inf (gamma_le_of_dvd (Nat.dvd_mul_left M p))
      (gamma_le_degeneracyGroup M p hM hp)

#print axioms projective_det_one_entry_eq_or_neg
#print axioms gamma_inf_degeneracyGroup

end QuantitativeNewGap
