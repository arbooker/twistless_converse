module

public import QuantitativeEulerOldProjectionHolomorphicCosetsV1
public import QuantitativeEulerOldProjectionCocycleV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionHolomorphic

open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalPetersson
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups

/-- At even weight the positive Petersson multiplier is exactly y^m. -/
theorem weighted_even (m : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    weighted ((2*m : ℕ) : ℤ) f z = (z.im : ℂ)^m * f z := by
  unfold weighted
  rw [zpow_natCast, show 2*m=m*2 by omega, pow_mul,
    Real.sqrt_sq (pow_nonneg z.im_pos.le m), Complex.ofReal_pow]

/-- The phase-corrected weighted slash agrees with the literal classical
slash for determinant-one matrices. -/
theorem weighted_slash_det_one (g : GL (Fin 2) ℝ) (hg : g.det.val = 1)
    (m : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    AsymptoticHyperbolicSlash.phase g (2*m) z * weighted ((2*m : ℕ) : ℤ) f (g • z) =
      weighted ((2*m : ℕ) : ℤ) (f ∣[((2*m : ℕ) : ℤ)] g) z := by
  rw [weighted_even, weighted_even, ← mul_assoc,
    AsymptoticHyperbolicSlash.normalized_slash g (by rw [hg]; exact zero_lt_one)]
  rw [ModularForm.slash_apply]
  simp only [σ, hg, zero_lt_one, ite_true, ContinuousAlgEquiv.refl_apply,
    abs_one, Complex.ofReal_one, one_pow, one_zpow, mul_one, zpow_neg,
    zpow_natCast, div_eq_mul_inv]
  ring

theorem phase_integralLabel (A : SL(2,ℤ)) (m : ℕ) (z : ℍ) :
    AsymptoticSlashGauge.phase (integralLabel A) m z =
      AsymptoticHyperbolicSlash.phase (Matrix.SpecialLinearGroup.mapGL ℝ A) (2*m) z := by
  apply AsymptoticSlashGauge.phase_projective_eq
  change AsymptoticRationalGroup.rationalMap (AsymptoticSlashGauge.representative (integralLabel A)) = _
  rw [AsymptoticSlashGauge.representative_spec]
  change Matrix.ProjGenLinGroup.mk (AsymptoticRationalFreeness.realMatrix (rationalGL A)) = _
  congr 1
  apply Units.ext
  ext i j
  change ((A.val i j : ℚ) : ℝ) = (A.val i j : ℝ)
  simp

/-- Actual even-weight cusp forms satisfy the unitary projective cocycle
law. They are not scalar-invariant functions on the upper half-plane. -/
theorem weighted_phase_invariant (N m : ℕ)
    (f : CuspForm (level N) ((2*m : ℕ) : ℤ)) (h : gamma N) (z : ℍ) :
    AsymptoticSlashGauge.phase h.val m z * weighted ((2*m : ℕ) : ℤ) f (h.val • z) =
      weighted ((2*m : ℕ) : ℤ) f z := by
  obtain ⟨A, hA, he⟩ := h.property
  rw [← he, phase_integralLabel, integralLabel_action]
  have hs : (f : ℍ → ℂ) ∣[((2*m : ℕ) : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ A) = f :=
    f.slash_action_eq' _ ⟨A, hA, rfl⟩
  have hh := weighted_slash_det_one (Matrix.SpecialLinearGroup.mapGL ℝ A)
    (by simp) m f z
  rw [hs] at hh
  exact hh

#print axioms weighted_slash_det_one
#print axioms phase_integralLabel
#print axioms weighted_phase_invariant
end QuantitativeEulerOldProjectionHolomorphic
