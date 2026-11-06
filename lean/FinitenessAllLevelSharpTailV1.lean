module

public import FinitenessAllLevelSharpHeightV1
public import FinitenessAllLevelFormalCuspV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set Function.Periodic FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelGlobalHeight QuantitativeArithmeticRetainedCertificate

/-- The disk norm is controlled by any bound for the corresponding Fourier
function above the disk's initial height. -/
theorem norm_le_of_tail {a : ℝ} (F : space (radius a)) (G : ℂ → ℂ)
    (he : ∀ z : ℂ, a ≤ z.im → lift F z = G z)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z : ℂ, a ≤ z.im → ‖G z‖ ≤ M) : ‖F‖ ≤ M := by
  apply (ContinuousMap.norm_le F.val hM).mpr
  intro w
  rw [← extend_apply F.val w]
  by_cases hw : w.val = 0
  · rw [hw, F.property.2, norm_zero]
    exact hM
  · have hi : a ≤ (invQParam 1 w.val).im := by
      have hn : ‖qParam 1 (invQParam 1 w.val)‖ ≤ radius a := by
        rw [qParam_right_inv (by norm_num) hw]
        simpa only [mem_closedBall, dist_zero_right] using w.property
      rw [norm_qParam, div_one] at hn
      change Real.exp (-2 * Real.pi * (invQParam 1 w.val).im) ≤ Real.exp (-2 * Real.pi * a) at hn
      rw [Real.exp_le_exp] at hn
      nlinarith [Real.pi_pos]
    have heq := he (invQParam 1 w.val) hi
    change extend F.val (qParam 1 (invQParam 1 w.val)) = G (invQParam 1 w.val) at heq
    rw [qParam_right_inv (by norm_num) hw] at heq
    rw [heq]
    exact hb _ hi

/-- Sharp tail propagation for any function recovered by the actual formal
tree. The constant precedes the eigenvalue, function and initial tail bound;
original Fourier functions satisfy the recovery identity by original_formal. -/
theorem sharp_tail_bound {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℂ) (F : space (radius a)) (G : ℂ → ℂ),
      (∀ z : ℂ, 0 < z.im → formal A P a χ m lam F z = G z) →
      ∀ M : ℝ, 0 ≤ M → (∀ z : ℂ, a ≤ z.im → ‖G z‖ ≤ M) →
      ∀ z : ℂ, a / (p : ℝ) ^ j ≤ z.im → ‖G z‖ ≤ C * (1 + ‖lam‖) ^ j * M := by
  obtain ⟨C, hC, hb⟩ := formal_sharp_height hN hp A P ha hae χ m j
  refine ⟨C, hC, fun lam F G he M hM htail z hz => ?_⟩
  have hF : ‖F‖ ≤ M := norm_le_of_tail F G (fun w hw =>
    (formal_above A P a χ m lam F hw).symm.trans (he w (ha.trans_le hw))) hM htail
  have hzpos : 0 < z.im := (div_pos ha (pow_pos (Nat.cast_pos.mpr hp.pos) _)).trans_le hz
  rw [← he z hzpos]
  exact (hb lam F z hz).trans (mul_le_mul_of_nonneg_left hF (by positivity))

#print axioms norm_le_of_tail
#print axioms sharp_tail_bound

end FinitenessAllLevelFormalContinuation
