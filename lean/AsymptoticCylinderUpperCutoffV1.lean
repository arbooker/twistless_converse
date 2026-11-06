module

public import AsymptoticSandwichCutoffV1
public import AsymptoticCylinderUpperTailLimitV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open ContinuousLinearMap InnerProductSpace AsymptoticObservation AsymptoticDiagonalTrace
open AsymptoticFourierNorm
open scoped InnerProduct

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

noncomputable def upperCutTrace (R : G →L[ℂ] Space) (I : G →L[ℂ] G)
    (m t : ℕ) {scale ε : ℝ} (hs : 0 < scale) (hε : 0 < ε) (H : ℝ) : ℝ :=
  trace (fourierBasis m t hs hε)
    (compressedSandwich (removePart (upperProjection H) R) I (holomorphicSpace m t hs hε))

theorem upperCompression_trace_nonneg (m t : ℕ) {scale ε : ℝ}
    (hs : 0 < scale) (hε : 0 < ε) (H : ℝ) :
    0 ≤ trace (fourierBasis m t hs hε) (upperCompression m t hs hε H) := by
  simp only [trace, upperCompression_diagonal]
  exact tsum_nonneg (fun n => upperMass_nonneg m t (mul_pos hs (by positivity)) hε H)

theorem upper_adjoint_gram_bound (R : G →L[ℂ] Space) {B : ℝ} (hR : ‖R‖ ≤ B)
    (m t n : ℕ) {scale ε : ℝ} (hs : 0 < scale) (hε : 0 < ε) (H : ℝ) :
    ‖R.adjoint (upperProjection H (unitMode m t n hs hε))‖^2 ≤
      B^2 * upperMass m t (scale*(n+1:ℕ)) ε H := by
  have hh := R.adjoint.le_opNorm (upperProjection H (unitMode m t n hs hε))
  rw [ContinuousLinearMap.adjoint.norm_map] at hh
  have hn := hh.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  apply (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq
  rw [mul_pow, upperProjection_unitMode_norm_sq]

theorem upper_adjoint_gram_summable_bound (R : G →L[ℂ] Space) {B : ℝ} (hR : ‖R‖ ≤ B)
    (m t : ℕ) {scale ε H : ℝ} (hs : 0 < scale) (hε : 0 < ε) (hH : 0 < H) :
    Summable (fun n => ‖R.adjoint (upperProjection H (unitMode m t n hs hε))‖^2) ∧
    (∑' n, ‖R.adjoint (upperProjection H (unitMode m t n hs hε))‖^2) ≤
      B^2 * trace (fourierBasis m t hs hε) (upperCompression m t hs hε H) := by
  have hm := (upperMass_summable_bound m t hs hε hH).1.mul_left (B^2)
  have hp := fun n => upper_adjoint_gram_bound R hR m t n hs hε H
  have hg := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hp hm
  refine ⟨hg, ?_⟩
  apply (hg.tsum_le_tsum hp hm).trans_eq
  rw [tsum_mul_left]
  simp only [trace, upperCompression_diagonal]

theorem factored_gram_summable_bound (R₀ : G →L[ℂ] Space) {B : ℝ} (hR : ‖R₀‖ ≤ B)
    (m t : ℕ) {scale ε : ℝ} (hs : 0 < scale) (hε : 0 < ε) :
    Summable (fun n => ‖((inclusion hε).comp R₀).adjoint (unitMode m t n hs hε)‖^2) ∧
    (∑' n, ‖((inclusion hε).comp R₀).adjoint (unitMode m t n hs hε)‖^2) ≤
      B^2*(1+majorantConstant t scale ε)*(m+2:ℕ) := by
  have hp (n : ℕ) : ‖((inclusion hε).comp R₀).adjoint (unitMode m t n hs hε)‖^2 ≤
      B^2*modeRatio m t scale ε (n+1) := by
    have hh := reconstructed_fourier_gram R₀ m t hs hε n
    simp only [fourierBasis_apply, modeInSpace] at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hR 2)
      (modeRatio_nonneg m t (n+1) scale hε)
  have hm := positive_modeRatio_summable_bound m t hs hε
  have hg := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hp (hm.1.mul_left (B^2))
  refine ⟨hg, ?_⟩
  apply (hg.tsum_le_tsum hp (hm.1.mul_left (B^2))).trans
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left hm.2 (sq_nonneg B)).trans_eq
  ring

noncomputable def upperCutError (A B C r : ℝ) : ℝ :=
  C*(2*Real.sqrt A*Real.sqrt (B^2*r)+B^2*r)

/-- The concrete normalized upper-cut error is controlled by the
normalized upper-cusp Fourier mass and the original capped Gram bound. -/
theorem factored_upperCut_trace_bound (R₀ : G →L[ℂ] Space) (I : G →L[ℂ] G)
    {B C : ℝ} (hR : ‖R₀‖ ≤ B) (hI : ‖I‖ ≤ C)
    (m t : ℕ) {scale ε H : ℝ} (hs : 0 < scale) (hε : 0 < ε) (hH : 0 < H) :
    ‖trace (fourierBasis m t hs hε)
        (compressedSandwich ((inclusion hε).comp R₀) I (holomorphicSpace m t hs hε)) -
      upperCutTrace ((inclusion hε).comp R₀) I m t hs hε H‖/(m+2:ℕ) ≤
      upperCutError (B^2*(1+majorantConstant t scale ε)) B C
        (trace (fourierBasis m t hs hε) (upperCompression m t hs hε H)/(m+2:ℕ)) := by
  let R := (inclusion hε).comp R₀
  let T := trace (fourierBasis m t hs hε) (upperCompression m t hs hε H)
  let k : ℝ := (m+2:ℕ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hT : 0 ≤ T := upperCompression_trace_nonneg m t hs hε H
  have hRn : ‖R‖ ≤ B := by
    apply (opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_right (inclusion_norm_le hε) (norm_nonneg _)).trans
    simpa only [one_mul] using hR
  obtain ⟨hu, hu'⟩ := factored_gram_summable_bound R₀ hR m t hs hε
  obtain ⟨hd, hd'⟩ := upper_adjoint_gram_summable_bound R hRn m t hs hε hH
  have hA : 0 ≤ B^2*(1+majorantConstant t scale ε) := by
    unfold majorantConstant
    positivity
  have hD : 0 ≤ B^2*(T/k) := mul_nonneg (sq_nonneg B) (div_nonneg hT hk.le)
  have hdb : (∑' n, ‖R.adjoint (upperProjection H (unitMode m t n hs hε))‖^2) ≤
      (B^2*(T/k))*k := by
    rw [mul_assoc, div_mul_cancel₀ _ hk.ne']
    exact hd'
  have hh := removePart_normalized_trace_bound (upperProjection H)
    (AsymptoticRegionL2.projection_adjoint _ _ _) R I (holomorphicSpace m t hs hε)
    (fourierBasis m t hs hε)
    (by simpa only [fourierBasis_apply, modeInSpace] using hu)
    (by simpa only [fourierBasis_apply, modeInSpace] using hd) hA hD hk
    (by simpa only [fourierBasis_apply, modeInSpace] using hu')
    (by simpa only [fourierBasis_apply, modeInSpace] using hdb)
  apply hh.trans
  exact mul_le_mul_of_nonneg_right hI (add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hD)

#print axioms upper_adjoint_gram_summable_bound
#print axioms factored_gram_summable_bound
#print axioms factored_upperCut_trace_bound

end AsymptoticCylinder
