module

public import AsymptoticCylinderUpperTailV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open Filter AsymptoticDiagonalTrace
open scoped Topology

/-- Elementary normalization of the upper-cusp trace bound. -/
theorem normalized_affine_tendsto (t : ℕ) (C D : ℝ) :
    Tendsto (fun m : ℕ => (((m+2*t+1:ℕ):ℝ)*C+D)/(m+2:ℕ)) atTop (𝓝 C) := by
  have hi : Tendsto (fun m : ℕ => ((m:ℝ)+2)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop)
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).add
    (hi.const_mul (((2*(t:ℝ)-1)*C)+D))
  have he (m : ℕ) : (((m+2*t+1:ℕ):ℝ)*C+D)/(m+2:ℕ)=
      C+(((2*(t:ℝ)-1)*C)+D)*((m:ℝ)+2)⁻¹ := by
    have hn : (m:ℝ)+2≠0 := by positivity
    push_cast
    field_simp
    ring
  simp only [mul_zero,add_zero] at ht
  exact ht.congr (fun m => (he m).symm)

/-- For each fixed upper height, the normalized trace is eventually
bounded by its O(1/H) leading term plus any prescribed error. -/
theorem upperCompression_normalized_eventually (t : ℕ) {scale ε H : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hH : 0<H) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop,
      trace (fourierBasis m t hs hε) (upperCompression m t hs hε H)/(m+2:ℕ)<
        Real.log 2/(scale*H/2)+δ := by
  have ht := normalized_affine_tendsto t (Real.log 2/(scale*H/2))
    (1/(1-Real.exp (-(scale*H/2))))
  have he := (tendsto_order.mp ht).2 (Real.log 2/(scale*H/2)+δ) (lt_add_of_pos_right _ hδ)
  apply he.mono
  intro m hm
  apply (div_le_div_of_nonneg_right (upperCompression_trace_bound m t hs hε hH).2 (by positivity : (0:ℝ)≤(m+2:ℕ))).trans_lt
  simpa only [mul_div_assoc] using hm

/-- Taking upper height to infinity after the weight limit removes the
actual upper-cusp compression. No interchange of limits is used. -/
theorem upperCompression_normalized_small (t : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) {δ : ℝ} (hδ : 0<δ) :
    ∃ H₀ : ℝ,0<H₀ ∧ ∀ H : ℝ,H₀≤H →
      ∀ᶠ m : ℕ in atTop,
        trace (fourierBasis m t hs hε) (upperCompression m t hs hε H)/(m+2:ℕ)<δ := by
  let H₀ := 1+4*Real.log 2/(scale*δ)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hH₀ : 0<H₀ := by dsimp [H₀]; positivity
  refine ⟨H₀,hH₀,?_⟩
  intro H hH
  have hHp : 0<H := hH₀.trans_le hH
  have hc : Real.log 2/(scale*H/2)<δ/2 := by
    apply (div_lt_iff₀ (by positivity : 0<scale*H/2)).mpr
    have hbase : 4*Real.log 2/(scale*δ)<H := by
      dsimp [H₀] at hH
      linarith
    have hb := (div_lt_iff₀ (mul_pos hs hδ)).mp hbase
    nlinarith
  apply (upperCompression_normalized_eventually t hs hε hHp (half_pos hδ)).mono
  intro m hm
  linarith

#print axioms normalized_affine_tendsto
#print axioms upperCompression_normalized_eventually
#print axioms upperCompression_normalized_small

end AsymptoticCylinder
