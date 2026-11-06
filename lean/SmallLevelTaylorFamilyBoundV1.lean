module

public import SmallLevelTaylorGeometryV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Set Metric FinitenessPolynomialSeries FinitenessFourierConstruction

theorem deformed_bound (k : ℕ) {a : ℕ → ℂ} (K : ℕ) {C : ℝ} (hC : 0≤C)
    (hbound : ∀ z : ℂ, 0<z.im → ‖fourier a z‖≤C/z.im^K)
    (β : ℝ) {c y : ℝ} (hc : 0<c) (hy : 0<y) {u : ℂ} (hu : ‖u‖≤1/2) :
    ‖deformed k a β c y u‖≤(2^k*C*(8*c)^K)/y^K := by
  have hpref : ‖((1+u)^k)⁻¹‖≤(2:ℝ)^k := by
    rw [← inv_pow,norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (one_add_inv_norm_le hu) k
  have hheight := deformPoint_height β hc hy hu
  have hpos := deformPoint_positive β hc hy hu
  have hpow : (y/(8*c))^K≤(deformPoint β c y u).im^K :=
    pow_le_pow_left₀ (by positivity) hheight K
  calc
    ‖deformed k a β c y u‖=‖((1+u)^k)⁻¹‖*‖fourier a (deformPoint β c y u)‖ := norm_mul _ _
    _≤2^k*(C/(deformPoint β c y u).im^K) :=
      mul_le_mul hpref (hbound _ hpos) (norm_nonneg _) (by positivity)
    _≤2^k*(C/(y/(8*c))^K) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left hC (by positivity) hpow
    _=(2^k*C*(8*c)^K)/y^K := by
      rw [div_pow,div_div_eq_mul_div]
      ring

/-- One exponent and constant work for every small height and every complex
deformation parameter in the fixed half-unit disk. This is the uniform bound
needed for Cauchy's Taylor remainder estimate. -/
theorem deformed_family_bound (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∃ D : ℝ, 0≤D ∧ ∀ β y : ℝ, 0<y → ∀ u : ℂ, ‖u‖≤1/2 →
      ‖deformed k a β c y u‖≤D/y^K := by
  obtain ⟨K,C,hC,hbound⟩ := fourier_boundary_bound ha ha0
  exact ⟨K,2^k*C*(8*c)^K,by positivity,
    fun β y hy u hu => deformed_bound k K hC hbound β hc hy hu⟩

/-- The uniform bound applies to the actual Fourier coefficients supplied by
an original Euler-product solution, with no extra coefficient assumption. -/
theorem original_deformed_family_bound {N k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∃ D : ℝ, 0≤D ∧ ∀ β y : ℝ, 0<y → ∀ u : ℂ, ‖u‖≤1/2 →
      ‖deformed k (FinitenessOriginalFourier.fullCoefficients f k) β c y u‖≤D/y^K := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  exact deformed_family_bound k (FinitenessOriginalFourier.polynomial_bound hf.zero hg k)
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero k) hc

#print axioms deformed_bound
#print axioms deformed_family_bound
#print axioms original_deformed_family_bound

end SmallLevelTaylor
