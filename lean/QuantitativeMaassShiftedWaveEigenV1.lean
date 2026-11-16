module

public import QuantitativeMaassShiftedWaveRangeV1
public import QuantitativeMaassWaveEigenV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem shiftedRangeCosine_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {v : H} (hv : A v = s • v) (t : ℝ) :
    shiftedRangeCosine A t v = signedCosine t (s⁻¹-1-1/4) • v := by
  have he := shiftedRangeCosine_range A hA hd t v
  rw [cfc_eigen A hA hv _ (shiftedDampedCosine_continuous t), hv,
    ← algebraMap_smul ℂ s, map_smul, algebraMap_smul] at he
  have he' := congrArg (fun w : H => s⁻¹ • w) he
  rw [shiftedDampedCosine_on_spectrum t s hs hs1] at he'
  simpa [smul_smul, ne_of_gt hs] using he'

theorem shiftedRangeCosine_graph_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) {e : ℝ} (he : 0 ≤ e) {v : H}
    (h : A (v+e • v) = v) (t : ℝ) :
    shiftedRangeCosine A t v = signedCosine t (e-1/4) • v := by
  have hs : 0 < (1+e)⁻¹ := inv_pos.mpr (by linarith)
  have hs1 : (1+e)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
  have hh := shiftedRangeCosine_eigen A hA hd hs hs1 (inverse_eigen_of_graph A he h) t
  simpa only [inv_inv, add_sub_cancel_left] using hh

theorem shiftedRangeCosine_graph_eigen_complex (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) {e : ℝ} (he : 0 ≤ e) {v : H}
    (h : A (v+(e:ℂ) • v) = v) (t : ℝ) :
    shiftedRangeCosine A t v = (signedCosine t (e-1/4) : ℂ) • v := by
  have h' : A (v+e • v) = v := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using h
  have hh := shiftedRangeCosine_graph_eigen A hA hd he h' t
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using hh

/-- Exact action on the actual quotient Laplacian graph, including energies
below 1/4. No spectral decomposition or eigenfunction completeness is assumed. -/
theorem shiftedQuotientWave_eigen (N : ℕ) {e : ℝ} (he : 0 ≤ e)
    {v : AutomorphicSpace N} (h : FriedrichsGraph N v ((e:ℂ) • v)) (t : ℝ) :
    shiftedQuotientWave N t v = (signedCosine t (e-1/4) : ℂ) • v :=
  shiftedRangeCosine_graph_eigen_complex (friedrichsResolvent N)
    (friedrichsResolvent_isSelfAdjoint N) (friedrichsResolvent_denseRange N) he h t

theorem shiftedQuotientWave_principal (N : ℕ) (r : ℝ)
    {v : AutomorphicSpace N} (h : FriedrichsGraph N v (((1/4+r^2 : ℝ):ℂ) • v))
    (t : ℝ) : shiftedQuotientWave N t v = (Real.cos (t*r) : ℂ) • v := by
  have hh := shiftedQuotientWave_eigen N (e := 1/4+r^2) (by positivity) h t
  have he : (1/4+r^2 : ℝ)-1/4 = r^2 := by ring
  rw [he, signedCosine_nonneg_energy t (r^2) (sq_nonneg r), Real.sqrt_sq_eq_abs] at hh
  have hc : Real.cos (t*|r|) = Real.cos (t*r) := by
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr, mul_neg, Real.cos_neg]
  simpa only [hc] using hh

theorem shiftedQuotientWave_exceptional (N : ℕ) {e : ℝ} (he : 0 ≤ e)
    (he1 : e ≤ 1/4) {v : AutomorphicSpace N}
    (h : FriedrichsGraph N v ((e:ℂ) • v)) (t : ℝ) :
    shiftedQuotientWave N t v = (Real.cosh (t*Real.sqrt (1/4-e)) : ℂ) • v := by
  have hh := shiftedQuotientWave_eigen N he h t
  rw [signedCosine_nonpos_energy t (e-1/4) (sub_nonpos.mpr he1)] at hh
  simpa only [neg_sub] using hh

#print axioms shiftedQuotientWave_eigen
#print axioms shiftedQuotientWave_principal
#print axioms shiftedQuotientWave_exceptional

end QuantitativeMaass.Wave
