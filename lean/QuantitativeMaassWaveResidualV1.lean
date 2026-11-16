module

public import QuantitativeMaassOscillatorResidualV1
public import QuantitativeArithmeticMaassWavePDEV1
public import QuantitativeMaassShiftedWavePacketV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology

namespace QuantitativeMaass.Wave

open QuantitativeArithmeticMaassWave

/-- Strong wave evolution of an approximate eigenvector on the whole
quotient. The forcing is the evolved actual Friedrichs-graph residual. -/
theorem quotientWave_residual_velocity (N : ℕ) (x d : AutomorphicSpace N)
    (t s : ℝ) :
    HasDerivAt (quotientWaveVelocity N x ((((t:ℂ)^2+1/4) • x)+d))
      (-(t^2) • shiftedQuotientWave N s x-shiftedQuotientWave N s d) s := by
  have h := quotientWaveVelocity_hasDerivAt N x ((((t:ℂ)^2+1/4) • x)+d) s
  apply h.congr_deriv
  simp only [map_add,map_smul]
  module

/-- Exact Duhamel formula for the genuine quotient wave. In particular
the continuous and exceptional spectra have not been discarded. -/
theorem quotientWave_residual_integral (N : ℕ) (x d : AutomorphicSpace N)
    (t : ℝ) (ht : t ≠ 0)
    (hgraph : FriedrichsGraph N x ((((t:ℂ)^2+1/4) • x)+d)) (s : ℝ) :
    shiftedQuotientWave N s x-Real.cos (t*s) • x =
      ∫ r in (0:ℝ)..s, (Real.sin (t*(s-r))/t) • (-shiftedQuotientWave N r d) := by
  have h := oscillator_residual_integral
    (fun r => shiftedQuotientWave N r x)
    (quotientWaveVelocity N x ((((t:ℂ)^2+1/4) • x)+d))
    (fun r => -shiftedQuotientWave N r d) t ht
    (quotientWave_hasDerivAt N hgraph)
    (fun r => by simpa only [sub_eq_add_neg] using quotientWave_residual_velocity N x d t r)
    (shiftedQuotientWave_stronglyContinuous N d).neg
    (quotientWaveVelocity_zero N x _) s
  simpa only [shiftedQuotientWave_zero,ContinuousLinearMap.id_apply] using h

/-- The full-quotient wave residual estimate gains one power of the
central frequency. No cuspidal projection or basis is used. -/
theorem quotientWave_residual_norm (N : ℕ) (x d : AutomorphicSpace N)
    (t : ℝ) (ht : 0 < t)
    (hgraph : FriedrichsGraph N x ((((t:ℂ)^2+1/4) • x)+d)) (s : ℝ) :
    ‖shiftedQuotientWave N s x-Real.cos (t*s) • x‖ ≤
      |s| * (Real.cosh (|s|/2)*‖d‖)/t := by
  have hbound (r : ℝ) (hr : r ∈ uIoc 0 s) :
      ‖-shiftedQuotientWave N r d‖ ≤ Real.cosh (|s|/2)*‖d‖ := by
    have har : |r| ≤ |s| := by
      by_cases hs : 0 ≤ s
      · rw [uIoc_of_le hs] at hr
        rw [abs_of_nonneg hr.1.le,abs_of_nonneg hs]
        exact hr.2
      · have hs' : s ≤ 0 := le_of_not_ge hs
        rw [uIoc_of_ge hs'] at hr
        rw [abs_of_nonpos hr.2,abs_of_nonpos hs']
        linarith [hr.1]
    rw [norm_neg]
    apply (shiftedQuotientWave_apply_norm_le N r d).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ |r|/2),
      abs_of_nonneg (by positivity : 0 ≤ |s|/2)]
    linarith
  have h := oscillator_residual_norm
    (fun r => shiftedQuotientWave N r x)
    (quotientWaveVelocity N x ((((t:ℂ)^2+1/4) • x)+d))
    (fun r => -shiftedQuotientWave N r d) t ht
    (quotientWave_hasDerivAt N hgraph)
    (fun r => by simpa only [sub_eq_add_neg] using quotientWave_residual_velocity N x d t r)
    (shiftedQuotientWave_stronglyContinuous N d).neg
    (quotientWaveVelocity_zero N x _) s (Real.cosh (|s|/2)*‖d‖) hbound
  simpa only [shiftedQuotientWave_zero,ContinuousLinearMap.id_apply] using h

#print axioms quotientWave_residual_velocity
#print axioms quotientWave_residual_integral
#print axioms quotientWave_residual_norm

end QuantitativeMaass.Wave
