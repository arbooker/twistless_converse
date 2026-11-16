module

public import QuantitativeMaassWaveResidualV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology

namespace QuantitativeMaass.Wave

/-- A normalized short-time packet approximates every actual graph
vector at the central frequency, on the full quotient Hilbert space.
The error depends on the graph residual and time radius, not on a
cuspidal spectral expansion or the later LV propagation radius. -/
theorem quotientWavePacket_residual_norm (N : ℕ) (x d : AutomorphicSpace N)
    (t : ℝ) (ht : 0 < t)
    (hgraph : FriedrichsGraph N x ((((t:ℂ)^2+1/4) • x)+d))
    (φ : ℝ → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support φ ⊆ Icc (-R) R)
    (hscalar : (∫ s : ℝ, φ s*(Real.cos (t*s):ℂ))=1) :
    let hw := shiftedWaveWeight_of_support (hφ.integrable_of_hasCompactSupport hc) hR hs
    ‖shiftedQuotientWavePacket N φ hw x-x‖ ≤
      (∫ s : ℝ, ‖φ s‖)*(R*Real.cosh (R/2)*‖d‖/t) := by
  intro hw
  have hi : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hcos : Continuous (fun s : ℝ => (Real.cos (t*s):ℂ)) := by fun_prop
  have hprod : Integrable (fun s : ℝ => φ s*(Real.cos (t*s):ℂ)) :=
    (hφ.mul hcos).integrable_of_hasCompactSupport hc.mul_right
  have hscalar' : (∫ s : ℝ, φ s • ((Real.cos (t*s):ℂ) • x))=x := by
    simp_rw [smul_smul]
    rw [integral_smul_const,hscalar,one_smul]
  have hi' : Integrable (fun s : ℝ => φ s • ((Real.cos (t*s):ℂ) • x)) := by
    simpa only [smul_smul] using hprod.smul_const x
  have he : shiftedQuotientWavePacket N φ hw x-x =
      ∫ s : ℝ, φ s • (shiftedQuotientWave N s x-(Real.cos (t*s):ℂ) • x) := by
    calc
      _ = (∫ s : ℝ, φ s • shiftedQuotientWave N s x)-
          ∫ s : ℝ, φ s • ((Real.cos (t*s):ℂ) • x) := by
        rw [shiftedQuotientWavePacket_apply,hscalar']
      _ = _ := by
        rw [← integral_sub (shiftedQuotientWave_packet_integrable N hw x) hi']
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => (smul_sub (φ s) _ _).symm)
  let C : ℝ := R*Real.cosh (R/2)*‖d‖/t
  have hb (s : ℝ) :
      ‖φ s • (shiftedQuotientWave N s x-(Real.cos (t*s):ℂ) • x)‖ ≤ ‖φ s‖*C := by
    by_cases hz : φ s=0
    · simp only [hz,zero_smul,norm_zero,zero_mul,le_refl]
    · have hab : |s| ≤ R := abs_le.mpr (hs hz)
      have hcosh : Real.cosh (|s|/2) ≤ Real.cosh (R/2) := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg (by positivity : 0 ≤ |s|/2),
          abs_of_nonneg (by positivity : 0 ≤ R/2)]
        linarith
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (quotientWave_residual_norm N x d t ht hgraph s).trans
      dsimp only [C]
      apply div_le_div_of_nonneg_right _ ht.le
      calc
        _ ≤ R*(Real.cosh (R/2)*‖d‖) :=
          mul_le_mul hab (mul_le_mul_of_nonneg_right hcosh (norm_nonneg _))
            (by positivity) hR
        _ = _ := by ring
  rw [he]
  calc
    _ ≤ ∫ s : ℝ, ‖φ s‖*C :=
      norm_integral_le_of_norm_le (hi.norm.mul_const C) (Filter.Eventually.of_forall hb)
    _ = _ := integral_mul_const _ _

#print axioms quotientWavePacket_residual_norm

end QuantitativeMaass.Wave
