module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic
public import QuantitativeMaassWeightedEnergyCancellationV1
public import QuantitativeMaassWeightedGradientBoundV1

/-! Consolidated chapter: QuantitativeArithmeticMaassWeighted. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticMaassWeightedFluxBoundV1 -/
section
/- Adapted from Min’s paused WeightedFluxBound draft. The original source is
unchanged. This separate namespace supplies the missing scalar cancellation. -/




set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section

open scoped InnerProductSpace

namespace QuantitativeArithmeticMaassWeighted

/-- Sharp two-component flux estimate, retaining speed one in the eventual
exponential-weight argument. -/
theorem paired_flux_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {a K : ℝ} (ha : 0≤a) (d₀ d₁ g₀ g₁ : H)
    (hd : ‖d₀‖^2+‖d₁‖^2≤a^2*K^2) :
    4*|(inner ℂ d₀ g₀+inner ℂ d₁ g₁).re|≤
      2*a*(K^2+‖g₀‖^2+‖g₁‖^2) := by
  by_cases hz : a=0
  · subst a
    norm_num at hd
    have hd₀ : d₀=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg d₀,sq_nonneg ‖d₁‖])
    have hd₁ : d₁=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg d₁,sq_nonneg ‖d₀‖])
    simp [hd₀,hd₁]
  have hap : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
  have hs : |(inner ℂ d₀ g₀+inner ℂ d₁ g₁).re|≤‖d₀‖*‖g₀‖+‖d₁‖*‖g₁‖ := by
    exact (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans
      (add_le_add (norm_inner_le_norm d₀ g₀) (norm_inner_le_norm d₁ g₁)))
  have hp : a*(2*(‖d₀‖*‖g₀‖+‖d₁‖*‖g₁‖))≤a*(a*(K^2+‖g₀‖^2+‖g₁‖^2)) := by
    nlinarith [sq_nonneg (‖d₀‖-a*‖g₀‖),sq_nonneg (‖d₁‖-a*‖g₁‖)]
  have h : 2*(‖d₀‖*‖g₀‖+‖d₁‖*‖g₁‖)≤a*(K^2+‖g₀‖^2+‖g₁‖^2) := by
    by_contra hnot
    have hpos := mul_pos hap (sub_pos.mpr (lt_of_not_ge hnot))
    nlinarith [hp]
  linarith

#print axioms paired_flux_bound

end QuantitativeArithmeticMaassWeighted
end
end

/-! ## QuantitativeArithmeticMaassWeightedEnergyEstimateV1 -/
section
/- Adapted from Min’s paused WeightedEnergyEstimate draft, preserving the
original draft and using a separate namespace for the checked completion. -/





set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology InnerProductSpace

namespace QuantitativeArithmeticMaassWeighted

open QuantitativeMaass QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassGradient QuantitativeArithmeticMaassWave

/-- The sharp weighted energy differential bound. Its pointwise hypothesis is
an explicit logarithmic-gradient estimate, not a propagation assumption. -/
theorem energyRate_le (N : ℕ) (b : Cutoff N) {a : ℝ} (ha : 0≤a)
    (hlog : ∀ z : ℍ, ‖cutoffGradient true b.value z‖^2+‖cutoffGradient false b.value z‖^2≤
      a^2*‖upperFunction b.value z‖^2)
    (u v : QuotientEnergySpace N) (y : AutomorphicSpace N)
    (hy : FriedrichsGraph N (energyInclusion N u) y) :
    energyRate N b u v (energyInclusion N v) ((1/4 : ℂ) • energyInclusion N u-y)≤
      (2*a+5/4)*energy N b u (energyInclusion N v) := by
  let k := multiplier N b (ambientInclusion N v)
  let m := multiplier N b (ambientInclusion N u)
  let gx := multiplier N b (quotientGradient N true u)
  let gy := multiplier N b (quotientGradient N false u)
  let F := inner ℂ (gradientMultiplier N b true (ambientInclusion N v)) gx+
    inner ℂ (gradientMultiplier N b false (ambientInclusion N v)) gy
  have hf : 4*|F.re|≤2*a*(‖k‖^2+‖gx‖^2+‖gy‖^2) :=
    paired_flux_bound ha _ _ gx gy (gradient_pair_bound N b a hlog (ambientInclusion N v))
  have hm0 : (inner ℂ m k).re≤‖m‖*‖k‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm m k)
  have hm : (5/2 : ℝ)*(inner ℂ m k).re≤(5/4 : ℝ)*(‖m‖^2+‖k‖^2) := by
    nlinarith [sq_nonneg (‖m‖-‖k‖)]
  rw [energyRate_wave N b u v y hy]
  change (5/2 : ℝ)*(inner ℂ m k).re-4*F.re≤
    (2*a+5/4)*(‖k‖^2+‖gx‖^2+‖gy‖^2+‖m‖^2)
  nlinarith [neg_le_abs F.re,mul_nonneg ha (sq_nonneg ‖m‖),sq_nonneg ‖gx‖,sq_nonneg ‖gy‖]

/-- Weighted energy of the actual constructed quotient wave. -/
def waveEnergy (N : ℕ) (b : Cutoff N) (x y : AutomorphicSpace N) (t : ℝ) : ℝ :=
  energy N b (quotientEnergyWave N x y t) (quotientWaveVelocity N x y t)

theorem waveEnergy_hasDerivAt (N : ℕ) (b : Cutoff N) {x y z : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z) (t : ℝ) :
    HasDerivAt (waveEnergy N b x y)
      (energyRate N b (quotientEnergyWave N x y t)
        (graphEnergyLift N (quotientWaveVelocity N x y t) (quotientWaveVelocity N y z t))
        (quotientWaveVelocity N x y t)
        ((1/4 : ℂ) • Wave.shiftedQuotientWave N t x-Wave.shiftedQuotientWave N t y)) t :=
  energy_hasDerivAt N b (quotientEnergyWave_hasDerivAt N hxy hyz t)
    (quotientWaveVelocity_hasDerivAt N x y t)

/-- Actual wave-energy growth estimate for initial data in the second operator
domain, hence for smooth compact Poincare seeds. -/
theorem waveEnergy_deriv_le (N : ℕ) (b : Cutoff N) {a : ℝ} (ha : 0≤a)
    (hlog : ∀ Z : ℍ, ‖cutoffGradient true b.value Z‖^2+‖cutoffGradient false b.value Z‖^2≤
      a^2*‖upperFunction b.value Z‖^2)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y) (hyz : FriedrichsGraph N y z)
    (t : ℝ) : deriv (waveEnergy N b x y) t≤(2*a+5/4)*waveEnergy N b x y t := by
  rw [(waveEnergy_hasDerivAt N b hxy hyz t).deriv]
  have hu := quotientEnergyWave_value N hxy t
  have hv := graphEnergyLift_value N (quotientWaveVelocity_graph N hxy hyz t)
  have hg : FriedrichsGraph N (energyInclusion N (quotientEnergyWave N x y t))
      (Wave.shiftedQuotientWave N t y) := by
    rw [hu]
    exact Wave.shiftedQuotientWave_graph N t hxy
  have h := energyRate_le N b ha hlog (quotientEnergyWave N x y t)
    (graphEnergyLift N (quotientWaveVelocity N x y t) (quotientWaveVelocity N y z t))
    (Wave.shiftedQuotientWave N t y) hg
  rw [hu,hv] at h
  exact h

#print axioms energyRate_le
#print axioms waveEnergy_deriv_le

end QuantitativeArithmeticMaassWeighted
end
end

/-! ## QuantitativeArithmeticMaassWeightedGronwallV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open QuantitativeMaass QuantitativeMaass.Weighted
open QuantitativeArithmeticMaassGradient QuantitativeArithmeticMaassWave

namespace QuantitativeArithmeticMaassWeighted

/-- Gronwall applied to the actual quotient-wave energy. The coefficient of
the logarithmic gradient is exactly two, as needed for propagation speed one. -/
theorem waveEnergy_exp_bound (N : ℕ) (b : Cutoff N) {a : ℝ} (ha : 0 ≤ a)
    (hlog : ∀ Z : ℍ, ‖cutoffGradient true b.value Z‖^2 +
      ‖cutoffGradient false b.value Z‖^2 ≤ a^2 * ‖upperFunction b.value Z‖^2)
    {x y z : AutomorphicSpace N} (hxy : FriedrichsGraph N x y)
    (hyz : FriedrichsGraph N y z) {t : ℝ} (ht : 0 ≤ t) :
    waveEnergy N b x y t ≤ waveEnergy N b x y 0 * Real.exp ((2*a+5/4)*t) := by
  let E := waveEnergy N b x y
  have hd : ∀ s : ℝ, DifferentiableAt ℝ E s :=
    fun s => (waveEnergy_hasDerivAt N b hxy hyz s).differentiableAt
  have hc : Continuous E := continuous_iff_continuousAt.mpr
    (fun s => (hd s).continuousAt)
  have hg := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := deriv E) (δ := E 0) (K := 2*a+5/4) (ε := 0)
    (a := 0) (b := t) hc.continuousOn
    (fun s _ r hr => (hd s).hasDerivAt.hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun s _ => by
      simpa only [add_zero] using waveEnergy_deriv_le N b ha hlog hxy hyz s)
  simpa only [gronwallBound_ε0, sub_zero] using hg t ⟨ht, le_rfl⟩

#print axioms waveEnergy_exp_bound
end QuantitativeArithmeticMaassWeighted
end
end
