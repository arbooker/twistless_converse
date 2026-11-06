module

public import QuantitativeArithmeticRetainedActualTerminalBoundV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedHorizonScale
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns AsymptoticFiniteBranch
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule QuantitativeArithmeticRetainedTerminalAlgebra
open QuantitativeArithmeticRetainedPhysicalSector QuantitativeArithmeticRetainedNestedCountComparison
open QuantitativeArithmeticRetainedApproximationSchedule QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedNestedGeometricTrace

variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)
    (hR₀ : ∀p∈R₀,p.Prime)

/-- One scale pays all reconstruction and trace errors for a common finite
filter. Every parameter constant is chosen before the horizon and weight. -/
theorem exists_common_sector_scale (hN : 0<N) (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) {K a : ℝ} (hK : 0≤K) (ha : 0≤a) :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀ n h : ℕ,∀ c : ℝ,0<h →
      1≤Real.log (observationScale c (h+1)) →
      32≤Real.log (Real.log (h+1:ℝ)) →
      (4:ℝ)^n≤(Real.log (observationScale c (h+1)))^2 → D*c^2≤1/2 →
      ∀ e : Sector N,∀ F : Algebra A P,0≤F ∧ F≤1 → ∀ T : Expression,
      expressionBound T≤Real.exp (Real.exp (a*(4:ℝ)^n)) →
      ExpressionMatrixBound T (Real.exp (Real.exp (a*(4:ℝ)^n))) →
      (∀ x,0≤regularSum T x ∧ regularSum T x≤1) →
      (∀ x,‖rep A P F x-regularSum T x‖≤2/(4:ℝ)^n) →
      0≤holomorphicSum T (h+1) ∧ holomorphicSum T (h+1)≤1 →
      ‖holomorphicSum T (h+1)*normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad-
        normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad‖≤2/(4:ℝ)^n →
      (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
        tr A P F/(4*Real.pi)+C/(4:ℝ)^n+3*Real.exp (-Real.log (h+1:ℝ)/4) := by
  obtain ⟨b,hb,hcost⟩ := exists_horizon_sandwich_cost A hR₀ hN P hK ha
  obtain ⟨d,hd,htrace⟩ := exists_horizon_trace_scale A P hK hb
  obtain ⟨C₀,D₀,hC₀,hD₀,hanalytic⟩ := exists_horizon_analytic_scale A P hK
  let C := C₀+2*P.ε⁻¹/(4*Real.pi)
  let D := geometryGrowthCoefficient+29+d+D₀
  have hε := P.epsilon_pos
  have hC : 0≤C := by dsimp only [C]; positivity
  have hD : 0≤D := by dsimp only [D]; linarith [geometryGrowthCoefficient_nonneg]
  refine ⟨C,D,hC,hD,?_⟩
  intro n h c hh hs hlog hn hscale e F hF T hmass hmatrix hreg happrox hphys hres
  let s := Real.exp ((K+1)*(4:ℝ)^n)
  let E := sandwichExpression A hR₀ hN P (tolerance s 0) e T
  let M := Real.exp (Real.exp (b*(4:ℝ)^n))
  let Y := lowerHeight A P (tolerance s 0)
  let H := Real.exp (16*s)
  have hc := hcost n e T hmass hmatrix
  have hgeom : (geometryGrowthCoefficient+29+d)*c^2≤1/2 := by
    apply le_trans _ hscale
    dsimp only [D]
    nlinarith [mul_nonneg hD₀ (sq_nonneg c)]
  have han : D₀*c^2≤1/2 := by
    apply le_trans _ hscale
    dsimp only [D]
    nlinarith [mul_nonneg (show 0≤geometryGrowthCoefficient+29+d by linarith [geometryGrowthCoefficient_nonneg]) (sq_nonneg c)]
  have ht := htrace n h c hh hs hlog hn hgeom
  have he := hanalytic n h c hh hlog hn han
  have hf : expressionBound E*uniformRetainedTraceError (M*(H+2)) Y H h (periodizationSet Y H).card≤
      Real.exp (-Real.log (h+1:ℝ)/4) := by
    apply le_trans _ ht.2
    exact mul_le_mul_of_nonneg_right hc.1
      (uniformRetainedTraceError_nonneg _ _ (lowerHeight_pos A P (tolerance_pos s 0)) _ _)
  have hV := sector_finrank_le_terminal A hR₀ hN P hdiv hbad (tolerance_pos s 0)
    (QuantitativeArithmeticRetainedScheduledTrace.accuracy_le_half (Real.exp_pos _).le)
    (Real.exp_pos (16*s)) h e T hphys.1
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hphys.1).mpr hphys.2)
    F hF hreg (2/(4:ℝ)^n) (2/(4:ℝ)^n) hres happrox (Real.exp_pos _).le hc.2 ht.1
  have hsplit : (tr A P F+(2/(4:ℝ)^n)*P.ε⁻¹)/(4*Real.pi)+C₀/(4:ℝ)^n=
      tr A P F/(4*Real.pi)+C/(4:ℝ)^n := by dsimp only [C]; ring
  dsimp only at hV he
  linarith only [hV,he,hf,hsplit]

#print axioms exists_common_sector_scale
end QuantitativeArithmeticRetainedHorizonScale
