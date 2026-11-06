module

public import AsymptoticKernelIntegralSeriesV1
public import AsymptoticGramTracePerturbationV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open MeasureTheory UpperHalfPlane Set AsymptoticCylinder AsymptoticCylinderLift
open AsymptoticObservation AsymptoticDiagonalTrace ContinuousLinearMap InnerProductSpace
open AsymptoticStripCoordinates
open scoped InnerProduct

noncomputable def liftedMode (h n : ℕ) {ε : ℝ} (hε : 0 < ε) : AsymptoticHyperbolicSlash.Space :=
  lift (unitMode (2*h) 0 n (by positivity : 0 < 4*Real.pi) hε)

theorem liftedMode_coeFn (h n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    liftedMode h n hε =ᵐ[volume] AsymptoticMassTransport.strip.indicator
      (fun z : ℍ => (z.im : ℂ)*unitRepresentative (2*h) 0 n ε (cylinder z)) :=
  lift_coeFn_of_ae _ _ (unitRepresentative_coeFn (2*h) 0 n hε)

noncomputable def liftedTrace (h : ℕ) {ε : ℝ} (hε : 0 < ε)
    (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) : ℝ :=
  trace (fourierBasis (2*h) 0 (by positivity : 0 < 4*Real.pi) hε)
    (compressedSandwich lift.toContinuousLinearMap.adjoint W
      (holomorphicSpace (2*h) 0 (by positivity : 0 < 4*Real.pi) hε))

theorem liftedTrace_eq_sum (h : ℕ) {ε : ℝ} (hε : 0 < ε)
    (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) :
    liftedTrace h hε W = ∑' n, (⟪W (liftedMode h n hε),liftedMode h n hε⟫_ℂ).re := by
  unfold liftedTrace trace
  apply tsum_congr
  intro n
  let U := holomorphicSpace (2*h) 0 (by positivity : 0 < 4*Real.pi) hε
  let b := fourierBasis (2*h) 0 (by positivity : 0 < 4*Real.pi) hε n
  let L := lift.toContinuousLinearMap
  simp only [compressedSandwich, comp_apply, adjoint_adjoint]
  have hu := U.subtypeL.adjoint_inner_left b (L.adjoint (W (L (b : AsymptoticCylinder.Space))))
  change (⟪U.subtypeL.adjoint (L.adjoint (W (L (b : AsymptoticCylinder.Space)))),b⟫_ℂ).re = _
  rw [hu]
  change (⟪L.adjoint (W (L (b : AsymptoticCylinder.Space))), (b : AsymptoticCylinder.Space)⟫_ℂ).re = _
  rw [L.adjoint_inner_left]
  simp only [b, fourierBasis_apply, modeInSpace, liftedMode, L, LinearIsometry.coe_toContinuousLinearMap]

/-- The branch-action identity on the actual lifted Fourier modes gives
the kernel term on the trace diagonal. All strip indicators are accounted
for here, before interchanging the Fourier sum and integral. -/
theorem branch_diagonal_integral (h n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (S : Set ℍ) (hS : MeasurableSet S) (hstrip : S ⊆ AsymptoticMassTransport.strip)
    (u : ℍ → ℍ) (c : ℍ → ℂ)
    (hact : W (liftedMode h n hε) =ᵐ[volume] S.indicator
      (fun z => c z * (u z).im * unitRepresentative (2*h) 0 n ε (cylinder (u z)))) :
    ⟪liftedMode h n hε,W (liftedMode h n hε)⟫_ℂ =
      ∫ z in S, c z * hyperbolicKernelTerm h n ε (u z) z := by
  rw [L2.inner_def, ← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [hact, liftedMode_coeFn h n hε] with z hw hf
  rw [hw, hf]
  classical
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem (hstrip hz), indicator_of_mem hz]
    simp only [RCLike.inner_apply, hyperbolicKernelTerm, kernelTerm, Complex.ofReal_mul,
      Complex.star_def, map_mul, Complex.conj_ofReal]
    ring
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, inner_zero_right]

/-- The exact trace formula for a bounded measurable branch supported
on a finite retained cell. No smoothness of its coefficient or cell rule
is required. The action hypothesis can be checked on each finite branch
word using the existing concrete slash-operator formulas. -/
theorem branch_trace_integral (h : ℕ) {ε Y H C : ℝ} (hε : 0 < ε) (hY : 0 < Y) (hC : 0 ≤ C)
    (W : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (S : Set ℍ) (hS : MeasurableSet S) (hstrip : S ⊆ AsymptoticMassTransport.strip)
    [IsFiniteMeasure ((volume : Measure ℍ).restrict S)]
    (u : ℍ → ℍ) (hu : Measurable u) (c : ℍ → ℂ)
    (hcmeas : AEStronglyMeasurable c ((volume : Measure ℍ).restrict S))
    (hc : ∀ᵐ z ∂((volume : Measure ℍ).restrict S), ‖c z‖ ≤ C)
    (hregion : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      Y ≤ (u z).im ∧ Y ≤ z.im ∧ (u z).im ≤ H ∧ z.im ≤ H)
    (hact : ∀ n, W (liftedMode h n hε) =ᵐ[volume] S.indicator
      (fun z => c z * (u z).im * unitRepresentative (2*h) 0 n ε (cylinder (u z)))) :
    liftedTrace h hε W =
      (∫ z in S, c z * ((u z).im*z.im : ℝ) * fourierKernel h ε (u z) z).re := by
  have hh := hasSum_integral_kernel h hε hY hC u id hu measurable_id c hcmeas hc hregion
  have hr := Complex.hasSum_re hh
  rw [liftedTrace_eq_sum]
  have hd (n : ℕ) : (⟪W (liftedMode h n hε),liftedMode h n hε⟫_ℂ).re =
      (∫ z in S, c z * hyperbolicKernelTerm h n ε (u z) z).re := by
    calc
      _ = (⟪liftedMode h n hε,W (liftedMode h n hε)⟫_ℂ).re :=
        inner_re_symm (𝕜:=ℂ) _ _
      _ = _ := congrArg Complex.re (branch_diagonal_integral h n hε W S hS hstrip u c (hact n))
  simp only [hd]
  exact hr.tsum_eq

#print axioms liftedTrace_eq_sum
#print axioms branch_diagonal_integral
#print axioms branch_trace_integral

end AsymptoticUnweightedKernel
