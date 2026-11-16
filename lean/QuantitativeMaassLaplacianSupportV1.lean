module

public import QuantitativeMaassLaplacianLocalV1
public import QuantitativeMaassPoincareChartExtensionV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem upperFunction_cartesianLift {u : Point → ℂ} {Z : Point} (hZ : 0<Z.2) :
    upperFunction u (cartesianLift Z)=u Z := by
  rw [cartesianLift_positive Z hZ]
  rfl

/-- Taking the literal hyperbolic Laplacian cannot enlarge upper-half-plane
support. No global smoothness outside the positive-height chart is needed. -/
theorem upperLaplacian_support (u : Point → ℂ) :
    Function.support (upperLaplacian u) ⊆ tsupport (upperFunction u) := by
  intro z hz
  by_contra hn
  have hcart : cartesianLift (z.re,z.im)=z := by
    rw [cartesianLift_positive _ z.im_pos]
    rfl
  have ht : Tendsto cartesianLift (𝓝 (z.re,z.im)) (𝓝 z) := by
    simpa only [ContinuousAt,hcart] using cartesianLift_continuousAt (z.re,z.im) z.im_pos
  have he := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    ht
  have he' : u=ᶠ[𝓝 (z.re,z.im)] 0 := by
    filter_upwards [he,(isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos]
      with W hW hpos
    simpa only [Function.comp_apply,upperFunction_cartesianLift hpos,Pi.zero_apply] using hW
  have hl := hyperbolic_congr_eventually he'
  have hzero : hyperbolic (0 : Point → ℂ) (z.re,z.im)=0 := by
    simp [hyperbolic,euclidean]
  exact hz (hl.trans hzero)

theorem upperLaplacian_compact (u : Point → ℂ) (hc : HasCompactSupport (upperFunction u)) :
    HasCompactSupport (upperLaplacian u) :=
  hc.of_isClosed_subset isClosed_closure (closure_minimal (upperLaplacian_support u) isClosed_closure)

/-- Smoothness of the literal differential expression on its genuine
positive-height domain. -/
theorem hyperbolic_contDiffOn {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) :
    ContDiffOn ℝ ∞ (hyperbolic u) {Z | 0<Z.2} := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hX := dir_contDiffOn (dir_contDiffOn hu hs e₁) hs e₁
  have hY := dir_contDiffOn (dir_contDiffOn hu hs e₂) hs e₂
  have he : EqOn (hyperbolic u) (fun Z => -(Z.2^2) • (X (X u) Z+Y (Y u) Z))
      {Z : Point | 0<Z.2} := by
    intro Z hZ
    change hyperbolic u Z=-(Z.2^2) • (X (X u) Z+Y (Y u) Z)
    rw [XX_eq_deriv hu hs hZ,YY_eq_deriv hu hs hZ]
    rfl
  apply ContDiffOn.congr _ he
  exact (contDiffOn_snd.pow 2).neg.smul (hX.add hY)

theorem upperLaplacian_continuous {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) : Continuous (upperLaplacian u) :=
  (hyperbolic_contDiffOn hu).continuousOn.comp_continuous
    upperCoordinates_openEmbedding.continuous (fun z => z.im_pos)

#print axioms upperLaplacian_compact
#print axioms upperLaplacian_continuous

end QuantitativeMaass
