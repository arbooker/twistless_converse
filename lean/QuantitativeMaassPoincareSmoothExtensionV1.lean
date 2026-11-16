module

public import QuantitativeMaassLaplacianSupportV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem upperSeedExtension_eqOn (u : Point → ℂ) :
    EqOn (upperSeedExtension (upperFunction u)) u {Z : Point | 0<Z.2} := by
  intro Z hZ
  have h := congrFun (upperSeedExtension_represents (upperFunction u)) (cartesianLift Z)
  simpa only [upperFunction_cartesianLift hZ] using h

/-- A seed smooth on the upper half-plane and compactly supported there has
a genuinely globally smooth Cartesian zero extension. Compactness keeps
the support away from height zero. -/
theorem upperSeedExtension_contDiff {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hc : HasCompactSupport (upperFunction u)) :
    ContDiff ℝ ∞ (upperSeedExtension (upperFunction u)) := by
  rw [contDiff_iff_contDiffAt]
  intro Z
  by_cases hZ : Z∈tsupport (upperSeedExtension (upperFunction u))
  · have hp := upperSeedExtension_support_positive (upperFunction u) hc hZ
    have hs := (isOpen_lt continuous_const continuous_snd).mem_nhds hp
    have he : upperSeedExtension (upperFunction u)=ᶠ[𝓝 Z] u :=
      Filter.eventually_of_mem hs (fun W hW => upperSeedExtension_eqOn u hW)
    exact (hu.contDiffAt hs).congr_of_eventuallyEq he
  · have he := notMem_tsupport_iff_eventuallyEq.mp hZ
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem upperLaplacian_upperSeedExtension {u : Point → ℂ} :
    upperLaplacian (upperSeedExtension (upperFunction u))=upperLaplacian u := by
  funext z
  apply hyperbolic_congr_eventually
  exact Filter.eventually_of_mem
    ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos)
    (fun W hW => upperSeedExtension_eqOn u hW)

#print axioms upperSeedExtension_contDiff

end QuantitativeMaass
