module

public import QuantitativeMaassPoincareChartExtensionV1
public import QuantitativeMaassPoincareGraphV1
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem upperSeedExtension_positive (u : Point → ℂ) (Z : Point) (hZ : 0<Z.2) :
    upperSeedExtension (upperFunction u) Z=u Z := by
  have hh := congrFun (upperSeedExtension_represents (upperFunction u)) (⟨⟨Z.1,Z.2⟩,hZ⟩:ℍ)
  exact hh

/-- Compact upper-half-plane seeds have globally smooth zero extensions;
their support is separated from the singular boundary. -/
theorem upperSeedExtension_smooth (u : SmoothUpperSeed) :
    ContDiff ℝ ∞ (upperSeedExtension (upperFunction u.toFun)) := by
  rw [contDiff_iff_contDiffAt]
  intro Z
  by_cases hZ : Z∈tsupport (upperSeedExtension (upperFunction u.toFun))
  · have hz := upperSeedExtension_support_positive (upperFunction u.toFun) u.compact hZ
    have hn : {W : Point | 0<W.2}∈𝓝 Z :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hz
    apply (u.smooth.contDiffAt hn).congr_of_eventuallyEq
    filter_upwards [hn] with W hW
    exact upperSeedExtension_positive u.toFun W hW
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hZ)

/-- The actual smooth compact seed admits a finite global coordinate
Lipschitz constant after zero extension. -/
theorem upperSeedExtension_lipschitz (u : SmoothUpperSeed) :
    ∃ K : NNReal,LipschitzWith K (upperSeedExtension (upperFunction u.toFun)) :=
  ContDiff.lipschitzWith_of_hasCompactSupport
    (upperSeedExtension_compact (upperFunction u.toFun) u.compact)
    (upperSeedExtension_smooth u) (by simp)

#print axioms upperSeedExtension_positive
#print axioms upperSeedExtension_smooth
#print axioms upperSeedExtension_lipschitz

end QuantitativeMaass
