module

public import QuantitativeMaassCompactSobolevApproxV1
public import QuantitativeMaassQuotientWeightSeedLipschitzV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set Filter UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Strong coordinate Sobolev approximation of the literal orbit weight times
a smooth compact seed. No smoothness hypothesis on the orbit weight is used. -/
theorem quotientWeight_seed_sobolev_approx (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) :
    let f : Point → ℂ := fun Z => (quotientWeightPlane N ε v Z:ℂ)*
      upperSeedExtension (upperFunction w.toFun) Z
    ∃ (L : NNReal) (K : Set ℍ) (u : ℕ → SmoothUpperSeed),IsCompact K ∧
      (∀ n,tsupport (upperFunction (u n).toFun)⊆K) ∧
      (∀ n,ContDiff ℝ ∞ (u n).toFun ∧ HasCompactSupport (u n).toFun ∧
        tsupport (u n).toFun⊆{Z : Point | 0<Z.2} ∧ LipschitzWith L (u n).toFun) ∧
      Tendsto (fun n => ∫ Z,‖(u n).toFun Z-f Z‖^2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ Z,‖fderiv ℝ (u n).toFun Z-fderiv ℝ f Z‖^2) atTop (𝓝 0) ∧
      (∀ᵐ Z ∂(volume : Measure Point),
        Tendsto (fun n => fderiv ℝ (u n).toFun Z) atTop (𝓝 (fderiv ℝ f Z))) := by
  dsimp only
  let f : Point → ℂ := fun Z => (quotientWeightPlane N ε v Z:ℂ)*
    upperSeedExtension (upperFunction w.toFun) Z
  obtain ⟨L,hL⟩ := quotientWeight_seed_lipschitz N hε hv w
  have hc : HasCompactSupport f := (upperSeedExtension_compact _ w.compact).mono
    (Function.support_mul_subset_right _ _)
  have hp : tsupport f⊆{Z : Point | 0<Z.2} :=
    tsupport_mul_subset_right.trans (upperSeedExtension_support_positive _ w.compact)
  exact ⟨L,compact_lipschitz_sobolev_approx hL hc hp⟩

#print axioms quotientWeight_seed_sobolev_approx

end QuantitativeMaass
