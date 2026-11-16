module

public import QuantitativeMaassPoincareChartExtensionV1
public import Mathlib.Geometry.Manifold.SmoothApprox

set_option autoImplicit false
@[expose] public noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Uniform smooth approximation of literal upper-half-plane seeds,
preserving their support. The Cartesian smooth functions remain compactly
supported inside the positive-height chart. No boundary integrability
assumption on an extended hyperbolic measure is used. -/
theorem upper_seed_uniform_smooth_approx (f : ℍ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (ε : ℝ) (hε : 0<ε) :
    ∃ u : Point → ℂ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      tsupport u ⊆ {Z : Point | 0<Z.2} ∧
      HasCompactSupport (upperFunction u) ∧
      Function.support (upperFunction u) ⊆ Function.support f ∧
      ∀ z : ℍ, ‖upperFunction u z-f z‖<ε := by
  obtain ⟨u,hu,ha,hs⟩ := (upperSeedExtension_continuous f hf hc).exists_contDiff_approx
    ⊤ (ε := fun _ => ε) continuous_const (fun _ => hε)
  have hs' : Function.support (upperFunction u) ⊆ Function.support f := by
    intro z hz
    have h := hs (show u (upperCoordinates z)≠0 from hz)
    have he := congrFun (upperSeedExtension_represents f) z
    change upperSeedExtension f (upperCoordinates z)≠0 at h
    change upperSeedExtension f (upperCoordinates z)=f z at he
    rw [he] at h
    exact h
  refine ⟨u,hu,(upperSeedExtension_compact f hc).mono hs,
    (closure_mono hs).trans (upperSeedExtension_support_positive f hc),hc.mono hs',hs',?_⟩
  intro z
  have h := ha (upperCoordinates z)
  have he := congrFun (upperSeedExtension_represents f) z
  change upperSeedExtension f (upperCoordinates z)=f z at he
  rw [he,dist_eq_norm] at h
  exact h

#print axioms upper_seed_uniform_smooth_approx

end QuantitativeMaass
