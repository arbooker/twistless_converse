module

public import QuantitativeMaassEnergySupportV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

/-- Exact covariance plus a common locally finite compact-orbit set allows
periodization through the energy pairing with an invariant first argument. -/
theorem hyperbolicEnergy_poincare_right (N : ℕ) {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport (upperFunction v))
    (hinv : ∀ g : gamma N, ∀ z, upperFunction u (g•z)=upperFunction u z)
    (Z : Point) (hZ : 0<Z.2) :
    hyperbolicEnergy u (congruencePoincareCartesian N v) Z=
      poincareSum (G := gamma N) (upperEnergy u v) (cartesianLift Z) := by
  obtain ⟨S,U,hU,hS⟩ := compact_orbit_locally_finite (G := gamma N)
    (tsupport (upperFunction v)) hc (cartesianLift Z)
  have hout (y : ℍ) (hy : y∈U) (g : gamma N) (hg : g∉S) : upperFunction v (g•y)=0 := by
    by_contra hn
    exact hS y hy g hg (subset_tsupport (upperFunction v) hn)
  have heout (y : ℍ) (hy : y∈U) (g : gamma N) (hg : g∉S) : upperEnergy u v (g•y)=0 := by
    by_contra hn
    exact hS y hy g hg (upperEnergy_support_right u v hn)
  have he : congruencePoincareCartesian N v =ᶠ[𝓝 Z]
      fun W => ∑ g∈S, v (integralCuspChart (representative g) W) := by
    filter_upwards [(cartesianLift_continuousAt Z hZ).preimage_mem_nhds hU,
      (isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW hpos
    change poincareSum (G := gamma N) (upperFunction v) (cartesianLift W)=_
    rw [show poincareSum (G := gamma N) (upperFunction v) (cartesianLift W)=
      ∑ g∈S, upperFunction v (g•cartesianLift W) from tsum_eq_sum (hout _ hW)]
    exact Finset.sum_congr rfl (fun g _ => congruence_pullback_cartesian N v g W hpos)
  rw [hyperbolicEnergy_congr_right he,
    hyperbolicEnergy_finset_sum_right S u
      (fun g W => v (integralCuspChart (representative g) W))
      (fun g _ => integralCuspChart_pullback_smooth (representative g) hv) hZ]
  rw [show poincareSum (G := gamma N) (upperEnergy u v) (cartesianLift Z)=
    ∑ g∈S, upperEnergy u v (g•cartesianLift Z) from
      tsum_eq_sum (heout _ (mem_of_mem_nhds hU))]
  apply Finset.sum_congr rfl
  intro g _
  have hi : u ∘ integralCuspChart (representative g)=ᶠ[𝓝 Z] u := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW
    change u (integralCuspChart (representative g) W)=u W
    rw [← congruence_pullback_cartesian N u g W hW,hinv,upperFunction_cartesianLift hW]
  calc
    _ = hyperbolicEnergy (u ∘ integralCuspChart (representative g))
        (v ∘ integralCuspChart (representative g)) Z :=
      hyperbolicEnergy_congr_left hi.symm
    _ = hyperbolicEnergy u v (integralCuspChart (representative g) Z) :=
      hyperbolicEnergy_integralCuspChart (representative g) hu hv hZ
    _ = _ := (congruence_pullback_cartesian N (hyperbolicEnergy u v) g Z hZ).symm

theorem upperEnergy_poincare_right (N : ℕ) {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport (upperFunction v))
    (hinv : ∀ g : gamma N, ∀ z, upperFunction u (g•z)=upperFunction u z) :
    upperEnergy u (congruencePoincareCartesian N v)=
      poincareSum (G := gamma N) (upperEnergy u v) := by
  funext z
  change hyperbolicEnergy u (congruencePoincareCartesian N v) (z.re,z.im)=_
  rw [hyperbolicEnergy_poincare_right N hu hv hc hinv _ z.im_pos,
    cartesianLift_positive _ z.im_pos]
  rfl

#print axioms upperEnergy_poincare_right

end QuantitativeMaass
