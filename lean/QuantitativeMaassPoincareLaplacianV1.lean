module

public import QuantitativeMaassLaplacianSupportV1
public import QuantitativeMaassPoincareQuotientDenseV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

theorem compact_orbit_locally_finite {G A : Type*} [Group G] [TopologicalSpace A]
    [LocallyCompactSpace A] [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (K : Set A) (hK : IsCompact K) (x : A) :
    ∃ S : Finset G, ∃ U∈𝓝 x, ∀ y∈U, ∀ g∉S, g•y∉K := by
  classical
  obtain ⟨L,hL,hLx⟩ := exists_compact_mem_nhds x
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) hL hK
  refine ⟨hf.toFinset,L,hLx,?_⟩
  intro y hy g hg hgy
  exact hg (hf.mem_toFinset.mpr ⟨g•y,⟨y,hy,rfl⟩,hgy⟩)

theorem congruence_pullback_cartesian (N : ℕ) (u : Point → ℂ) (g : gamma N)
    (Z : Point) (hZ : 0<Z.2) :
    upperFunction u (g•cartesianLift Z)=u (integralCuspChart (representative g) Z) := by
  have he : representative g • cartesianLift Z=g•cartesianLift Z := by
    rw [← integralLabel_action,representative_label]
    rfl
  rw [← he]
  exact upperFunction_integral_action u (representative g) Z hZ

/-- The literal projective Poincaré series commutes with the actual
hyperbolic Laplacian. The proof uses one locally finite compact-orbit set
for both differential expressions, followed by proved chart covariance. -/
theorem hyperbolic_congruencePoincareCartesian (N : ℕ) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (hc : HasCompactSupport (upperFunction u))
    (Z : Point) (hZ : 0<Z.2) :
    hyperbolic (congruencePoincareCartesian N u) Z=
      poincareSum (G := gamma N) (upperLaplacian u) (cartesianLift Z) := by
  obtain ⟨S,U,hU,hS⟩ := compact_orbit_locally_finite (G := gamma N)
    (tsupport (upperFunction u)) hc (cartesianLift Z)
  have hout (y : ℍ) (hy : y∈U) (g : gamma N) (hg : g∉S) : upperFunction u (g•y)=0 := by
    by_contra hn
    exact hS y hy g hg (subset_tsupport (upperFunction u) hn)
  have hdout (y : ℍ) (hy : y∈U) (g : gamma N) (hg : g∉S) : upperLaplacian u (g•y)=0 := by
    by_contra hn
    exact hS y hy g hg (upperLaplacian_support u hn)
  have he : congruencePoincareCartesian N u =ᶠ[𝓝 Z]
      fun W => ∑ g∈S, u (integralCuspChart (representative g) W) := by
    filter_upwards [(cartesianLift_continuousAt Z hZ).preimage_mem_nhds hU,
      (isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW hpos
    change poincareSum (G := gamma N) (upperFunction u) (cartesianLift W)=_
    rw [show poincareSum (G := gamma N) (upperFunction u) (cartesianLift W)=
      ∑ g∈S, upperFunction u (g•cartesianLift W) from tsum_eq_sum (hout _ hW)]
    exact Finset.sum_congr rfl (fun g _ => congruence_pullback_cartesian N u g W hpos)
  rw [hyperbolic_congr_eventually he,
    hyperbolic_finset_sum S (fun g W => u (integralCuspChart (representative g) W))
      (fun g _ => integralCuspChart_pullback_smooth (representative g) hu) Z hZ]
  rw [show poincareSum (G := gamma N) (upperLaplacian u) (cartesianLift Z)=
    ∑ g∈S, upperLaplacian u (g•cartesianLift Z) from
      tsum_eq_sum (hdout _ (mem_of_mem_nhds hU))]
  apply Finset.sum_congr rfl
  intro g _
  change hyperbolic (u ∘ integralCuspChart (representative g)) (Z.1,Z.2)=_
  rw [hyperbolic_integralCuspChart (representative g) hu Z.1 Z.2 hZ]
  exact (congruence_pullback_cartesian N (hyperbolic u) g Z hZ).symm

theorem upperLaplacian_congruencePoincareCartesian (N : ℕ) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (hc : HasCompactSupport (upperFunction u)) :
    upperLaplacian (congruencePoincareCartesian N u)=
      poincareSum (G := gamma N) (upperLaplacian u) := by
  funext z
  change hyperbolic (congruencePoincareCartesian N u) (z.re,z.im)=_
  rw [hyperbolic_congruencePoincareCartesian N hu hc _ z.im_pos,
    cartesianLift_positive _ z.im_pos]
  rfl

theorem poincareLaplacian_memLp (N : ℕ) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (hc : HasCompactSupport (upperFunction u)) :
    MemLp (upperLaplacian (congruencePoincareCartesian N u)) 2 (quotientMeasure N) := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  rw [upperLaplacian_congruencePoincareCartesian N hu hc]
  exact poincareSum_memLp volume (fun g => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) (upperLaplacian u)
    (upperLaplacian_continuous hu) (upperLaplacian_compact u hc)

#print axioms upperLaplacian_congruencePoincareCartesian
#print axioms poincareLaplacian_memLp

end QuantitativeMaass
