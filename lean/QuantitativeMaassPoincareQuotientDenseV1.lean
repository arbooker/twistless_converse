module

public import QuantitativeMaassPoincareDensityV1
public import QuantitativeMaassSubgroupSpaceV1
public import QuantitativeMaassHeckeL2V1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

instance congruence_action_proper (N : ℕ) : ProperlyDiscontinuousSMul (gamma N) ℍ := by
  constructor
  intro K L hK hL
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := SL(2,ℤ)) hK hL
  have hi : Function.Injective (representative (N := N)) := by
    intro a b hab
    apply Subtype.ext
    rw [← representative_label a,← representative_label b,hab]
  apply (hf.preimage hi.injOn).subset
  intro g hg
  have he : (fun z : ℍ => representative g • z)=(fun z : ℍ => g • z) := by
    funext z
    rw [← integralLabel_action,representative_label]
    rfl
  change ((fun z : ℍ => representative g • z) '' K ∩ L).Nonempty
  rw [he]
  exact hg

def congruencePoincareCartesian (N : ℕ) (u : Point → ℂ) (Z : Point) : ℂ :=
  poincareSum (G := gamma N) (upperFunction u) (cartesianLift Z)

/-- The projective periodization is locally a finite sum of literal
integral chart pullbacks. Choosing one representative for each projective
label does not introduce a duplicate central term. -/
theorem congruencePoincareCartesian_eventually_finite (N : ℕ) (u : Point → ℂ)
    (hu : HasCompactSupport (upperFunction u)) (Z : Point) (hZ : 0<Z.2) :
    ∃ S : Finset (gamma N), congruencePoincareCartesian N u =ᶠ[𝓝 Z]
      fun W => ∑ g∈S, u (integralCuspChart (representative g) W) := by
  obtain ⟨S,hS⟩ := poincareSum_eventually_finite (G := gamma N) (upperFunction u) hu
    (cartesianLift Z)
  refine ⟨S,?_⟩
  filter_upwards [hS.comp_tendsto (cartesianLift_continuousAt Z hZ),
    (isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hsum hW
  change poincareSum (G := gamma N) (upperFunction u) (cartesianLift W)=_
  dsimp only [Function.comp_apply] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro g _
  have he : representative g • cartesianLift W=g•cartesianLift W := by
    rw [← integralLabel_action,representative_label]
    rfl
  rw [← he]
  exact upperFunction_integral_action u (representative g) W hW

theorem congruencePoincareCartesian_smooth (N : ℕ) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (hc : HasCompactSupport (upperFunction u)) :
    ContDiffOn ℝ ∞ (congruencePoincareCartesian N u) {Z | 0<Z.2} := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  rw [hs.contDiffOn_iff]
  intro Z hZ
  obtain ⟨S,hS⟩ := congruencePoincareCartesian_eventually_finite N u hc Z hZ
  apply ContDiffAt.congr_of_eventuallyEq _ hS
  exact ((ContDiffOn.sum (s := S) fun g _ =>
    integralCuspChart_pullback_smooth (representative g) hu).contDiffAt (hs.mem_nhds hZ))

theorem congruencePoincareCartesian_represents (N : ℕ) (u : Point → ℂ) (z : ℍ) :
    upperFunction (congruencePoincareCartesian N u) z=
      poincareSum (G := gamma N) (upperFunction u) z := by
  unfold upperFunction congruencePoincareCartesian
  rw [cartesianLift_positive _ z.im_pos]
  rfl

/-- Density of literal smooth compact Poincaré seeds for the actual
projective Gamma0 quotient measure. Normalization and properness are proved
for this action, rather than supplied as analytic hypotheses. -/
theorem congruence_smooth_poincare_dense (N : ℕ) :
    closure (smoothSeedClasses (G := gamma N) (quotientMeasure N))=
      (AutomorphicSpace N : Set (Lp ℂ 2 (quotientMeasure N))) := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  have he := closure_smoothSeedClasses_eq_automorphic_space volume
    (fun g => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
  rw [AutomorphicL2.space_subgroup_top] at he
  exact he

#print axioms congruence_action_proper
#print axioms congruencePoincareCartesian_smooth
#print axioms congruence_smooth_poincare_dense

end QuantitativeMaass
