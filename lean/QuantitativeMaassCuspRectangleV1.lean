module

public import QuantitativeMaassCuspHeightAverageV1
public import QuantitativeMaassHyperbolicIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

def upperRectangle (l r a b : ℝ) : Set ℍ :=
  {Z | (Z.re,Z.im)∈Icc l r ×ˢ Icc a b}

theorem upperRectangle_measurable (l r a b : ℝ) : MeasurableSet (upperRectangle l r a b) :=
  (isClosed_Icc.prod isClosed_Icc).measurableSet.preimage
    (continuous_re.prodMk continuous_im).measurable

theorem upperRectangle_compact (l r a b : ℝ) (ha : 0<a) : IsCompact (upperRectangle l r a b) := by
  have hc : ContinuousOn cartesianLift (Icc l r ×ˢ Icc a b) := by
    intro Z hZ
    exact (cartesianLift_continuousAt Z (ha.trans_le hZ.2.1)).continuousWithinAt
  have he : upperRectangle l r a b=cartesianLift '' (Icc l r ×ˢ Icc a b) := by
    ext Z
    constructor
    · intro hZ
      refine ⟨(Z.re,Z.im),hZ,?_⟩
      rw [cartesianLift_positive _ Z.im_pos]
      rfl
    · rintro ⟨W,hW,rfl⟩
      have hp := ha.trans_le hW.2.1
      change ((cartesianLift W).re,(cartesianLift W).im)∈Icc l r ×ˢ Icc a b
      rw [cartesianLift_positive W hp]
      exact hW
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hc

/-- Exact hyperbolic rectangle integral in Cartesian coordinates. No
regularity assumption is needed for this change-of-measure identity. -/
theorem integral_upperRectangle (l r a b : ℝ) (ha : 0<a) (F : ℍ → ℂ) :
    (∫ Z in upperRectangle l r a b, F Z)=
      ∫ W in Icc l r ×ˢ Icc a b, F (cartesianLift W)/(W.2:ℂ)^2 := by
  classical
  let S := Icc l r ×ˢ Icc a b
  let G : MaassDifferential.Point → ℂ := S.indicator (fun W => F (cartesianLift W))
  have hs : Function.support G⊆{W | 0<W.2} := by
    intro W hW
    have hmem : W∈S := by
      by_contra hn
      exact hW (Set.indicator_of_notMem hn _)
    exact ha.trans_le hmem.2.1
  have hu : upperFunction G=(upperRectangle l r a b).indicator F := by
    funext Z
    have hc : cartesianLift (Z.re,Z.im)=Z := by
      rw [cartesianLift_positive _ Z.im_pos]
      rfl
    by_cases hZ : (Z.re,Z.im)∈S
    · change S.indicator (fun W => F (cartesianLift W)) (Z.re,Z.im)=_
      rw [Set.indicator_of_mem hZ,Set.indicator_of_mem (show Z∈upperRectangle l r a b from hZ),hc]
    · change S.indicator (fun W => F (cartesianLift W)) (Z.re,Z.im)=_
      rw [Set.indicator_of_notMem hZ,
        Set.indicator_of_notMem (show Z∉upperRectangle l r a b from hZ)]
  have hg : (fun W => G W/(W.2:ℂ)^2)=S.indicator (fun W => F (cartesianLift W)/(W.2:ℂ)^2) := by
    funext W
    by_cases hW : W∈S
    · simp only [G,Set.indicator_of_mem hW]
    · simp only [G,Set.indicator_of_notMem hW,zero_div]
  have h := integral_upper_cartesian_of_support G hs
  rw [hu,hg,integral_indicator (upperRectangle_measurable l r a b),
    integral_indicator (measurableSet_Icc.prod measurableSet_Icc)] at h
  exact h

#print axioms upperRectangle_compact
#print axioms integral_upperRectangle

end QuantitativeMaass
