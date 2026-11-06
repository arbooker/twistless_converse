module

public import MaassODEComparisonV1
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

@[expose] public section

open Set Filter
open scoped Topology

namespace MaassODEComparison

/-- On a terminal interval, the product v*v' is increasing if v*v'' is
nonnegative. A zero product limit and eventual positivity then force
positivity everywhere on the interval. All inputs are explicit here and
must be paid when instantiated with an actual Bessel integral. -/
theorem pos_of_eventual_pos
    (v v₁ v₂ : ℝ → ℝ) (b : ℝ)
    (hd : ∀ x ∈ Ici b, HasDerivAt v (v₁ x) x)
    (hd₁ : ∀ x ∈ Ici b, HasDerivAt v₁ (v₂ x) x)
    (hode : ∀ x ∈ Ici b, 0 ≤ v x * v₂ x)
    (hlim : Tendsto (fun x => v x * v₁ x) atTop (𝓝 0))
    (hevent : ∃ R : ℝ, ∀ y ≥ R, 0 < v y)
    {x : ℝ} (hx : b ≤ x) : 0 < v x := by
  have hg (z : ℝ) (hz : z ∈ Ici b) : HasDerivAt (fun w => v w * v₁ w)
      (v₁ z ^ 2 + v z * v₂ z) z := by
    convert (hd z hz).mul (hd₁ z hz) using 1
    ring
  have hm : MonotoneOn (fun z => v z * v₁ z) (Ici b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici b)
    · exact fun z hz => (hg z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hg z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hg z (interior_subset hz)).deriv]
      exact add_nonneg (sq_nonneg _) (hode z (interior_subset hz))
  have hprod (z : ℝ) (hz : z ∈ Ici b) : v z * v₁ z ≤ 0 :=
    nonpos_of_monotoneOn_tendsto (g := fun w => v w * v₁ w) (x := z) hm hlim hz
  have hs (z : ℝ) (hz : z ∈ Ici b) : HasDerivAt (fun w => v w ^ 2)
      (2 * (v z * v₁ z)) z := by
    convert (hd z hz).pow 2 using 1
    ring
  have hanti : AntitoneOn (fun z => v z ^ 2) (Ici b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici b)
    · exact fun z hz => (hs z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hs z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hs z (interior_subset hz)).deriv]
      linarith [hprod z (interior_subset hz)]
  obtain ⟨R,hR⟩ := hevent
  have hn (z : ℝ) (hz : b ≤ z) : v z ≠ 0 := by
    intro hzero
    have hp := hR (max z R) (le_max_right _ _)
    have hh := hanti hz (hz.trans (le_max_left z R)) (le_max_left z R)
    change v (max z R)^2 ≤ v z^2 at hh
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hh
    exact (not_le_of_gt (sq_pos_of_pos hp)) hh
  by_contra hnot
  have hnpos : v x ≤ 0 := le_of_not_gt hnot
  let Y := max x R
  have hxy : x ≤ Y := le_max_left _ _
  have hYpos : 0 < v Y := hR Y (le_max_right _ _)
  have hc : ContinuousOn v (Icc x Y) := by
    intro z hz
    exact (hd z (hx.trans hz.1)).continuousAt.continuousWithinAt
  obtain ⟨z,hz,hzero⟩ := intermediate_value_Icc hxy hc ⟨hnpos,hYpos.le⟩
  exact hn z (hx.trans hz.1) hzero

#print axioms pos_of_eventual_pos

end MaassODEComparison
