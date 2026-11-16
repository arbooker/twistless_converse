module

public import QuantitativeMaassStrongScaleV1

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass.Strong

/-- A cusp height whose logarithm dominates the propagation radius but
remains sublogarithmic in the spectral parameter. Unlike a large fixed
power of `t`, it also pays for the `exp (30 * L)` geometric loss. -/
def compactCuspHeight (t : ℝ) : ℝ := Real.exp (strongScale t)

theorem compactCuspHeight_pos (t : ℝ) : 0 < compactCuspHeight t := Real.exp_pos _

theorem log_compactCuspHeight (t : ℝ) :
    Real.log (compactCuspHeight t) = strongScale t := Real.log_exp _

theorem compactCuspHeight_tendsto : Tendsto compactCuspHeight atTop atTop :=
  Real.tendsto_exp_atTop.comp strongScale_tendsto

/-- Every fixed polynomial loss in the chosen height, together with a
fixed exponential propagation loss, preserves the square-root saving. -/
theorem compact_height_geometric_cost (ε : ℝ → ℝ) (A B C : ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => C * Real.sqrt t *
      Real.exp (A * propagation (slowScale t) (ε t) +
        B * Real.log (compactCuspHeight t)) / (t * ε t)) atTop (𝓝 0) := by
  have hcost := ((shrinking_propagation_div_log ε hε hproduct).const_mul A).add
    (strongScale_div_log.const_mul B)
  have h := (sqrt_geometric_cost_tendsto ε
    (fun t => A * propagation (slowScale t) (ε t) + B * strongScale t)
    hε hproduct (by
      simpa only [mul_zero, add_zero, add_div, mul_div_assoc] using hcost)).const_mul C
  simp only [mul_zero] at h
  simpa only [log_compactCuspHeight, mul_assoc, mul_div_assoc] using h

/-- The sharp inverse-height tail is negligible at the theorem's original
width hypothesis, even after an arbitrary fixed propagation loss. -/
theorem compact_height_tail_cost (ε : ℝ → ℝ) (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => C * Real.exp (A * propagation (slowScale t) (ε t)) /
      (compactCuspHeight t * ε t)) atTop (𝓝 0) := by
  have h := (chosen_propagation_excess slowScale ε A 1 hA (by norm_num)
    slowScale_tendsto hε hproduct).const_mul C
  simp only [mul_zero, one_mul] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [hε] with t he
    exact div_nonneg (mul_nonneg hC (Real.exp_pos _).le)
      (mul_pos (compactCuspHeight_pos t) he).le
  · filter_upwards [hε, slowScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
      with t he ht
    have hs : slowScale t ≤ strongScale t := by
      dsimp only [strongScale]
      nlinarith
    have heq : C * Real.exp (A * propagation (slowScale t) (ε t)) /
        (compactCuspHeight t * ε t) =
        C * (Real.exp (A * propagation (slowScale t) (ε t) - strongScale t) / ε t) := by
      rw [Real.exp_sub]
      dsimp only [compactCuspHeight]
      ring
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ hC
    apply div_le_div_of_nonneg_right _ he.le
    exact Real.exp_le_exp.mpr (sub_le_sub_left hs _)

/-- The new linear-height centering loss is covered by the same cutoff. -/
theorem compact_height_centering_cost (ε : ℝ → ℝ) (A C : ℝ) (hC : 0 ≤ C)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => C * Real.sqrt t * (ε t)^2 *
      Real.exp (A * propagation (slowScale t) (ε t)) * compactCuspHeight t /
      (t * ε t)) atTop (𝓝 0) := by
  have hpos := hε.mono (fun _ h => h.1)
  have h := compact_height_geometric_cost ε A 1 C hpos hproduct
  apply squeeze_zero' _ _ h
  · filter_upwards [hε, eventually_gt_atTop (0 : ℝ)] with t he ht
    have hheight := compactCuspHeight_pos t
    have hepos := he.1
    positivity
  · filter_upwards [hε, eventually_gt_atTop (0 : ℝ)] with t he ht
    have hheight := (compactCuspHeight_pos t).le
    have he2 : (ε t)^2 ≤ 1 := by nlinarith [sq_nonneg (ε t - 1)]
    rw [one_mul, Real.exp_add, Real.exp_log (compactCuspHeight_pos t)]
    apply div_le_div_of_nonneg_right _ (mul_pos ht he.1).le
    calc
      _ ≤ C * Real.sqrt t * 1 * Real.exp (A * propagation (slowScale t) (ε t)) *
          compactCuspHeight t := by gcongr
      _ = _ := by ring

#print axioms compactCuspHeight_pos
#print axioms log_compactCuspHeight
#print axioms compactCuspHeight_tendsto
#print axioms compact_height_geometric_cost
#print axioms compact_height_tail_cost
#print axioms compact_height_centering_cost

end QuantitativeMaass.Strong
