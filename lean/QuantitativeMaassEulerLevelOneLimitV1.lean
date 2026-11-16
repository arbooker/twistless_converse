module

public import QuantitativeMaassEulerLevelOneUpperV1
public import QuantitativeMaassTerminalWindowFiniteV1
public import QuantitativeNinaMaassEigenSolutionsV1
public import QuantitativeMaassWindowConsequencesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set Filter QuantitativeConcreteGoals
open scoped Topology

namespace QuantitativeMaass

theorem maass_level_one_admissible : GridAdmissibleGap.Admissible 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro p hp _ hd
  have hl := Nat.le_of_dvd (by norm_num : 0 < 1) hd
  have hp2 := hp.two_le
  nlinarith

theorem maass_level_one_coefficient :
    AsymptoticTotalNewCorner.arithmeticCoefficient 1 = 1 / 12 := by
  simp [AsymptoticTotalNewCorner.arithmeticCoefficient, Subgroup.relIndex_self]

/-- The complete literal Euler-product window theorem at level one.
The general-level upper trace estimate is not assumed here. -/
theorem originalLevelOneWindow_limit (σ : ℕ) (hσ : σ = 0 ∨ σ = 1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    MaassWindowClaim 1 σ ε := by
  have hfinite := EulerHilbert.Nonzero.admissible_originalWindow_eventually_finite
    1 maass_level_one_admissible σ ε
  refine ⟨hfinite, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro c hc
    let d := (c + AsymptoticTotalNewCorner.arithmeticCoefficient 1) / 2
    have hcd : c < d := by dsimp [d]; linarith
    have hd : d < AsymptoticTotalNewCorner.arithmeticCoefficient 1 := by
      dsimp [d]; linarith
    have hl := QuantitativeNinaMaass.original_maass_solution_ncard_lower
      1 maass_level_one_admissible σ hσ ε hε hproduct hfinite d hd
    filter_upwards [hl, hε, eventually_gt_atTop (0 : ℝ)] with t ht he ht0
    exact hcd.trans_le ((le_div_iff₀ (mul_pos ht0 he.1)).mpr ht)
  · intro c hc
    rw [maass_level_one_coefficient] at hc
    have hu := originalLevelOneWindow_eventual_upper σ ε hε hproduct
      (c - 1 / 12) (by linarith)
    simpa only [add_sub_cancel] using hu

theorem originalLevelOneWindow_parity_sum (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t : ℝ =>
      (((maassWindow 1 0 t (ε t)).ncard + (maassWindow 1 1 t (ε t)).ncard : ℕ) : ℝ) /
        (t * ε t)) atTop (𝓝 (1 / 6)) := by
  have h := (maassWindow_parity_sum 1 ε
    (originalLevelOneWindow_limit 0 (Or.inl rfl) ε hε hproduct)
    (originalLevelOneWindow_limit 1 (Or.inr rfl) ε hε hproduct)).2
  norm_num [maass_level_one_coefficient] at h ⊢
  exact h

theorem originalLevelOneWindow_pointwise (σ : ℕ) (hσ : σ = 0 ∨ σ = 1) :
    (∀ᶠ r in atTop, (maassWindow 1 σ r 0).Finite) ∧
    Tendsto (fun r : ℝ => ((maassWindow 1 σ r 0).ncard : ℝ) / r)
      atTop (𝓝 0) :=
  maassWindow_pointwise_of_canonicalWidth 1 σ
    (originalLevelOneWindow_limit σ hσ canonicalWidth canonicalWidth_eventually_unit
      canonicalWidth_properties.2.2)

#print axioms maass_level_one_admissible
#print axioms maass_level_one_coefficient
#print axioms originalLevelOneWindow_limit
#print axioms originalLevelOneWindow_parity_sum
#print axioms originalLevelOneWindow_pointwise

end QuantitativeMaass
