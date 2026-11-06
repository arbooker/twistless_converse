module

public import AsymptoticClassicalFourierNormalizationV1
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane Filter Asymptotics Set Complex

/-- Absorb a bounded initial height interval into an exponential-decay
 estimate without changing its exponent. -/
theorem exponential_bound_on_Ici {f : ℝ → ℂ} {c : ℝ}
    (hf : ContinuousOn f (Ici 1))
    (ho : f =O[atTop] (fun t : ℝ => Real.exp (-c * t))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-c * t) := by
  obtain ⟨A, hA, ha⟩ := ho.exists_nonneg
  obtain ⟨R, hR⟩ := eventually_atTop.mp ha.bound
  have hb : ContinuousOn (fun t : ℝ => ‖f t‖ * Real.exp (c * t)) (Icc 1 (max 1 R)) :=
    (hf.mono (fun _ h => h.1)).norm.mul (by fun_prop)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hb
  refine ⟨max A (max B 0), le_trans hA (le_max_left _ _), ?_⟩
  intro t ht
  by_cases htR : R ≤ t
  · have hh := hR t htR
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hh : ‖f t‖ * Real.exp (c * t) ≤ max A (max B 0) :=
      (hB (mem_image_of_mem _ ⟨ht, (le_of_not_ge htR).trans (le_max_right _ _)⟩)).trans
        ((le_max_left B 0).trans (le_max_right A _))
    calc
      ‖f t‖ = (‖f t‖ * Real.exp (c * t)) * Real.exp (-c * t) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
      _ ≤ max A (max B 0) * Real.exp (-c * t) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

theorem axis_tendsto : Tendsto (fun t : ℝ => ofComplex (Complex.I * t)) atTop atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht, ← coe_im]

/-- Every classical cusp form has an exponential bound on the entire
 imaginary ray above height one. -/
theorem cusp_axis_exponential_bound {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ t : ℝ, 1 ≤ t →
      ‖f (ofComplex (Complex.I * t))‖ ≤ C * Real.exp (-c * t) := by
  obtain ⟨c, hc, ho⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  rw [(CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero] at ho
  simp only [sub_zero] at ho
  have ha : (fun t : ℝ => f (ofComplex (Complex.I * t)))
      =O[atTop] (fun t : ℝ => Real.exp (-c * t)) := by
    apply (ho.comp_tendsto axis_tendsto).congr' (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [Function.comp_apply, ofComplex_apply_of_im_pos, ht, ← coe_im]
  have hcts : ContinuousOn (fun t : ℝ => f (ofComplex (Complex.I * t))) (Ici 1) := by
    exact f.holo'.continuous.comp_continuousOn
      (continuousOn_ofComplex_I_mul.mono (fun t ht => lt_of_lt_of_le zero_lt_one ht))
  obtain ⟨C, hC, hbound⟩ := exponential_bound_on_Ici hcts ha
  exact ⟨C, c, hC, hc, hbound⟩

#print axioms exponential_bound_on_Ici
#print axioms axis_tendsto
#print axioms cusp_axis_exponential_bound

end AsymptoticClassicalLSeries
