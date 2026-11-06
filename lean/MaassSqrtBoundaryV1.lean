module

public import MaassSqrtRescalingV1
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Positivity

set_option autoImplicit false

@[expose] public section

open Set Filter
open scoped Topology

namespace MaassSqrtRescaling

/-- Only boundedness of k and k' at positive large arguments is needed
for the exponentially weighted infinity condition in both comparisons. -/
theorem weighted_boundary_tendsto
    (k k₁ : ℝ → ℝ) {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hk : ∀ x ∈ Ici (1 : ℝ), ‖k x‖ ≤ C)
    (hk₁ : ∀ x ∈ Ici (1 : ℝ), ‖k₁ x‖ ≤ C) :
    Tendsto (fun x => Real.exp (-a*x) * (W₁ k k₁ x + a * W k x)) atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-a*x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos ha) tendsto_id)
  have he₁ : Tendsto (fun x : ℝ => x * Real.exp (-a*x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  have hlim : Tendsto (fun x : ℝ =>
      C * Real.exp (-a*x) + ((1+a)*C) * (x * Real.exp (-a*x))) atTop (𝓝 0) := by
    simpa using (he.const_mul C).add (he₁.const_mul ((1+a)*C))
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hsx : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx)
  have hsq : |Real.sqrt x| = Real.sqrt x := abs_of_nonneg (Real.sqrt_nonneg x)
  have hv : ‖W k x‖ ≤ x*C := by
    dsimp only [W]
    rw [norm_mul, Real.norm_eq_abs, hsq]
    exact mul_le_mul hsx (hk x hx) (norm_nonneg _) hx0.le
  have hv₁ : ‖W₁ k k₁ x‖ ≤ C + x*C := by
    dsimp only [W₁]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, show ‖2 * Real.sqrt x‖ = 2 * Real.sqrt x from
        (Real.norm_eq_abs _).trans (abs_of_pos (by positivity))]
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt x)).mpr
      have hh := hk x hx
      nlinarith
    · rw [norm_mul, Real.norm_eq_abs, hsq]
      exact mul_le_mul hsx (hk₁ x hx) (norm_nonneg _) hx0.le
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hb : ‖W₁ k k₁ x + a * W k x‖ ≤ C + (1+a)*x*C := by
    calc
      _ ≤ ‖W₁ k k₁ x‖ + ‖a * W k x‖ := norm_add_le _ _
      _ ≤ (C+x*C) + a*(x*C) := by
        rw [norm_mul, show ‖a‖ = a from (Real.norm_eq_abs a).trans (abs_of_pos ha)]
        exact add_le_add hv₁ (mul_le_mul_of_nonneg_left hv ha.le)
      _ = _ := by ring
  calc
    _ ≤ Real.exp (-a*x) * (C + (1+a)*x*C) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

#print axioms weighted_boundary_tendsto

end MaassSqrtRescaling
