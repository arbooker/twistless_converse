module

public import FinitenessOriginalInputV1
public import Mathlib.Analysis.PSeries

@[expose] public section

set_option autoImplicit false

namespace FinitenessInputBounds

open Complex Filter Set Asymptotics FinitenessOriginalInput FinitenessFiniteOrder

/-- The compact exceptional region and REAL order in the original input
are absorbed into the global integer envelope used by the contour proof. -/
theorem finiteOrder_bound {F : ℂ → ℂ} (hc : Continuous F) (hF : FiniteOrder F) : Bound F := by
  obtain ⟨A,ρ,R,hA,hR,houtside⟩ := hF
  obtain ⟨d,hd⟩ := exists_nat_gt ρ
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hc.norm.continuousOn
  refine ⟨A+|C|+1, by positivity, d, ?_⟩
  intro z
  have hbase : 1 ≤ 1+‖z‖ := by linarith [norm_nonneg z]
  have hp : 1 ≤ (1+‖z‖)^d := one_le_pow₀ hbase
  by_cases hz : R ≤ ‖z‖
  · apply (houtside z hz).trans
    apply Real.exp_le_exp.mpr
    have hpow : (1+‖z‖)^ρ ≤ (1+‖z‖)^d := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hd.le
    nlinarith [mul_nonneg (show 0 ≤ |C|+1 by positivity) (pow_nonneg (by positivity : 0 ≤ 1+‖z‖) d)]
  · have hzball : z ∈ Metric.closedBall (0 : ℂ) R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (le_of_lt (lt_of_not_ge hz))
    have hnorm : ‖F z‖ ≤ C := hC (mem_image_of_mem (fun w => ‖F w‖) hzball)
    calc
      ‖F z‖ ≤ C := hnorm
      _ ≤ |C| := le_abs_self _
      _ ≤ Real.exp ((A+|C|+1)*(1+‖z‖)^d) := by
        have he := Real.add_one_le_exp ((A+|C|+1)*(1+‖z‖)^d)
        nlinarith [abs_nonneg C]

theorem bound_finiteOrder {F : ℂ → ℂ} (hF : Bound F) : FiniteOrder F := by
  obtain ⟨A,hA,d,hd⟩ := hF
  refine ⟨A,(d : ℝ),0,hA,le_rfl,?_⟩
  intro z _
  simpa only [Real.rpow_natCast] using hd z

theorem finiteOrder_iff_bound {F : ℂ → ℂ} (hc : Continuous F) : FiniteOrder F ↔ Bound F :=
  ⟨finiteOrder_bound hc, bound_finiteOrder⟩

theorem bound_shift {F : ℂ → ℂ} (hF : Bound F) (c : ℂ) : Bound (fun z => F (z+c)) := by
  obtain ⟨A,hA,d,hd⟩ := hF
  refine ⟨A*(1+‖c‖)^d, by positivity, d, ?_⟩
  intro z
  apply (hd (z+c)).trans
  apply Real.exp_le_exp.mpr
  have hn : 1+‖z+c‖ ≤ (1+‖c‖)*(1+‖z‖) := by
    nlinarith [norm_add_le z c, norm_nonneg z, norm_nonneg c]
  calc
    A*(1+‖z+c‖)^d ≤ A*((1+‖c‖)*(1+‖z‖))^d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn d) hA
    _ = _ := by rw [mul_pow]; ring

theorem bound_const (c : ℂ) : Bound (fun _ : ℂ => c) := by
  refine ⟨‖c‖,norm_nonneg _,0,?_⟩
  intro z
  simpa only [pow_zero,mul_one] using
    (show ‖c‖ ≤ Real.exp ‖c‖ by linarith [Real.add_one_le_exp ‖c‖])

/-- An individual real polynomial exponent gives absolute convergence on
ANY line to its right by more than one. Positive indices avoid zero powers. -/
theorem absolute_convergence {E : Type*} [NormedAddCommGroup E] {f : ℕ → E} {τ σ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (hσ : τ+1 < σ) :
    Summable (fun n : ℕ => ‖f (n+1)‖ * Real.exp (-σ*Real.log (n+1))) := by
  obtain ⟨C,hC,hbound⟩ := bound_of_isBigO_nat_atTop hf
  have hp : τ-σ < -1 := by linarith
  have hs : Summable (fun n : ℕ => ((n+1 : ℕ):ℝ)^(τ-σ)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hs.mul_left C)
  intro n
  have hn : 0 < ((n+1 : ℕ):ℝ) := by positivity
  have hb : ‖f (n+1)‖ ≤ C*((n+1 : ℕ):ℝ)^τ := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn τ)]
      using hbound (Real.rpow_pos_of_pos hn τ).ne'
  calc
    ‖f (n+1)‖ * Real.exp (-σ*Real.log (n+1)) ≤
        (C*((n+1 : ℕ):ℝ)^τ)*Real.exp (-σ*Real.log (n+1)) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = C*((n+1 : ℕ):ℝ)^(τ-σ) := by
      rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn, mul_assoc, ← Real.exp_add]
      congr 2
      push_cast
      ring

#print axioms finiteOrder_iff_bound
#print axioms absolute_convergence

end FinitenessInputBounds
