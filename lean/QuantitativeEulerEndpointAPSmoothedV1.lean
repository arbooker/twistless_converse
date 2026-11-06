module

public import QuantitativeEulerEndpointAPKernelsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset ArithmeticFunction ArithmeticFunction.vonMangoldt

def nonprimeError {M : ℕ} (a : ZMod M) (n : ℕ) : ℝ :=
  (if n.Prime then 0 else residueClass a n)/(n : ℝ)

theorem nonprimeError_nonneg {M : ℕ} (a : ZMod M) (n : ℕ) : 0≤nonprimeError a n := by
  unfold nonprimeError
  split_ifs <;> positivity [residueClass_nonneg a n]

theorem nonprimeError_summable {M : ℕ} (a : ZMod M) : Summable (nonprimeError a) :=
  summable_residueClass_non_primes_div a

theorem residue_le_primeLog_add_error {M : ℕ} (a : ZMod M) {t : ℝ}
    (ht : 0≤t) (n : ℕ) :
    residueClass a n/(n : ℝ)^(1+t)≤primeLogDirichlet a t n+nonprimeError a n := by
  by_cases hp : n.Prime
  · by_cases ha : (n : ZMod M)=a
    · simp [primeLogDirichlet,nonprimeError,residueClass,hp,ha,vonMangoldt_apply_prime hp]
    · simp [primeLogDirichlet,nonprimeError,residueClass,hp,ha]
  · simp only [primeLogDirichlet,nonprimeError,hp,false_and,ite_false,zero_add]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · apply div_le_div_of_nonneg_left (residueClass_nonneg a n) (by exact_mod_cast hn)
      conv_lhs => rw [← Real.rpow_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- Removing prime powers costs a fixed constant in the actual residue
class L-series, uniformly as the exponent approaches one. -/
theorem primeLog_pole_lower {M : ℕ} [NeZero M] (a : ZMod M) (ha : IsUnit a) :
    ∃ C : ℝ, 0≤C ∧ ∀ t : ℝ, 0<t → t≤1 →
      (M.totient : ℝ)⁻¹/t-C≤∑' n, primeLogDirichlet a t n := by
  obtain ⟨C₀,hC₀⟩ := LSeries_residueClass_lower_bound ha
  let H := ∑' n, nonprimeError a n
  have hH : 0≤H := tsum_nonneg (nonprimeError_nonneg a)
  refine ⟨|C₀|+H,add_nonneg (abs_nonneg _) hH,?_⟩
  intro t ht ht1
  have hbase := hC₀ (x := 1+t) (show 1+t∈Set.Ioc (1 : ℝ) 2 by constructor <;> linarith)
  simp only [add_sub_cancel_left] at hbase
  have hupper := (residueDirichlet_summable a ht).tsum_le_tsum (residue_le_primeLog_add_error a ht.le) ((primeLogDirichlet_summable a ht).add (nonprimeError_summable a))
  rw [Summable.tsum_add (primeLogDirichlet_summable a ht) (nonprimeError_summable a)] at hupper
  have hCabs := le_abs_self C₀
  dsimp only [H] at *
  linarith

/-- Quantitative smoothed reciprocal mass in every unit residue class.
The proof uses the actual L-series pole and the proved dyadic kernel bound;
no quantitative prime-density or reciprocal-mass hypothesis is assumed. -/
theorem primeDirichlet_dyadic_lower {M : ℕ} [NeZero M] (a : ZMod M) (ha : IsUnit a) :
    ∃ C : ℝ, 0≤C ∧ ∀ J : ℕ,
      (M.totient : ℝ)⁻¹*(J : ℝ)/2-C≤∑' n, primeDirichlet a (dyadic J) n := by
  obtain ⟨C,hC,hpole⟩ := primeLog_pole_lower a ha
  refine ⟨C,hC,fun J => ?_⟩
  have hterm (j : ℕ) : (M.totient : ℝ)⁻¹-C*dyadic j≤
      dyadic j*(∑' n, primeLogDirichlet a (dyadic j) n) := by
    have h := mul_le_mul_of_nonneg_left (hpole (dyadic j) (dyadic_pos j) (dyadic_le_one j))
      (dyadic_pos j).le
    rw [mul_sub,mul_div_cancel₀ _ (dyadic_pos j).ne'] at h
    nlinarith
  have hs := sum_le_sum (s := range J) (fun j _ => hterm j)
  simp only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,← mul_sum] at hs
  have hCsum := mul_le_mul_of_nonneg_left (sum_dyadic_le_two J) hC
  have hupper := dyadic_primeLog_sum_bound a J
  nlinarith

#print axioms primeLog_pole_lower
#print axioms primeDirichlet_dyadic_lower
end QuantitativeEulerEndpointAP
