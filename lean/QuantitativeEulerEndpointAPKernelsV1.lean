module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset ArithmeticFunction ArithmeticFunction.vonMangoldt LSeries

def dyadic (j : ℕ) : ℝ := (1/2 : ℝ)^j

theorem dyadic_pos (j : ℕ) : 0<dyadic j := by unfold dyadic; positivity

theorem dyadic_le_one (j : ℕ) : dyadic j≤1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem dyadic_succ (j : ℕ) : dyadic (j+1)=dyadic j/2 := by
  simp [dyadic,pow_succ,div_eq_mul_inv]

theorem sum_dyadic_le_two (J : ℕ) : (∑ j∈range J, dyadic j)≤2 := by
  have he : (∑ j∈range J, dyadic j)=2*(1-dyadic J) := by
    induction J with
    | zero => simp [dyadic]
    | succ J ih => rw [sum_range_succ,ih,dyadic_succ]; ring
  rw [he]
  have := (dyadic_pos J).le
  linarith

/-- A dyadic Laplace kernel is controlled by the difference of two adjacent
powers. This is the elementary exponential inequality, with no prime input. -/
theorem log_kernel_le_difference {u t : ℝ} (hu : 0<u) :
    t*(Real.log u/u^(1+t))≤2*(1/u^(1+t/2)-1/u^(1+t)) := by
  have hexp : t*Real.log u≤2*(u^(t/2)-1) := by
    rw [Real.rpow_def_of_pos hu]
    have h := Real.add_one_le_exp (Real.log u*(t/2))
    nlinarith
  have hp := Real.rpow_pos_of_pos hu (1+t)
  have hid : u^(1+t)=u^(1+t/2)*u^(t/2) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  calc
    _ = (t*Real.log u)/u^(1+t) := by ring
    _ ≤ 2*(u^(t/2)-1)/u^(1+t) := div_le_div_of_nonneg_right hexp hp.le
    _ = _ := by
      rw [hid]
      field_simp

/-- Summing geometrically spaced kernels costs an absolute constant,
rather than the number of sample points. -/
theorem dyadic_log_kernel_sum {u : ℝ} (hu : 0<u) (J : ℕ) :
    (∑ j∈range J, dyadic j*(Real.log u/u^(1+dyadic j)))≤2/u^(1+dyadic J) := by
  calc
    _ ≤ ∑ j∈range J, 2*(1/u^(1+dyadic (j+1))-1/u^(1+dyadic j)) := by
      apply sum_le_sum
      intro j _
      rw [dyadic_succ]
      exact log_kernel_le_difference hu
    _ = 2*(1/u^(1+dyadic J)-1/u^(1+dyadic 0)) := by
      rw [← mul_sum]
      congr 1
      exact sum_range_sub (fun j : ℕ => 1/u^(1+dyadic j)) J
    _ ≤ _ := by
      have h : 0≤1/u^(1+dyadic 0) := by positivity
      simp only [div_eq_mul_inv] at *
      nlinarith

def primeDirichlet {M : ℕ} (a : ZMod M) (t : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod M)=a then 1/(n : ℝ)^(1+t) else 0

def primeLogDirichlet {M : ℕ} (a : ZMod M) (t : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod M)=a then Real.log (n : ℝ)/(n : ℝ)^(1+t) else 0

theorem primeDirichlet_summable {M : ℕ} (a : ZMod M) {t : ℝ} (ht : 0<t) :
    Summable (primeDirichlet a t) := by
  apply Summable.of_nonneg_of_le (fun n => by unfold primeDirichlet; split_ifs <;> positivity)
    (fun n => show primeDirichlet a t n≤1/(n : ℝ)^(1+t) by unfold primeDirichlet; split_ifs; exact le_rfl; positivity)
  exact Real.summable_one_div_nat_rpow.mpr (by linarith)

theorem residueDirichlet_summable {M : ℕ} (a : ZMod M) {t : ℝ} (ht : 0<t) :
    Summable (fun n : ℕ => residueClass a n/(n : ℝ)^(1+t)) :=
  summable_real_of_abscissaOfAbsConv_lt
    ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by norm_cast; linarith))

theorem primeLogDirichlet_le_residue {M : ℕ} (a : ZMod M) (t : ℝ) (n : ℕ) :
    primeLogDirichlet a t n≤residueClass a n/(n : ℝ)^(1+t) := by
  unfold primeLogDirichlet
  split_ifs with h
  · simp [residueClass,h.2,vonMangoldt_apply_prime h.1]
  · exact div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem primeLogDirichlet_summable {M : ℕ} (a : ZMod M) {t : ℝ} (ht : 0<t) :
    Summable (primeLogDirichlet a t) := by
  apply Summable.of_nonneg_of_le (fun n => ?_) (primeLogDirichlet_le_residue a t)
    (residueDirichlet_summable a ht)
  unfold primeLogDirichlet
  split_ifs with h
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.1.one_lt.le))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact le_rfl

/-- The finite dyadic kernel estimate applied to actual primes in one
residue class, and then summed over those primes. -/
theorem dyadic_primeLog_sum_bound {M : ℕ} (a : ZMod M) (J : ℕ) :
    (∑ j∈range J, dyadic j*(∑' n, primeLogDirichlet a (dyadic j) n))≤
      2*(∑' n, primeDirichlet a (dyadic J) n) := by
  have hpoint (n : ℕ) : (∑ j∈range J, dyadic j*primeLogDirichlet a (dyadic j) n)≤
      2*primeDirichlet a (dyadic J) n := by
    by_cases hn : n.Prime ∧ (n : ZMod M)=a
    · simpa only [primeLogDirichlet,primeDirichlet,hn,and_self,ite_true,mul_one_div] using
        dyadic_log_kernel_sum (u := (n : ℝ)) (by exact_mod_cast hn.1.pos) J
    · simp [primeLogDirichlet,primeDirichlet,hn]
  have hs (j : ℕ) : Summable (fun n => dyadic j*primeLogDirichlet a (dyadic j) n) :=
    (primeLogDirichlet_summable a (dyadic_pos j)).mul_left _
  have hsum : Summable (fun n => ∑ j∈range J, dyadic j*primeLogDirichlet a (dyadic j) n) := by
    clear hpoint
    induction J with
    | zero => simp
    | succ J ih => simpa only [sum_range_succ] using ih.add (hs J)
  calc
    _ = ∑' n, ∑ j∈range J, dyadic j*primeLogDirichlet a (dyadic j) n := by
      simp only [← tsum_mul_left]
      exact (Summable.tsum_finsetSum (fun j _ => hs j)).symm
    _ ≤ ∑' n, 2*primeDirichlet a (dyadic J) n :=
      hsum.tsum_le_tsum hpoint
        ((primeDirichlet_summable a (dyadic_pos J)).mul_left _)
    _ = _ := tsum_mul_left

#print axioms dyadic_log_kernel_sum
#print axioms dyadic_primeLog_sum_bound
end QuantitativeEulerEndpointAP
