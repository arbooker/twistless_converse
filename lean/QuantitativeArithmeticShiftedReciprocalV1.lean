module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic
public import QuantitativeHolomorphicPrimeProductV1

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Filter Topology ArithmeticFunction
open ArithmeticFunction.vonMangoldt

/-- Reciprocal-prime summand for one literal unit residue class. -/
def reciprocalPrimeClass {M : ℕ} (a : ZMod M) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod M) = a then 1 / (n : ℝ) else 0

private def step (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private lemma step_pos (n : ℕ) : 0 < step n := by
  unfold step
  positivity

private lemma step_le_one (n : ℕ) : step n ≤ 1 := by
  unfold step
  apply (div_le_one (by positivity)).2
  linarith [Nat.cast_nonneg (α := ℝ) n]

private lemma step_tendsto : Tendsto step atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Uniform Abel-kernel bound; this supplies a summable unweighted majorant. -/
private lemma log_kernel_le {x t : ℝ} (hx : 0 < x) :
    t * (Real.log x / x ^ (1 + t)) ≤ 1 / x := by
  rw [Real.rpow_add hx, Real.rpow_one]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos hx (Real.rpow_pos_of_pos hx t))).2
  have he : t * Real.log x ≤ x ^ t := by
    rw [Real.rpow_def_of_pos hx]
    have := Real.add_one_le_exp (Real.log x * t)
    nlinarith
  convert he using 1
  field_simp

private lemma power_quotient_le {M : ℕ} (a : ZMod M) (m : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    residueClass a m / (m : ℝ) ^ (1 + t) ≤ residueClass a m / m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  apply div_le_div_of_nonneg_left (residueClass_nonneg a m) (by exact_mod_cast hm)
  conv_lhs => rw [← Real.rpow_one (m : ℝ)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)

/-- Unweighted reciprocal primes diverge in every unit residue class.

This derives the assertion from Mathlib's actual Dirichlet L-series pole,
not from a density assumption or from infinitude alone. The proof uses
dominated convergence of the scaled Abel kernels. -/
theorem not_summable_reciprocalPrimeClass {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) : ¬ Summable (reciprocalPrimeClass a) := by
  intro hs
  let bound : ℕ → ℝ := fun m => reciprocalPrimeClass a m +
    (if m.Prime then 0 else residueClass a m) / m
  have hsum : Summable bound := hs.add (summable_residueClass_non_primes_div a)
  let f : ℕ → ℕ → ℝ := fun n m =>
    step n * (residueClass a m / (m : ℝ) ^ (1 + step n))
  have hf_nonneg (n m : ℕ) : 0 ≤ f n m := by
    dsimp [f]
    positivity [step_pos n, residueClass_nonneg a m]
  have hf_le (n m : ℕ) : f n m ≤ bound m := by
    by_cases hp : m.Prime
    · by_cases hm : (m : ZMod M) = a
      · simp only [bound, reciprocalPrimeClass, hp, hm, and_self, ↓reduceIte,
          zero_div, add_zero]
        simpa only [f, residueClass, Set.indicator_apply, Set.mem_ofPred_eq, hm,
          ↓reduceIte, vonMangoldt_apply_prime hp] using
          (log_kernel_le (x := (m : ℝ)) (t := step n) (by exact_mod_cast hp.pos))
      · simp [f, bound, reciprocalPrimeClass, residueClass, hp, hm]
    · simp only [bound, reciprocalPrimeClass, hp, false_and, ↓reduceIte, zero_add]
      calc
        f n m ≤ step n * (residueClass a m / m) :=
          mul_le_mul_of_nonneg_left (power_quotient_le a m (step_pos n).le) (step_pos n).le
        _ ≤ residueClass a m / m :=
          mul_le_of_le_one_left (by positivity [residueClass_nonneg a m]) (step_le_one n)
  have hf_lim (m : ℕ) : Tendsto (fun n => f n m) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => hf_nonneg n m)
      (fun n => mul_le_mul_of_nonneg_left
        (power_quotient_le a m (step_pos n).le) (step_pos n).le)
    simpa using step_tendsto.mul_const (residueClass a m / m)
  have hlim : Tendsto (fun n => ∑' m, f n m) atTop (𝓝 0) := by
    simpa only [tsum_zero] using
      (tendsto_tsum_of_dominated_convergence hsum hf_lim
        (Filter.Eventually.of_forall (fun n m => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg n m)]
          exact hf_le n m)))
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound ha
  have hineq (n : ℕ) : (M.totient : ℝ)⁻¹ - C * step n ≤ ∑' m, f n m := by
    have hn : 1 + step n ∈ Set.Ioc (1 : ℝ) 2 :=
      ⟨by linarith [step_pos n], by linarith [step_le_one n]⟩
    have hh := mul_le_mul_of_nonneg_left (hC hn) (step_pos n).le
    simp only [add_sub_cancel_left] at hh
    have heq : step n * ((M.totient : ℝ)⁻¹ / step n - C) =
        (M.totient : ℝ)⁻¹ - C * step n := by
      field_simp [(step_pos n).ne']
    rw [heq] at hh
    simpa only [f, tsum_mul_left] using hh
  have hleft : Tendsto (fun n => (M.totient : ℝ)⁻¹ - C * step n)
      atTop (𝓝 ((M.totient : ℝ)⁻¹)) := by
    simpa using tendsto_const_nhds.sub (step_tendsto.const_mul C)
  have hz : (M.totient : ℝ)⁻¹ ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hlim (Filter.Eventually.of_forall hineq)
  exact (not_le_of_gt (inv_pos.mpr (by exact_mod_cast M.totient.pos_of_neZero))) hz

/-- Any fixed finite exclusions leave the reciprocal AP divergence intact. -/
theorem not_summable_reciprocalPrimeClass_remove_finset {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) (B : Finset ℕ) :
    ¬ Summable (fun n => if n ∈ B then 0 else reciprocalPrimeClass a n) := by
  intro hs
  apply not_summable_reciprocalPrimeClass a ha
  apply hs.congr_cofinite
  filter_upwards [B.eventually_cofinite_notMem] with n hn
  simp only [hn, ↓reduceIte]

/-- Actual finite auxiliary-prime packets with arbitrarily large reciprocal
mass, after any fixed finite exclusions. This is the form needed by the
CRT avoidance-density argument. -/
theorem exists_primeClass_packet_sum_gt {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) (B : Finset ℕ) (A : ℝ) :
    ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ (p : ZMod M) = a ∧ p ∉ B) ∧
      A < ∑ p ∈ S, 1 / (p : ℝ) := by
  classical
  let f : ℕ → ℝ := fun n => if n ∈ B then 0 else reciprocalPrimeClass a n
  have hf : ¬ Summable f := not_summable_reciprocalPrimeClass_remove_finset a ha B
  have hlarge : ∃ U : Finset ℕ, A < ∑ p ∈ U, f p := by
    by_contra! h
    apply hf
    apply summable_of_sum_le (c := A) (fun p => ?_) h
    dsimp [f, reciprocalPrimeClass]
    split_ifs <;> positivity
  obtain ⟨U, hU⟩ := hlarge
  let S := U.filter (fun p : ℕ => p.Prime ∧ (p : ZMod M) = a ∧ p ∉ B)
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · convert hU using 1
    dsimp [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [f, reciprocalPrimeClass]
    split_ifs <;> simp_all

#print axioms not_summable_reciprocalPrimeClass
#print axioms not_summable_reciprocalPrimeClass_remove_finset
#print axioms exists_primeClass_packet_sum_gt

/-- Arbitrarily small CRT avoidance proportions from actual auxiliary
primes in a prescribed unit class. No prime-density premise is retained. -/
theorem exists_primeClass_packet_product_lt {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) (B : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ (p : ZMod M) = a ∧ p ∉ B) ∧
      (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))) < ε := by
  obtain ⟨S, hS, hmass⟩ := exists_primeClass_packet_sum_gt a ha B (-Real.log ε)
  refine ⟨S, hS, ?_⟩
  have hcomp : (∑ p ∈ S, 1 / (p : ℝ)) ≤ ∑ p ∈ S, 1 / ((p : ℝ) - 1) := by
    apply Finset.sum_le_sum
    intro p hp
    have htwo : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
    apply one_div_le_one_div_of_le (by linarith)
    linarith
  have hprod := QuantitativeHolomorphic.contraction_product_le_exp S
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (fun p hp =>
      QuantitativeHolomorphic.reciprocal_loss_mem_unit_interval (hS p hp).1
        (by norm_num) (by norm_num))
  apply hprod.trans_lt
  rw [← Real.exp_log hε]
  apply Real.exp_lt_exp.mpr
  linarith

#print axioms exists_primeClass_packet_product_lt

end QuantitativeArithmetic
