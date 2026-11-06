module

public import QuantitativeArithmeticShiftedSieveDenominatorDefsV1
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

@[expose] public noncomputable section
namespace QuantitativeArithmetic

open Finset

theorem reciprocal_square_sum_le_two (z : ℕ) :
    (∑ b ∈ Icc 1 z, 1 / (b : ℝ) ^ 2) ≤ 2 := by
  have hstrong (z : ℕ) :
      (∑ b ∈ Icc 1 z, 1 / (b : ℝ) ^ 2) ≤ 2 - 2 / ((z : ℝ) + 1) := by
    induction z with
    | zero => norm_num
    | succ z ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hz : (0 : ℝ) < (z : ℝ) + 1 := by positivity
      have hz' : (0 : ℝ) < (z : ℝ) + 2 := by positivity
      have he : 1 / ((z : ℝ) + 1) ^ 2 ≤
          2 / ((z : ℝ) + 1) - 2 / ((z : ℝ) + 2) := by
        field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) z]
      push_cast
      rw [show (z : ℝ) + 1 + 1 = (z : ℝ) + 2 by ring]
      linarith
  exact (hstrong z).trans (sub_le_self _ (by positivity))

theorem squarefreeCoprimeHarmonic_le_denominator (R z : ℕ) :
    squarefreeCoprimeHarmonic R z ≤ shiftedSieveDenominator R z := by
  classical
  unfold squarefreeCoprimeHarmonic shiftedSieveDenominator
  apply sum_le_sum
  intro n hn
  split_ifs with h
  · apply one_div_le_one_div_of_le
    · exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hn).1
    · exact_mod_cast Nat.totient_le n
  · rfl

/-- Every positive integer has a squarefree-times-square decomposition.
Injecting the coprime integers into all such pairs bounds their harmonic
mass by the squarefree harmonic mass times the reciprocal-square sum. -/
theorem coprimeHarmonic_le_two_squarefree (R z : ℕ) :
    coprimeHarmonic R z ≤ 2 * squarefreeCoprimeHarmonic R z := by
  classical
  choose b a heq hsf using fun n : ℕ => exists_sq_mul_squarefree n
  let T := (Icc 1 z).filter (fun n => Nat.Coprime n R)
  let A := (Icc 1 z).filter (fun n => Squarefree n ∧ Nat.Coprime n R)
  have hprops (n : ℕ) (hn : n ∈ T) :
      a n ∈ A ∧ b n ∈ Icc 1 z := by
    obtain ⟨hnrange, hcop⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnle⟩ := mem_Icc.mp hnrange
    have ha : 1 ≤ a n := Nat.one_le_iff_ne_zero.mpr (hsf n).ne_zero
    have hb : 1 ≤ b n := by
      by_contra! hh
      have hzero : b n = 0 := by omega
      have := heq n
      simp [hzero] at this
      omega
    have hbsq : 1 ≤ b n ^ 2 := by nlinarith
    have hab : a n ≤ n := by nlinarith [heq n]
    have hbb : b n ≤ n := by nlinarith [heq n, Nat.le_mul_self (b n)]
    have hcopa : Nat.Coprime (a n) R := hcop.of_dvd_left ⟨b n ^ 2, by
      simpa only [mul_comm] using (heq n).symm⟩
    exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨ha, hab.trans hnle⟩, hsf n, hcopa⟩,
      mem_Icc.mpr ⟨hb, hbb.trans hnle⟩⟩
  have hsum : (∑ n ∈ T, 1 / (n : ℝ)) ≤
      ∑ ab ∈ A ×ˢ Icc 1 z, (1 / (ab.1 : ℝ)) * (1 / (ab.2 : ℝ) ^ 2) := by
    apply sum_le_sum_of_injOn (fun n => (a n, b n))
    · intro n hn m hm hnm
      have hh := congrArg (fun ab : ℕ × ℕ => ab.2 ^ 2 * ab.1) hnm
      simpa only [heq] using hh
    · intro ab hab
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hab
      exact mem_product.mpr (hprops n hn)
    · intro n _
      have hh : (b n : ℝ) ^ 2 * (a n : ℝ) = n := by exact_mod_cast heq n
      rw [← hh]
      simp only [one_div, mul_inv_rev]
      rfl
    · intro ab _ _
      positivity
  have heval : (∑ ab ∈ A ×ˢ Icc 1 z, (1 / (ab.1 : ℝ)) * (1 / (ab.2 : ℝ) ^ 2)) =
      (∑ n ∈ A, 1 / (n : ℝ)) * (∑ b ∈ Icc 1 z, 1 / (b : ℝ) ^ 2) := by
    rw [sum_product]
    simp only [← mul_sum, ← sum_mul]
  have hnonneg : 0 ≤ ∑ n ∈ A, 1 / (n : ℝ) := by positivity
  rw [heval] at hsum
  have hh := hsum.trans (mul_le_mul_of_nonneg_left (reciprocal_square_sum_le_two z) hnonneg)
  simpa only [T, A, sum_filter, coprimeHarmonic, squarefreeCoprimeHarmonic, mul_comm] using hh

theorem half_coprimeHarmonic_le_denominator (R z : ℕ) :
    coprimeHarmonic R z / 2 ≤ shiftedSieveDenominator R z := by
  have h1 := coprimeHarmonic_le_two_squarefree R z
  have h2 := squarefreeCoprimeHarmonic_le_denominator R z
  linarith

theorem coprimeHarmonic_mono (R : ℕ) : Monotone (coprimeHarmonic R) := by
  classical
  intro x y hxy
  unfold coprimeHarmonic
  apply sum_le_sum_of_subset_of_nonneg
  · exact Icc_subset_Icc_right hxy
  · intro n _ _
    split_ifs <;> positivity

private theorem coprime_block_lower (R j : ℕ) (_hR : 0 < R) :
    (R.totient : ℝ) / ((R : ℝ) * (j + 1)) ≤
      ∑ n ∈ Ico (R * j + 1) (R * (j + 1) + 1),
        if Nat.Coprime n R then 1 / (n : ℝ) else 0 := by
  classical
  let B := (Ico (R * j + 1) (R * (j + 1) + 1)).filter (fun n => Nat.Coprime n R)
  have hcard : B.card = R.totient := by
    simpa only [B, show R * j + 1 + R = R * (j + 1) + 1 by ring,
      Nat.coprime_comm] using Nat.filter_coprime_Ico_eq_totient R (R * j + 1)
  have hs : (∑ n ∈ B, 1 / ((R : ℝ) * (j + 1))) ≤ ∑ n ∈ B, 1 / (n : ℝ) := by
    apply sum_le_sum
    intro n hn
    have hn' := mem_Ico.mp (mem_filter.mp hn).1
    have hnp : 0 < n := by omega
    apply one_div_le_one_div_of_le (by exact_mod_cast hnp)
    have hnle : n ≤ R * (j + 1) := by omega
    exact_mod_cast hnle
  simpa only [sum_const, nsmul_eq_mul, hcard, mul_one_div, B, sum_filter] using hs

/-- Complete residue blocks give a finite harmonic lower bound with the
correct totient factor; no distribution of primes is used. -/
theorem coprimeHarmonic_mul_lower (R L : ℕ) (hR : 0 < R) :
    ((R.totient : ℝ) / R) * (harmonic L : ℝ) ≤ coprimeHarmonic R (R * L) := by
  classical
  induction L with
  | zero => simp [coprimeHarmonic]
  | succ L ih =>
    have hblock := coprime_block_lower R L hR
    have hsplit := sum_Ico_consecutive
      (fun n : ℕ => if Nat.Coprime n R then 1 / (n : ℝ) else 0)
      (m := 1) (n := R * L + 1) (k := R * (L + 1) + 1)
      (by omega) (by nlinarith)
    simp only [Ico_add_one_right_eq_Icc] at hsplit
    change coprimeHarmonic R (R * L) + _ = coprimeHarmonic R (R * (L + 1)) at hsplit
    simp only [Ico_add_one_right_eq_Icc] at hblock
    rw [harmonic_succ]
    push_cast
    rw [mul_add, ← hsplit]
    apply add_le_add ih
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hblock

theorem coprimeHarmonic_div_lower (R z : ℕ) (hR : 0 < R) :
    ((R.totient : ℝ) / R) * (harmonic (z / R) : ℝ) ≤ coprimeHarmonic R z :=
  (coprimeHarmonic_mul_lower R (z / R) hR).trans
    (coprimeHarmonic_mono R (Nat.mul_div_le z R))

/-- A finite denominator lower bound, stronger than the factor 1/4
originally planned for the fixed-modulus density proof. -/
theorem shiftedSieveDenominator_harmonic_lower (R z : ℕ) (hR : 0 < R) :
    ((R.totient : ℝ) / (2 * R)) * (harmonic (z / R) : ℝ) ≤
      shiftedSieveDenominator R z := by
  have h1 := coprimeHarmonic_div_lower R z hR
  have h2 := half_coprimeHarmonic_le_denominator R z
  have he : ((R.totient : ℝ) / (2 * R)) * (harmonic (z / R) : ℝ) =
      (((R.totient : ℝ) / R) * (harmonic (z / R) : ℝ)) / 2 := by ring
  rw [he]
  linarith

theorem half_log_le_harmonic_div (R z : ℕ) (hR : 0 < R) (hz : R ^ 2 ≤ z) :
    Real.log (z : ℝ) / 2 ≤ (harmonic (z / R) : ℝ) := by
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hzp : (0 : ℝ) < z := by exact_mod_cast (lt_of_lt_of_le (pow_pos hR 2) hz)
  have hmod := Nat.mod_lt z hR
  have hdiv := Nat.mod_add_div z R
  have hnat : z ≤ R * (z / R + 1) := by nlinarith
  have hprod : (z : ℝ) ≤ (R : ℝ) * ((z / R : ℕ) + 1) := by exact_mod_cast hnat
  have hlog := Real.log_le_log hzp hprod
  rw [Real.log_mul hRp.ne' (by positivity)] at hlog
  have hsq : (R : ℝ) ^ 2 ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogR := Real.log_le_log (pow_pos hRp 2) hsq
  rw [Real.log_pow] at hlogR
  have hH := log_add_one_le_harmonic (z / R)
  push_cast at hH hlogR
  linarith

/-- The denominator has an explicit logarithmic lower bound once the
natural cutoff exceeds the square of the fixed modulus. -/
theorem shiftedSieveDenominator_log_lower (R z : ℕ) (hR : 0 < R) (hz : R ^ 2 ≤ z) :
    ((R.totient : ℝ) / (4 * R)) * Real.log z ≤ shiftedSieveDenominator R z := by
  have hh := mul_le_mul_of_nonneg_left (half_log_le_harmonic_div R z hR hz)
    (show 0 ≤ (R.totient : ℝ) / (2 * R) by positivity)
  have he : ((R.totient : ℝ) / (2 * R)) * (Real.log z / 2) =
      ((R.totient : ℝ) / (4 * R)) * Real.log z := by ring
  rw [he] at hh
  exact hh.trans (shiftedSieveDenominator_harmonic_lower R z hR)

theorem eventually_shiftedSieveDenominator_log_lower (R : ℕ) (hR : 0 < R) :
    ∀ᶠ z : ℕ in Filter.atTop,
      ((R.totient : ℝ) / (4 * R)) * Real.log z ≤ shiftedSieveDenominator R z :=
  Filter.eventually_atTop.mpr ⟨R ^ 2, fun z hz => shiftedSieveDenominator_log_lower R z hR hz⟩

#print axioms half_coprimeHarmonic_le_denominator
#print axioms shiftedSieveDenominator_harmonic_lower
#print axioms shiftedSieveDenominator_log_lower
#print axioms eventually_shiftedSieveDenominator_log_lower
end QuantitativeArithmetic
