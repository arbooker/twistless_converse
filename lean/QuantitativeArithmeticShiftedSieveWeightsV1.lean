module

public import QuantitativeArithmeticShiftedSieveDenominatorDefsV1
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Finite Möbius inversion in the usual divisor order. -/
def divisorMobiusTransform (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ)*f p.2

theorem sum_divisorMobiusTransform (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, divisorMobiusTransform f d = f n := by
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
    (fun _ _ => rfl)) n hn

theorem divisorMobiusTransform_eq (f : ℕ → ℝ) (n : ℕ) :
    divisorMobiusTransform f n = ∑ d ∈ n.divisors, (μ (n/d) : ℝ)*f d := by
  exact Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ)*f b)

/-- The reversed divisor transform. Its definition avoids extending an
inverse matrix off the finite divisor lattice. -/
def reverseDivisorMobius (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  divisorMobiusTransform (fun n => y (P/n)) (P/d)

theorem sum_reverseDivisorMobius (P : ℕ) (hP : P ≠ 0) (y : ℕ → ℝ)
    (l : ℕ) (hl : l ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d then reverseDivisorMobius P y d else 0) = y l := by
  rw [← Nat.sum_div_divisors P
    (fun d => if l ∣ d then reverseDivisorMobius P y d else 0)]
  have heq (d : ℕ) (hd : d ∈ P.divisors) :
      (if l ∣ P/d then reverseDivisorMobius P y (P/d) else 0) =
      if d ∣ P/l then divisorMobiusTransform (fun n => y (P/n)) d else 0 := by
    have hdP := (Nat.mem_divisors.mp hd).1
    have hiff : l ∣ P/d ↔ d ∣ P/l := by
      rw [Nat.dvd_div_iff_mul_dvd hdP, Nat.dvd_div_iff_mul_dvd hl, mul_comm]
    simp only [hiff, reverseDivisorMobius, Nat.div_div_self hdP hP]
  rw [sum_congr rfl heq, ← sum_filter,
    Nat.divisors_filter_dvd_of_dvd hP (Nat.div_dvd_of_dvd hl)]
  rw [sum_divisorMobiusTransform _ _ (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl))), Nat.div_div_self hl hP]

/-- The finite denominator on an arbitrary squarefree sieve modulus. -/
def divisorSieveDenominator (P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then 1/(Nat.totient d : ℝ) else 0

def sieveDualWeights (P z : ℕ) (d : ℕ) : ℝ :=
  if d ≤ z then (μ d : ℝ)/((Nat.totient d : ℝ)*divisorSieveDenominator P z) else 0

/-- The actual optimal weights; all their properties are derived below. -/
def shiftedSieveWeights (P z : ℕ) (d : ℕ) : ℝ :=
  (d : ℝ)*reverseDivisorMobius P (sieveDualWeights P z) d

theorem shiftedSieveWeights_dual (P z l : ℕ) (hP : P ≠ 0) (hl : l ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d then shiftedSieveWeights P z d/(d : ℝ) else 0) =
      sieveDualWeights P z l := by
  rw [← sum_reverseDivisorMobius P hP (sieveDualWeights P z) l hl]
  apply sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  simp [shiftedSieveWeights, hd0]

theorem divisorSieveDenominator_nonneg (P z : ℕ) :
    0 ≤ divisorSieveDenominator P z := by
  apply sum_nonneg
  intro d _
  split_ifs <;> positivity

theorem one_le_divisorSieveDenominator (P z : ℕ) (hP : P ≠ 0) (hz : 1 ≤ z) :
    1 ≤ divisorSieveDenominator P z := by
  have h1 : 1 ∈ P.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hP⟩
  have hh := Finset.single_le_sum (s := P.divisors)
    (f := fun d => if d ≤ z then 1/(Nat.totient d : ℝ) else 0)
    (fun d _ => by split_ifs <;> positivity) h1
  simpa [divisorSieveDenominator, hz] using hh

theorem abs_sieveDualWeights (P z d : ℕ) (hP : Squarefree P) (hd : d ∣ P) :
    |sieveDualWeights P z d| =
      if d ≤ z then (1/(Nat.totient d : ℝ))/divisorSieveDenominator P z else 0 := by
  have hμ : |(μ d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (Squarefree.squarefree_of_dvd hd hP)
  simp only [sieveDualWeights]
  split_ifs
  · rw [abs_div, abs_mul, hμ, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (divisorSieveDenominator_nonneg P z)]
    ring
  · simp

theorem sum_abs_sieveDualWeights (P z : ℕ) (hP : Squarefree P) (hz : 1 ≤ z) :
    ∑ d ∈ P.divisors, |sieveDualWeights P z d| = 1 := by
  have hG : divisorSieveDenominator P z ≠ 0 := by
    have hh := one_le_divisorSieveDenominator P z hP.ne_zero hz
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
        (if d ≤ z then 1/(Nat.totient d : ℝ) else 0)/divisorSieveDenominator P z := by
      apply sum_congr rfl
      intro d hd
      rw [abs_sieveDualWeights P z d hP (Nat.mem_divisors.mp hd).1]
      split_ifs <;> simp
    _ = divisorSieveDenominator P z / divisorSieveDenominator P z := by
      rw [← sum_div]; rfl
    _ = 1 := div_self hG

theorem reverseDivisorMobius_abs_le (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    |reverseDivisorMobius P y d| ≤ ∑ l ∈ P.divisors, |y l| := by
  rw [reverseDivisorMobius, divisorMobiusTransform_eq]
  calc
    _ ≤ ∑ a ∈ (P/d).divisors, |(μ (P/d/a) : ℝ)*y (P/a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ (P/d).divisors, |y (P/a)| := by
      apply sum_le_sum
      intro a _
      rw [abs_mul]
      have hμ : |(μ (P/d/a) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := P/d/a))
      simpa using mul_le_mul_of_nonneg_right hμ (abs_nonneg (y (P/a)))
    _ ≤ ∑ a ∈ P.divisors, |y (P/a)| :=
      sum_le_sum_of_subset_of_nonneg
        (Nat.divisors_subset_of_dvd hP (Nat.div_dvd_of_dvd hd)) (fun _ _ _ => abs_nonneg _)
    _ = ∑ l ∈ P.divisors, |y l| := Nat.sum_div_divisors P (fun l => |y l|)

theorem shiftedSieveWeights_abs_le (P z d : ℕ) (hP : Squarefree P) (hz : 1 ≤ z)
    (hd : d ∣ P) : |shiftedSieveWeights P z d| ≤ (d : ℝ) := by
  rw [shiftedSieveWeights, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hh := reverseDivisorMobius_abs_le P d hP.ne_zero hd (sieveDualWeights P z)
  rw [sum_abs_sieveDualWeights P z hP hz] at hh
  simpa using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg d : (0 : ℝ) ≤ d)

theorem shiftedSieveWeights_one (P z : ℕ) (hP : Squarefree P) (hz : 1 ≤ z) :
    shiftedSieveWeights P z 1 = 1 := by
  rw [shiftedSieveWeights, Nat.cast_one, one_mul, reverseDivisorMobius, Nat.div_one,
    divisorMobiusTransform_eq, Nat.sum_div_divisors P (fun d => (μ d : ℝ)*sieveDualWeights P z d)]
  rw [← sum_abs_sieveDualWeights P z hP hz]
  apply sum_congr rfl
  intro d hd
  have hdP := (Nat.mem_divisors.mp hd).1
  rw [abs_sieveDualWeights P z d hP hdP]
  have hμ : (μ d : ℝ)^2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (Squarefree.squarefree_of_dvd hdP hP)
  simp only [sieveDualWeights]
  split_ifs
  · calc
      _ = (μ d : ℝ)^2/((Nat.totient d : ℝ)*divisorSieveDenominator P z) := by ring
      _ = _ := by rw [hμ]; ring
  · simp

theorem shiftedSieveWeights_eq_zero_of_lt (P z d : ℕ) (hP : P ≠ 0)
    (hd : d ∣ P) (hzd : z < d) : shiftedSieveWeights P z d = 0 := by
  rw [shiftedSieveWeights, reverseDivisorMobius, divisorMobiusTransform_eq]
  have hs : (∑ a ∈ (P/d).divisors,
      (μ (P/d/a) : ℝ)*sieveDualWeights P z (P/a)) = 0 := by
    apply sum_eq_zero
    intro a ha
    have haD := (Nat.mem_divisors.mp ha).1
    have haP : a ∣ P := haD.trans (Nat.div_dvd_of_dvd hd)
    have hdPa : d ∣ P/a := by
      apply (Nat.dvd_div_iff_mul_dvd haP).mpr
      simpa [mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).mp haD
    have ha0 := Nat.pos_of_mem_divisors ha
    have hPa : 0 < P/a := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) haP) ha0
    have hdle := Nat.le_of_dvd hPa hdPa
    simp [sieveDualWeights, show ¬P/a ≤ z by omega]
  rw [hs, mul_zero]

/-- Identify the generic diagonal sieve factor with the actual totient.
This uses the proved divisor sum of Euler's totient and Möbius inversion. -/
theorem sieve_inverse_term_eq_totient (s : BoundingSieve)
    (hnu : ∀ n : ℕ, s.nu n = 1/(n : ℝ)) (l : ℕ) (hl : l ∣ s.prodPrimes) :
    (s.selbergTerms l)⁻¹ = (Nat.totient l : ℝ) := by
  have hl0 : 0 < l := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero s.prodPrimes_squarefree.ne_zero hl)
  rw [BoundingSieve.inv_selbergTerms_eq_sum_divisors_moebius_nu
    (s.squarefree_of_dvd_prodPrimes hl) (s.nu_ne_zero hl)]
  simp only [hnu, one_div, inv_inv]
  have htot : ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, (Nat.totient d : ℝ) = (n : ℝ) := by
    intro n _
    exact_mod_cast Nat.sum_totient n
  exact ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp htot l hl0

theorem sum_totient_dual_sq (P z : ℕ) (hP : Squarefree P) (hz : 1 ≤ z) :
    (∑ l ∈ P.divisors, (Nat.totient l : ℝ)*sieveDualWeights P z l^2) =
      1/divisorSieveDenominator P z := by
  have hG : divisorSieveDenominator P z ≠ 0 := by
    have hh := one_le_divisorSieveDenominator P z hP.ne_zero hz
    linarith
  calc
    _ = ∑ l ∈ P.divisors,
      (if l ≤ z then 1/(Nat.totient l : ℝ) else 0)/divisorSieveDenominator P z^2 := by
      apply sum_congr rfl
      intro l hl
      have hlP := (Nat.mem_divisors.mp hl).1
      have hφ : (Nat.totient l : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hl)).ne'
      have hμ : (μ l : ℝ)^2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (Squarefree.squarefree_of_dvd hlP hP)
      simp only [sieveDualWeights]
      split_ifs
      · simp only [div_pow, mul_pow, hμ]
        field_simp
      · simp
    _ = divisorSieveDenominator P z/divisorSieveDenominator P z^2 := by
      rw [← sum_div]; rfl
    _ = _ := by field_simp

/-- Exact optimal main term for the already-defined finite weights. -/
theorem shiftedSieveWeights_mainSum (s : BoundingSieve)
    (hnu : ∀ n : ℕ, s.nu n = 1/(n : ℝ)) (z : ℕ) (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (shiftedSieveWeights s.prodPrimes z)) =
      1/divisorSieveDenominator s.prodPrimes z := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  rw [← sum_totient_dual_sq s.prodPrimes z s.prodPrimes_squarefree hz]
  apply sum_congr rfl
  intro l hl
  have hlP := (Nat.mem_divisors.mp hl).1
  rw [sieve_inverse_term_eq_totient s hnu l hlP]
  congr 2
  simpa only [hnu, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
    shiftedSieveWeights_dual s.prodPrimes z l s.prodPrimes_squarefree.ne_zero hlP

theorem lambdaSquared_abs_le (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤ BoundingSieve.lambdaSquared (fun n => |w n|) d := by
  unfold BoundingSieve.lambdaSquared
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro a _
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro b _
  split_ifs <;> simp [abs_mul]

/-- Summing the lcm coefficients exactly recovers the square of the sum.
The finite divisors in the inner definition are enlarged only where the
lcm constraint already forces both indices to divide that lcm. -/
theorem sum_divisors_lambdaSquared (P : ℕ) (hP : P ≠ 0) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d) =
      (∑ d ∈ P.divisors, w d)^2 := by
  unfold BoundingSieve.lambdaSquared
  have henlarge :
      (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then w a*w b else 0) =
      ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then w a*w b else 0 := by
    apply sum_congr rfl
    intro d hd
    have hdP := (Nat.mem_divisors.mp hd).1
    have hiff : ∀ a b, (a ∣ d ∧ b ∣ d ∧ d = Nat.lcm a b) ↔ d = Nat.lcm a b := by
      intro a b
      constructor
      · exact fun h => h.2.2
      · intro h
        rw [h]
        exact ⟨Nat.dvd_lcm_left _ _, Nat.dvd_lcm_right _ _, rfl⟩
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hP hdP, sum_filter, ite_sum_zero,
      ← ite_and, hiff]
  rw [henlarge, sum_comm]
  have hcollapse : (∑ a ∈ P.divisors, ∑ d ∈ P.divisors, ∑ b ∈ P.divisors,
      if d = Nat.lcm a b then w a*w b else 0) =
      ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, w a*w b := by
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
    apply sum_congr rfl
    intro b hb
    apply sum_ite_eq_of_mem'
    exact Nat.mem_divisors.mpr ⟨Nat.lcm_dvd_iff.mpr
      ⟨(Nat.mem_divisors.mp ha).1, (Nat.mem_divisors.mp hb).1⟩, hP⟩
  rw [hcollapse, sq, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]

theorem shiftedSieveWeights_sum_abs_le (P z : ℕ) (hP : Squarefree P) (hz : 1 ≤ z) :
    (∑ d ∈ P.divisors, |shiftedSieveWeights P z d|) ≤ (z : ℝ)^2 := by
  classical
  let S := P.divisors.filter (fun d => d ≤ z)
  have hsub : S ⊆ Icc 1 z := by
    intro d hd
    obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdz⟩
  have he : (∑ d ∈ P.divisors, |shiftedSieveWeights P z d|) =
      ∑ d ∈ S, |shiftedSieveWeights P z d| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hdS
    have hdz : z < d := by
      have hn : ¬d ≤ z := by intro h; exact hdS (mem_filter.mpr ⟨hd, h⟩)
      omega
    rw [shiftedSieveWeights_eq_zero_of_lt P z d hP.ne_zero (Nat.mem_divisors.mp hd).1 hdz]
    simp
  rw [he]
  calc
    _ ≤ ∑ d ∈ S, (d : ℝ) := sum_le_sum (fun d hd =>
      shiftedSieveWeights_abs_le P z d hP hz (Nat.mem_divisors.mp (mem_filter.mp hd).1).1)
    _ ≤ ∑ d ∈ Icc 1 z, (d : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ _d ∈ Icc 1 z, (z : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact_mod_cast (mem_Icc.mp hd).2
    _ = (z : ℝ)^2 := by simp [sq]

/-- The explicit optimal finite upper sieve, with its fully derived z^4
error. The remainder bound is the elementary progression-count input. -/
theorem shiftedSieveWeights_sifted_bound (s : BoundingSieve)
    (hnu : ∀ n : ℕ, s.nu n = 1/(n : ℝ)) (z : ℕ) (hz : 1 ≤ z)
    (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ 1) :
    s.siftedSum ≤ s.totalMass/divisorSieveDenominator s.prodPrimes z+(z : ℝ)^4 := by
  let w := shiftedSieveWeights s.prodPrimes z
  have hs := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared w)
    (BoundingSieve.upperMoebius_lambdaSquared w
      (shiftedSieveWeights_one s.prodPrimes z s.prodPrimes_squarefree hz))
  rw [shiftedSieveWeights_mainSum s hnu z hz] at hs
  have herr : s.errSum (BoundingSieve.lambdaSquared w) ≤ (z : ℝ)^4 := by
    unfold BoundingSieve.errSum
    calc
      _ ≤ ∑ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d| := by
        apply sum_le_sum
        intro d hd
        simpa using mul_le_mul_of_nonneg_left (hrem d hd) (abs_nonneg _)
      _ ≤ ∑ d ∈ s.prodPrimes.divisors, BoundingSieve.lambdaSquared (fun d => |w d|) d :=
        sum_le_sum (fun d _ => lambdaSquared_abs_le w d)
      _ = (∑ d ∈ s.prodPrimes.divisors, |w d|)^2 :=
        sum_divisors_lambdaSquared _ s.prodPrimes_squarefree.ne_zero _
      _ ≤ ((z : ℝ)^2)^2 := by
        apply pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _))
        exact shiftedSieveWeights_sum_abs_le _ _ s.prodPrimes_squarefree hz
      _ = _ := by ring
  have hh := hs.trans (add_le_add le_rfl herr)
  simpa only [div_eq_mul_inv, one_mul] using hh

#print axioms sum_reverseDivisorMobius
#print axioms shiftedSieveWeights_dual
#print axioms shiftedSieveWeights_abs_le
#print axioms shiftedSieveWeights_one
#print axioms shiftedSieveWeights_eq_zero_of_lt
#print axioms shiftedSieveWeights_mainSum
#print axioms shiftedSieveWeights_sum_abs_le
#print axioms shiftedSieveWeights_sifted_bound

end QuantitativeArithmetic
