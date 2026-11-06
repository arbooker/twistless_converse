module

public import QuantitativeArithmeticSmallLevelCircEigenSolutionV1
public import QuantitativeArithmeticSmallLevelCircCountV1
public import FinitenessAllLevelGoodCoefficientsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane FinitenessOriginalInput FinitenessOriginalFourier SmallLevelOriginal
open scoped ModularForm

theorem original_unitary_coefficients {N k : ℕ} {hN : 0 < N} {f : ℕ → ℂ}
    (hf : IsSolution N k f) (F : space N hN k)
    (hF : (F.val : ℍ → ℂ) = fourierFunction k f) : ModularLSeries.coefficients F.val = f := by
  funext n
  have hc := original_coefficient hf F hF n
  change (qExpansion 1 F.val).coeff n = fullCoefficients f k n at hc
  rw [ModularLSeries.coefficients, hc]
  by_cases hn : n = 0
  · subst n
    rw [fullCoefficients_zero hf.zero, zero_mul, hf.zero]
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    change (f n * (((n : ℝ)^FinitenessCompletedNormalization.alpha k : ℝ) : ℂ)) *
      (((n : ℝ)^(-((k : ℝ)-1)/2) : ℝ) : ℂ) = f n
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hnR,
      show FinitenessCompletedNormalization.alpha k + -((k : ℝ)-1)/2 = 0 by
        unfold FinitenessCompletedNormalization.alpha; ring]
    simp

theorem original_prime_eigen {N k : ℕ} [NeZero N] {hN : 0 < N} {f : ℕ → ℂ}
    (hf : IsSolution N k f) (F : space N hN k)
    (hF : (F.val : ℍ → ℂ) = fourierFunction k f) (p : Nat.Primes) :
    ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val =
      fullCoefficients f k p.val • F.val := by
  apply sub_eq_zero.mp
  apply modularCoefficient_separates N (k : ℤ)
  intro n
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [ModularHecke.coeff_primeHecke, map_smul]
  have hc (a : ℕ) : modularCoefficient N (k : ℤ) a F.val = fullCoefficients f k a :=
    original_coefficient hf F hF a
  simp only [hc, smul_eq_mul]
  by_cases hpN : p.val ∣ N
  · simp only [ModularHecke.primeHeckeFactor, hpN, ite_true, zero_mul, add_zero]
    exact AsymptoticRamifiedCoefficients.fullCoefficients_bad_mul hf.toEulerData p.property hpN k n
  · have hpR : 0 < (p.val : ℝ) := by exact_mod_cast p.property.pos
    have hpow : ((((p.val : ℝ)^FinitenessCompletedNormalization.alpha k : ℝ) : ℂ))^2 =
        (p.val : ℂ)^((k : ℤ)-1) := by
      rw [← Complex.ofReal_pow, pow_two, ← Real.rpow_add hpR]
      have ha : FinitenessCompletedNormalization.alpha k + FinitenessCompletedNormalization.alpha k =
          (((k : ℤ)-1 : ℤ) : ℝ) := by
        unfold FinitenessCompletedNormalization.alpha
        push_cast
        ring
      rw [ha, Real.rpow_intCast, Complex.ofReal_zpow]
      rfl
    have hr := FinitenessAllLevelGoodCoefficients.fullCoefficients_good_mul
      hf.toEulerData p.property hpN k n
    rw [hpow] at hr
    simp only [ModularHecke.primeHeckeFactor, hpN, ite_false]
    exact (sub_eq_iff_eq_add.mp hr.symm).symm

/-- Fourier inversion of the actual unitary coefficients of an Mcirc form. -/
theorem modular_fourierFunction {N k : ℕ} [NeZero N] {hN : 0 < N} (F : space N hN k) :
    fourierFunction k (ModularLSeries.coefficients F.val) = (F.val : ℍ → ℂ) := by
  have hc : fullCoefficients (ModularLSeries.coefficients F.val) k =
      fun n => (qExpansion 1 F.val).coeff n := by
    funext n
    by_cases hn : n = 0
    · subst n
      have hzero : (qExpansion 1 F.val).coeff 0 = 0 := coefficient_zero N hN k F
      rw [fullCoefficients_zero (ModularLSeries.coefficients_zero F.val hzero), hzero]
    · exact ModularLSeries.coefficients_recover F.val n (Nat.pos_of_ne_zero hn)
  funext z
  change FinitenessPolynomialSeries.sum (fullCoefficients (ModularLSeries.coefficients F.val) k)
    (Function.Periodic.qParam 1 z) = F.val z
  rw [hc, FinitenessPolynomialSeries.sum_eq_tsum]
  exact (ModularForm.hasSum_qExpansion (f := F.val) zero_lt_one
    (AsymptoticClassicalCusp.level_one_period N) z).tsum_eq

/-- Arbitrary-level identification, independent of any small-level converse
theorem or eigenbasis existence: original modular solutions are exactly the
normalized simultaneous prime-Hecke eigenforms in the literal full Mcirc. -/
theorem original_modular_iff_normalized_eigenform {N k : ℕ} [NeZero N]
    (hN : 0 < N) (hk : 0 < k) (heven : Even k) (f : ℕ → ℂ) :
    (IsSolution N k f ∧ SmallLevelOriginal.IsModular N k f) ↔
      ∃ F : space N hN k, ModularLSeries.coefficients F.val = f ∧
        coefficient N hN k 1 F = 1 ∧
        ∃ e : Nat.Primes → ℂ, ∀ p : Nat.Primes,
          ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val := by
  constructor
  · rintro ⟨hf, hmod⟩
    obtain ⟨F, hF⟩ := original_modular_mem_space hN hk heven hf hmod
    refine ⟨F, original_unitary_coefficients hf F hF, ?_,
      (fun p => fullCoefficients f k p.val), original_prime_eigen hf F hF⟩
    rw [original_coefficient hf F hF]
    have hone := (FinitenessEulerIdentification.euler_arithmetic hf.toEulerData).1
    simp [fullCoefficients, FinitenessGrowthNormalization.normalized, hone]
  · rintro ⟨F, hc, hone, e, he⟩
    refine ⟨?_, F.val, ?_⟩
    · simpa only [hc] using eigenform_isSolution hk heven F hone e he
    · rw [← hc]
      exact (modular_fourierFunction F).symm

#print axioms original_unitary_coefficients
#print axioms original_prime_eigen
#print axioms modular_fourierFunction
#print axioms original_modular_iff_normalized_eigenform
end QuantitativeArithmeticSmallLevelCirc
