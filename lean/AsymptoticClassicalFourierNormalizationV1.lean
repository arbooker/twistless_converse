module

public import AsymptoticClassicalFiniteDimensionV1
public import FinitenessGrowthNormalizationV1
public import Mathlib.NumberTheory.ModularForms.LFunction

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane Filter Asymptotics AsymptoticClassicalCusp

variable {N : ℕ} {k : ℤ}

/-- The unitary normalization of the actual Fourier coefficients. -/
def coefficients (f : CuspForm (level N) k) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n * ((n : ℝ) ^ (-((k : ℝ) - 1) / 2) : ℝ)

@[simp] theorem coefficients_zero (f : CuspForm (level N) k) : coefficients f 0 = 0 := by
  rw [coefficients, CuspFormClass.qExpansion_coeff_zero f zero_lt_one (level_one_period N), zero_mul]

@[simp] theorem coefficients_one (f : CuspForm (level N) k) :
    coefficients f 1 = (qExpansion 1 f).coeff 1 := by simp [coefficients]

theorem coefficients_recover (f : CuspForm (level N) k) (n : ℕ) (hn : 0 < n) :
    coefficients f n * ((n : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) = (qExpansion 1 f).coeff n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [coefficients, mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hnR]
  rw [show -((k : ℝ) - 1) / 2 + ((k : ℝ) - 1) / 2 = 0 by ring]
  simp

/-- The normalized sequence still determines the original cusp form. -/
theorem coefficients_injective : Function.Injective
    (coefficients : CuspForm (level N) k → ℕ → ℂ) := by
  intro f g he
  apply CuspForm.toModularFormₗ_injective
  apply ModularForm.qExpansion_injective zero_lt_one (level_one_period N)
  ext n
  by_cases hn : n = 0
  · subst n
    exact (CuspFormClass.qExpansion_coeff_zero f zero_lt_one (level_one_period N)).trans
      (CuspFormClass.qExpansion_coeff_zero g zero_lt_one (level_one_period N)).symm
  · have hf := coefficients_recover f n (Nat.pos_of_ne_zero hn)
    have hg := coefficients_recover g n (Nat.pos_of_ne_zero hn)
    rw [he] at hf
    exact hf.symm.trans hg

/-- The elementary Hecke coefficient bound suffices for the growth
 hypothesis of the complex Euler-product predicate. -/
theorem coefficients_isBigO [NeZero N] (f : CuspForm (level N) k) :
    coefficients f =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) := by
  have ha : (fun n => (qExpansion 1 f).coeff n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((k : ℝ) / 2)) := by
    simpa only [level, CongruenceSubgroup.strictWidthInfty_Gamma0] using
      CuspFormClass.qExpansion_isBigO f
  obtain ⟨C, _, hb⟩ := bound_of_isBigO_nat_atTop ha
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb' : ‖(qExpansion 1 f).coeff n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hnR _)] using
      hb (Real.rpow_pos_of_pos hnR ((k : ℝ) / 2)).ne'
  calc
    ‖coefficients f n‖ = ‖(qExpansion 1 f).coeff n‖ * (n : ℝ) ^ (-((k : ℝ) - 1) / 2) := by
      simp only [coefficients, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hnR _)]
    _ ≤ (C * (n : ℝ) ^ ((k : ℝ) / 2)) * (n : ℝ) ^ (-((k : ℝ) - 1) / 2) :=
      mul_le_mul_of_nonneg_right hb' (Real.rpow_pos_of_pos hnR _).le
    _ = C * ‖(n : ℝ) ^ (1 / 2 : ℝ)‖ := by
      rw [mul_assoc, ← Real.rpow_add hnR,
        show (k : ℝ) / 2 + -((k : ℝ) - 1) / 2 = 1 / 2 by ring,
        Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hnR _)]

theorem coefficients_growth [NeZero N] (f : CuspForm (level N) k) :
    ∃ σ : ℝ, 0 < σ ∧ coefficients f =O[atTop] (fun n : ℕ => (n : ℝ) ^ σ) :=
  ⟨1 / 2, by norm_num, coefficients_isBigO f⟩

#print axioms coefficients_zero
#print axioms coefficients_one
#print axioms coefficients_recover
#print axioms coefficients_injective
#print axioms coefficients_isBigO
#print axioms coefficients_growth

end AsymptoticClassicalLSeries
