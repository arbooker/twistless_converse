module

public import AsymptoticClassicalFourierNormalizationV1
public import FinitenessOriginalInputV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane Complex Filter AsymptoticClassicalCusp

variable {N : ℕ} {k : ℤ}

theorem coefficient_dirichlet_term (f : CuspForm (level N) k) (n : ℕ) (hn : 0 < n) (s : ℂ) :
    coefficients f n * (n : ℂ) ^ (-s) =
      (qExpansion 1 f).coeff n * (n : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [coefficients, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast,
    mul_assoc, ← Complex.cpow_add _ _ hnC]
  congr 2
  push_cast
  ring

theorem mellin_dirichlet_term (f : CuspForm (level N) k) (n : ℕ) (hn : 0 < n) (s : ℂ) :
    (Real.pi : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) * Gamma (s + ((k : ℂ) - 1) / 2) *
      (qExpansion 1 f).coeff n / (2 * (n : ℝ) : ℝ) ^ (s + ((k : ℂ) - 1) / 2) =
    ((2 * Real.pi : ℝ) : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) *
      Gamma (s + ((k : ℂ) - 1) / 2) * (coefficients f n * (n : ℂ) ^ (-s)) := by
  rw [coefficient_dirichlet_term f n hn s]
  simp only [Complex.ofReal_mul]
  rw [    Complex.mul_cpow_ofReal_nonneg zero_le_two (Nat.cast_nonneg n),
    Complex.mul_cpow_ofReal_nonneg zero_le_two Real.pi_pos.le]
  simp only [Complex.ofReal_ofNat, Complex.ofReal_natCast, div_eq_mul_inv, mul_inv_rev,
    ← Complex.cpow_neg]
  ring

/-- The entire completion supplied by the classical cusp-form Mellin
 transform, with precisely the conductor and weight normalization of E(N,k). -/
def entireCompletion (N k : ℕ) [NeZero N] (hk : 0 < k) (f : CuspForm (level N) (k : ℤ))
    (s : ℂ) : ℂ :=
  2 * (N : ℂ) ^ ((s - 1 / 2) / 2) *
    ModularForm.Λ (by exact_mod_cast hk) f (s + ((k : ℂ) - 1) / 2)

theorem entireCompletion_differentiable (N k : ℕ) [NeZero N] (hk : 0 < k)
    (f : CuspForm (level N) (k : ℤ)) : Differentiable ℂ (entireCompletion N k hk f) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hp : Differentiable ℂ (fun s : ℂ => (N : ℂ) ^ ((s - 1 / 2) / 2)) := by
    simp only [Complex.cpow_def_of_ne_zero hN]
    fun_prop
  have hΛ := CuspForm.differentiable_Λ (by exact_mod_cast hk : (0 : ℤ) < k) f
  exact ((differentiable_const _).mul hp).mul
    (hΛ.comp (differentiable_id.add (differentiable_const _)))

/-- The entire classical Mellin completion agrees with the actual
 Dirichlet-series completion on a right half-plane. -/
theorem entireCompletion_eq_completed (N k : ℕ) [NeZero N] (hk : 0 < k)
    (f : CuspForm (level N) (k : ℤ)) (s : ℂ) (hs : 2 < s.re) :
    entireCompletion N k hk f s = FinitenessOriginalInput.completed N k (coefficients f) s := by
  let z : ℂ := s + ((k : ℂ) - 1) / 2
  have hsz : (k : ℝ) / 2 + 1 < z.re := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re,
      Complex.one_re]
    linarith
  have hh := CuspForm.hasSum_Λ f (by exact_mod_cast hk : (0 : ℤ) < k) (s := z) hsz
  simp only [level, CongruenceSubgroup.strictWidthInfty_Gamma0, div_one] at hh
  have hh' : HasSum (fun n : ℕ => (Real.pi : ℂ) ^ (-z) * Gamma z *
      (qExpansion 1 f).coeff (n + 1) / (2 * (n + 1 : ℕ) : ℝ) ^ z)
      (ModularForm.Λ (by exact_mod_cast hk) f z) := by
    apply (hasSum_nat_add_iff 1 (f := fun n : ℕ => (Real.pi : ℂ) ^ (-z) * Gamma z *
      (qExpansion 1 f).coeff n / (2 * (n : ℝ) : ℝ) ^ z)).mpr
    simpa only [Finset.sum_range_one, CuspFormClass.qExpansion_coeff_zero f zero_lt_one
      (level_one_period N), mul_zero, zero_div, add_zero] using hh
  have hterms : (fun n : ℕ => (Real.pi : ℂ) ^ (-z) * Gamma z *
      (qExpansion 1 f).coeff (n + 1) / (2 * (n + 1 : ℕ) : ℝ) ^ z) =
      (fun n : ℕ => ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Gamma z *
        (coefficients f (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s))) := by
    funext n
    exact mellin_dirichlet_term f (n + 1) (Nat.succ_pos n) s
  rw [hterms] at hh'
  have he := hh'.tsum_eq.symm
  rw [tsum_mul_left] at he
  change ModularForm.Λ _ f z = ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Gamma z *
    FinitenessOriginalInput.L (coefficients f) s at he
  unfold entireCompletion FinitenessOriginalInput.completed FinitenessOriginalInput.gammaC
  change 2 * (N : ℂ) ^ ((s - 1 / 2) / 2) * ModularForm.Λ _ f z = _
  rw [he]
  dsimp [z]
  ring

#print axioms coefficient_dirichlet_term
#print axioms mellin_dirichlet_term
#print axioms entireCompletion_differentiable
#print axioms entireCompletion_eq_completed

end AsymptoticClassicalLSeries
