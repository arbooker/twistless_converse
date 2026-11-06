module

public import AsymptoticClassicalHeckeFormulaV1
public import AsymptoticClassicalHeckeAverageV1
public import AsymptoticClassicalEigenCoefficientsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups

/-- The pointwise classical T_p formula, derived from the trace correspondence. -/
theorem dilationTrace_prime_apply (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (k : ℤ)
    (f : CuspForm (level N) k) (z : ℍ) :
    dilationTrace N p (Fact.out : p.Prime).pos k f z =
      (p : ℂ) ^ (k - 1) * f (dilationReal p (Fact.out : p.Prime).pos • z) +
        heckeAverage p (Fact.out : p.Prime).pos f z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ht : triangularFactor 1 p k = (p : ℂ)⁻¹ := by
    simp only [triangularFactor, one_mul, Complex.ofReal_natCast]
    rw [← zpow_add₀ hpC, show k - 1 + -k = -1 by omega, _root_.zpow_neg_one]
  have hf := congrFun (dilationTrace_prime_slash N p hN hpN A B hAB k f) z
  rw [← scaled_degeneracy_coe N p (Fact.out : p.Prime).pos k f] at hf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, degeneracy_apply,
    Finset.sum_apply, slash_triangular, ht] at hf
  rw [← Finset.mul_sum] at hf
  exact hf

/-- The exact good-prime Fourier-coefficient law for the concrete operator. -/
theorem coeff_dilationTrace (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (k : ℤ)
    (f : CuspForm (level N) k) (n : ℕ) :
    cuspCoefficient N k n (dilationTrace N p (Fact.out : p.Prime).pos k f) =
      cuspCoefficient N k (p * n) f + (p : ℂ) ^ (k - 1) *
        if p ∣ n then cuspCoefficient N k (n / p) f else 0 := by
  let hp := (Fact.out : p.Prime).pos
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  change (qExpansion 1 (dilationTrace N p hp k f)).coeff n = _
  symm
  apply ModularFormClass.qExpansion_coeff_unique
    (f := dilationTrace N p hp k f)
    (c := fun n => cuspCoefficient N k (p * n) f + (p : ℂ) ^ (k - 1) *
      if p ∣ n then cuspCoefficient N k (n / p) f else 0)
    zero_lt_one (level_one_period N) (m := n)
  intro z
  rw [dilationTrace_prime_apply N p hN hpN A B hAB k f z, add_comm]
  have ha := hasSum_heckeAverage p hp f (fun m => cuspCoefficient N k m f)
    (fun z => ModularForm.hasSum_qExpansion (f := f) zero_lt_one (level_one_period N) z) z
  have hd := ModularForm.hasSum_qExpansion (f := degeneracy N p hp k f)
    zero_lt_one (level_one_period (p * N)) z
  simp_rw [coeff_degeneracy, degeneracy_apply] at hd
  apply (ha.add (hd.mul_left ((p : ℂ) ^ (k - 1)))).congr_fun
  intro m
  simp only [cuspCoefficient_apply, smul_eq_mul]
  ring

#print axioms dilationTrace_prime_apply
#print axioms coeff_dilationTrace

end AsymptoticClassicalCusp
