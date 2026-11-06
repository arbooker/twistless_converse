module

public import AsymptoticClassicalHeckeTraceSumV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticAtkinLehner AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups

/-- Scalar normalization converts literal dilation to Mathlib's slash translate. -/
theorem scaled_degeneracy_coe (N p : ℕ) (hp : 0 < p) (k : ℤ)
    (f : CuspForm (level N) k) :
    (p : ℂ) ^ (k - 1) • (degeneracy N p hp k f : ℍ → ℂ) =
      (f : ℍ → ℂ) ∣[k] dilationReal p hp := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  change (p : ℂ) ^ (k - 1) • ((p : ℂ) ^ (1 - k) •
    ((f : ℍ → ℂ) ∣[k] dilationReal p hp)) = _
  rw [smul_smul, ← zpow_add₀ hpC]
  simp

/-- The classical good-prime operator expressed by its p+1 upper-triangular
 representatives. This follows from the concrete trace, not a prescribed action. -/
theorem dilationTrace_prime_slash (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (k : ℤ)
    (f : CuspForm (level N) k) :
    (dilationTrace N p (Fact.out : p.Prime).pos k f : ℍ → ℂ) =
      (f : ℍ → ℂ) ∣[k] dilationReal p (Fact.out : p.Prime).pos +
        ∑ a : Fin p, (f : ℍ → ℂ) ∣[k]
          triangularGL 1 a.val p (by norm_num) (by exact_mod_cast (Fact.out : p.Prime).pos) := by
  let hp := (Fact.out : p.Prime).pos
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  change (p : ℂ) ^ (k - 1) •
    (arithmeticTrace (level (p * N)) (level N) k (degeneracy N p hp k f) : ℍ → ℂ) = _
  rw [arithmeticTrace_prime_sum N p hN hpN A B hAB k, smul_add, Finset.smul_sum,
    scaled_degeneracy_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← ModularForm.SL_smul_slash, scaled_degeneracy_coe, ModularForm.SL_slash,
    ← SlashAction.slash_mul]
  change (f : ℍ → ℂ) ∣[k] (dilationReal p hp *
    SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB a.val)) = _
  rw [dilation_traceSL, SlashAction.slash_mul]
  have hinv : (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB) =
      (f : ℍ → ℂ) := f.slash_action_eq' _ ⟨_, heckeSL_mem N p A B hAB, rfl⟩
  rw [hinv]
  simp only [Int.cast_natCast]

#print axioms scaled_degeneracy_coe
#print axioms dilationTrace_prime_slash

end AsymptoticClassicalCusp
