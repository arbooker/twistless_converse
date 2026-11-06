module

public import AsymptoticClassicalHeckeOldIntertwineV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.CuspSpectral

open UpperHalfPlane AsymptoticClassicalCusp

/-- A cusp form cannot be proportional to its proper dilation.  This uses
the actual Fourier coefficients, including their vanishing constant term. -/
theorem degeneracy_proportional_zero (N p : ℕ) [NeZero N]
    (hp : 1 < p) (k : ℤ) (c : ℂ) (f : CuspForm (level N) k)
    (h : c • degeneracy N p (by omega) k f =
      restrict k (level_antitone (dvd_mul_left N p)) f) : f = 0 := by
  apply cuspCoefficient_separates N k f
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      exact CuspFormClass.qExpansion_coeff_zero f zero_lt_one (level_one_period N)
    have he := congrArg (cuspCoefficient (p * N) k n) h
    rw [map_smul, cuspCoefficient_degeneracy,
      cuspCoefficient_restrict (p * N) N (dvd_mul_left N p)] at he
    by_cases hpn : p ∣ n
    · simp only [hpn, ite_true,
        ih (n / p) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp), smul_zero] at he
      exact he.symm
    · simpa only [hpn, ite_false, smul_zero] using he.symm

#print axioms degeneracy_proportional_zero

end QuantitativeArithmeticSmallLevelCirc.CuspSpectral
