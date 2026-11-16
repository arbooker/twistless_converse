module

public import GridSelectedWindowsV1
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

namespace QuantitativeArithmeticRetainedPrimeChoice

open GridPrimeParts GridAdmissibleGap GridLabelDetection GridSelectedWindows

/-- Distinct prime divisors divide simultaneously. -/
theorem prime_product_dvd {P : Finset ℕ} {s : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hs : ∀ p ∈ P, p ∣ s) : (∏ p ∈ P, p) ∣ s := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp]
    have hp' : p.Prime := hP p (Finset.mem_insert_self _ _)
    have hc : Nat.Coprime p (∏ q ∈ P, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact hp'.coprime_iff_not_dvd.mpr (by
        intro hd
        have he := (hP q (Finset.mem_insert_of_mem hq)).eq_one_or_self_of_dvd p hd
        rcases he with he | he
        · exact hp'.ne_one he
        · exact hp (he ▸ hq))
    exact hc.mul_dvd_of_dvd_of_dvd (hs p (Finset.mem_insert_self _ _))
      (ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
        (fun q hq => hs q (Finset.mem_insert_of_mem hq)))

def GoodLabel (N : ℕ) {G : ℕ} (a : Fin G) : Prop :=
  levelPart N (labelOrder a) < (labelOrder a)^2

#print axioms prime_product_dvd

end QuantitativeArithmeticRetainedPrimeChoice
