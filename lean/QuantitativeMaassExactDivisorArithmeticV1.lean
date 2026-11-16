module

public import QuantitativeMaassGeneratorCharacterRelationsV1
public import GridAdmissibleGapV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- Every odd divisor of an admissible level is squarefree. -/
theorem admissible_odd_divisor_squarefree (N Q : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (hQ : Q∣N) (hodd : ¬2∣Q) : Squarefree Q := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hsq
  by_cases hp2 : p=2
  · subst p
    exact hodd ((dvd_mul_right 2 2).trans hsq)
  · exact hN.2.2 p hp hp2 (by simpa only [pow_two] using hsq.trans hQ)

/-- At least one side of an exact-divisor factorization of an admissible
level is squarefree, so its sign reduces to simple-prime signs. -/
theorem admissible_exact_factor_squarefree (N D Q : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (hQD : Q*D=N) (hcop : Nat.Coprime Q D) : Squarefree Q ∨ Squarefree D := by
  by_cases h2 : 2∣Q
  · right
    apply admissible_odd_divisor_squarefree N D hN
      ⟨Q,by rw [←hQD,Nat.mul_comm]⟩
    intro hd
    have hh := Nat.dvd_gcd h2 hd
    rw [hcop.gcd_eq_one] at hh
    norm_num at hh
  · exact Or.inl (admissible_odd_divisor_squarefree N Q hN ⟨D,hQD.symm⟩ h2)

/-- Every prime in a squarefree exact divisor occurs simply in the level. -/
theorem squarefree_exact_prime_simple (N D Q p : ℕ) (hQD : Q*D=N)
    (hcop : Nat.Coprime Q D) (hQ : Squarefree Q) (hp : p.Prime) (hpQ : p∣Q) :
    p∈AsymptoticSectorSigns.simplePrimes N := by
  apply AsymptoticSectorSigns.mem_simplePrimes.mpr
  refine ⟨hp,hpQ.trans ⟨D,hQD.symm⟩,?_⟩
  intro hsq
  have hpc : Nat.Coprime p D := hcop.of_dvd_left hpQ
  have hdiv : p^2∣Q*D := hQD ▸ hsq
  have hpq : p^2∣Q := (hpc.pow_left 2).dvd_of_dvd_mul_right hdiv
  exact Nat.squarefree_iff_prime_squarefree.mp hQ p hp (by simpa only [pow_two] using hpq)

#print axioms admissible_odd_divisor_squarefree
#print axioms admissible_exact_factor_squarefree
#print axioms squarefree_exact_prime_simple

end QuantitativeMaass
