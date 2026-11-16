module

public import SpanningCriterionConditionV1

@[expose] public section

namespace SpanningCriterion

open GridPrimeParts GridAdmissibleGap QuantitativeArithmeticRetainedPrimeChoice

theorem dvd_levelPart {N d s : ℕ} (hN : 0 < N) (hd : d ∣ N)
    (hs : ∀ p, p.Prime → p ∣ d → p ∣ s) : d ∣ levelPart N s := by
  have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hd hN).ne'
  apply (Nat.factorization_le_iff_dvd hd0 (part_ne_zero hN.ne' _)).mp
  rw [factorization_part]
  intro p
  simp only [Finsupp.filter_apply]
  by_cases hp : p ∣ s
  · rw [ite_eq_left hp]
    exact (Nat.factorization_le_iff_dvd hd0 hN.ne').mpr hd p
  · rw [ite_eq_right hp]
    by_cases hprime : p.Prime
    · rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hp (hs p hprime h))]
    · rw [Nat.factorization_eq_zero_of_not_prime d hprime]

theorem levelPart_eq_of_all_prime_divisors {N s : ℕ} (hN : 0 < N)
    (hs : ∀ p, p.Prime → p ∣ N → p ∣ s) : levelPart N s = N :=
  Nat.dvd_antisymm (part_dvd N _) (dvd_levelPart hN (dvd_refl N) hs)

theorem condition_of_admissible {N : ℕ} (hN : Admissible N) (P : Finset ℕ) :
    Condition N P := by
  intro s hs _
  have hh := level_gap hN hs
  nlinarith

theorem condition_empty_iff {N : ℕ} (hN : 0 < N) :
    Condition N ∅ ↔ ¬16 ∣ N ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p^2 ∣ N := by
  constructor
  · intro hc
    constructor
    · intro h16
      have hd : 16 ∣ levelPart N 4 := dvd_levelPart hN h16 (by
        intro p hp hpd
        have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (by simpa using hpd : p ∣ 2^4)
        have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
        subst p
        decide)
      have hh := hc 4 (by decide) (by simp)
      have hle : 16 ≤ levelPart N 4 := Nat.le_of_dvd (Nat.pos_of_ne_zero (part_ne_zero hN.ne' _)) hd
      norm_num at hh
      omega
    · intro p hp hp2 hpd
      have hs : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
      have hd : p^2 ∣ levelPart N p := dvd_levelPart hN hpd (by
        intro q hq hqd
        exact hq.dvd_of_dvd_pow hqd)
      have hh := hc p hs (by simp)
      have hle : p^2 ≤ levelPart N p := Nat.le_of_dvd (Nat.pos_of_ne_zero (part_ne_zero hN.ne' _)) hd
      omega
  · intro hh
    exact condition_of_admissible ⟨hN,hh⟩ ∅

theorem condition_primeFactors_iff {N : ℕ} (hN : 0 < N) :
    Condition N N.primeFactors ↔ N ∣ 8 ∨ N < (∏ p ∈ N.primeFactors, p)^2 := by
  classical
  let r := ∏ p ∈ N.primeFactors, p
  have hpr : ∀ p ∈ N.primeFactors, p ∣ r := fun p hp =>
    Finset.dvd_prod_of_mem (fun p => p) hp
  constructor
  · intro hc
    by_cases hr : 2 < r
    · right
      have hh := hc r hr hpr
      have he : levelPart N r = N := levelPart_eq_of_all_prime_divisors hN (by
        intro p hp hpd
        exact hpr p (Nat.mem_primeFactors.mpr ⟨hp,hpd,hN.ne'⟩))
      simpa only [he] using hh
    · left
      have hrle : r ≤ 2 := by omega
      have hrpos : 0 < r := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
      have htwo : ∀ p, p.Prime → p ∣ N → p = 2 := by
        intro p hp hpd
        have hle := (Nat.le_of_dvd hrpos (hpr p (Nat.mem_primeFactors.mpr ⟨hp,hpd,hN.ne'⟩))).trans hrle
        have hh := hp.two_le
        omega
      have hfour : ∀ p ∈ N.primeFactors, p ∣ 4 := by
        intro p hp
        rw [htwo p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
        decide
      have he : levelPart N 4 = N := levelPart_eq_of_all_prime_divisors hN (by
        intro p hp hpd
        rw [htwo p hp hpd]
        decide)
      have hn16 := hc 4 (by decide) hfour
      rw [he] at hn16
      have hexp : N.factorization 2 ≤ 3 := by
        by_contra hh
        have hd : 16 ∣ N := by
          have hd := (Nat.prime_two.pow_dvd_iff_le_factorization hN.ne').mpr
            (by omega : 4 ≤ N.factorization 2)
          simpa using hd
        have hle := Nat.le_of_dvd hN hd
        norm_num at hn16
        omega
      apply (Nat.factorization_le_iff_dvd hN.ne' (by decide : 8 ≠ 0)).mp
      intro p
      by_cases hp2 : p = 2
      · subst p
        simpa only [show 8 = 2^3 from rfl, Nat.prime_two.factorization_pow,
          Finsupp.single_eq_same] using hexp
      · have hz : N.factorization p = 0 := by
          by_cases hp : p.Prime
          · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hp2 (htwo p hp hd))
          · exact Nat.factorization_eq_zero_of_not_prime N hp
        rw [hz]
        exact Nat.zero_le _
  · rintro (h8 | hlarge)
    · apply condition_of_admissible (N:=N) _ N.primeFactors
      refine ⟨hN,?_,?_⟩
      · intro h16
        have hh := h16.trans h8
        norm_num at hh
      · intro p hp hp2 hpd
        have hd : p ∣ 8 := (dvd_pow_self p (by omega : 2 ≠ 0)).trans (hpd.trans h8)
        have hp' : p ∣ 2 := hp.dvd_of_dvd_pow (by simpa using hd : p ∣ 2^3)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp')
    · exact condition_of_product hN N.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp) hlarge

theorem condition_singleton {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hlarge : N < p^2) : Condition N {p} := by
  apply condition_of_product hN {p}
  · intro q hq
    simpa only [Finset.mem_singleton.mp hq] using hp
  · simpa using hlarge

#print axioms condition_empty_iff
#print axioms condition_primeFactors_iff
#print axioms condition_singleton

end SpanningCriterion
