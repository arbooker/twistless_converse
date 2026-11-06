module

public import GridPrimePartsV1

@[expose] public section

namespace GridAdmissibleGap

open GridPrimeParts

def Admissible (N : ℕ) : Prop := 0<N ∧ ¬16∣N ∧ ∀p:ℕ,p.Prime → p≠2 → ¬p^2∣N

theorem odd_exponent_le_one {N p : ℕ} (hN : Admissible N) (hp : p.Prime) (hp2 : p≠2) :
    N.factorization p≤1 := by
  have hh := hN.2.2 p hp hp2
  rw [hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hN.1)] at hh
  omega

theorem two_exponent_le_three {N : ℕ} (hN : Admissible N) : N.factorization 2≤3 := by
  have hh : ¬2^4∣N := by simpa using hN.2.1
  rw [Nat.prime_two.pow_dvd_iff_le_factorization (Nat.ne_of_gt hN.1)] at hh
  omega

def levelPart (N s : ℕ) : ℕ := primePart N (fun p => p∣s)

theorem levelPart_dvd_scaled {N s k : ℕ} (hN : Admissible N) (hs : 0<s)
    (h2 : 2∣s → N.factorization 2≤k+s.factorization 2) :
    levelPart N s∣2^k*s := by
  have hN0 := Nat.ne_of_gt hN.1
  have hs0 := Nat.ne_of_gt hs
  apply (Nat.factorization_le_iff_dvd (part_ne_zero hN0 _) (by positivity : 2^k*s≠0)).mp
  rw [factorization_part,Nat.factorization_mul (by positivity) hs0,
    Nat.prime_two.factorization_pow]
  intro p
  simp only [Finsupp.filter_apply,Finsupp.add_apply,Finsupp.single_apply]
  by_cases hps : p∣s
  · rw [ite_eq_left hps]
    by_cases hp2 : p=2
    · subst p
      simpa using h2 hps
    · rw [ite_eq_right (Ne.symm hp2),zero_add]
      by_cases hp : p.Prime
      · have h1 := odd_exponent_le_one hN hp hp2
        have h2 := hp.factorization_pos_of_dvd hs0 hps
        omega
      · rw [Nat.factorization_eq_zero_of_not_prime N hp]
        exact Nat.zero_le _
  · rw [ite_eq_right hps]
    exact Nat.zero_le _

theorem level_gap {N s : ℕ} (hN : Admissible N) (hs : 2<s) :
    3*levelPart N s≤2*s^2 := by
  have hs0 : 0<s := by omega
  have hN2 := two_exponent_le_three hN
  by_cases hodd : ¬2∣s
  · have hdvd := levelPart_dvd_scaled (k:=0) hN hs0 (fun h => False.elim (hodd h))
    simp only [pow_zero,one_mul] at hdvd
    have hle := Nat.le_of_dvd hs0 hdvd
    nlinarith
  · have heven : 2∣s := not_not.mp hodd
    by_cases hfour : 4∣s
    · have hs2 : 2≤s.factorization 2 := (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.ne_of_gt hs0)).mp
        (by simpa using hfour)
      have hdvd := levelPart_dvd_scaled (k:=1) hN hs0 (fun _ => by omega)
      simp only [pow_one] at hdvd
      have hle := Nat.le_of_dvd (by omega : 0<2*s) hdvd
      have hs4 := Nat.le_of_dvd hs0 hfour
      nlinarith
    · have hs2 := Nat.prime_two.factorization_pos_of_dvd (Nat.ne_of_gt hs0) heven
      have hdvd := levelPart_dvd_scaled (k:=2) hN hs0 (fun _ => by omega)
      have hle := Nat.le_of_dvd (by positivity : 0<2^2*s) hdvd
      have hne : s≠4 := by intro h; subst s; exact hfour (dvd_refl 4)
      obtain ⟨t,ht⟩ := heven
      have hs6 : 6≤s := by omega
      nlinarith

#print axioms levelPart_dvd_scaled
#print axioms level_gap

end GridAdmissibleGap
