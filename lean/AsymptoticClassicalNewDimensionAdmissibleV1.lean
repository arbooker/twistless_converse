module

public import AsymptoticClassicalNewDimensionPrimesV1
public import GridAdmissibleGapV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

/-- All distinct prime divisors, for levels without a repeated factor. -/
def allPrimeList (N : ℕ) : List ℕ := N.primeFactors.toList

/-- The simply ramified odd primes, leaving the repeated-2 condition as base. -/
def oddPrimeList (N : ℕ) : List ℕ := (N.primeFactors.erase 2).toList

theorem prime_coprime_div_of_square_not_dvd {N p : ℕ} (hp : p.Prime)
    (hd : p ∣ N) (hs : ¬p ^ 2 ∣ N) : p.Coprime (N / p) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  apply hs
  have hh := Nat.mul_dvd_mul_left p h
  simpa only [← pow_two, Nat.mul_div_cancel' hd] using hh

theorem allPrimeList_simple (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (h4 : ¬4 ∣ N) : SimplePrimesAt (allPrimeList N) N := by
  refine ⟨Finset.nodup_toList _, ?_⟩
  intro p hp
  have hm : p ∈ N.primeFactors := Finset.mem_toList.mp hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hm
  refine ⟨hpp, hpd, prime_coprime_div_of_square_not_dvd hpp hpd ?_⟩
  by_cases he : p = 2
  · simpa only [he, show 2 ^ 2 = 4 by decide] using h4
  · exact hN.2.2 p hpp he

theorem oddPrimeList_simple (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    SimplePrimesAt (oddPrimeList N) N := by
  refine ⟨Finset.nodup_toList _, ?_⟩
  intro p hp
  obtain ⟨hp2, hpf⟩ := Finset.mem_erase.mp (Finset.mem_toList.mp hp)
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hpf
  exact ⟨hpp, hpd, prime_coprime_div_of_square_not_dvd hpp hpd (hN.2.2 p hpp hp2)⟩

theorem oddPrimeList_coprime_four (N p : ℕ) (hp : p ∈ oddPrimeList N) : p.Coprime 4 := by
  obtain ⟨hp2, hpf⟩ := Finset.mem_erase.mp (Finset.mem_toList.mp hp)
  have hpp := (Nat.mem_primeFactors.mp hpf).1
  apply hpp.coprime_iff_not_dvd.mpr
  intro hd
  have hd2 : p ∣ 2 := hpp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hd)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hd2)

theorem oddPrimeList_ne_two (N p : ℕ) (hp : p ∈ oddPrimeList N) : p ≠ 2 :=
  (Finset.mem_erase.mp (Finset.mem_toList.mp hp)).1

theorem allPrimeList_covers (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hd : p ∣ N) :
    p ∈ allPrimeList N :=
  Finset.mem_toList.mpr (Nat.mem_primeFactors.mpr ⟨hp, hd, hN.ne'⟩)

theorem oddPrimeList_covers (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hd : p ∣ N) :
    p ∈ oddPrimeList N ∨ p = 2 := by
  by_cases he : p = 2
  · exact Or.inr he
  · exact Or.inl (Finset.mem_toList.mpr
      (Finset.mem_erase.mpr ⟨he, Nat.mem_primeFactors.mpr ⟨hp, hd, hN.ne'⟩⟩))

#print axioms prime_coprime_div_of_square_not_dvd
#print axioms allPrimeList_simple
#print axioms oddPrimeList_simple
#print axioms oddPrimeList_coprime_four
#print axioms oddPrimeList_ne_two
#print axioms allPrimeList_covers
#print axioms oddPrimeList_covers

end AsymptoticClassicalDimension
