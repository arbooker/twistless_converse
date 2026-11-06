module

public import QuantitativeArithmeticShiftedSieveUpperV1
public import QuantitativeArithmeticShiftedDensityFinalResidueV1
public import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Filter Finset QuantitativeArithmeticShiftedSieveCRT
open QuantitativeArithmeticShiftedSieveProgression

/-- Actual prime count avoiding a finite packet of shifted divisors.
Primes belonging to the packet are excluded explicitly. -/
def packetAvoidanceCount (S : Finset ℕ) (Q n : ℕ) : ℝ := by
  classical
  exact ((n.primesBelow.filter (fun p => p ∉ S ∧
    ∀ l ∈ S, ¬(l : ℤ) ∣ ((p : ℤ)-(Q : ℤ)))).card : ℝ)

/-- Finite CRT avoidance combined with the proved fixed-modulus prime
upper bound. The cutoff may depend on the chosen packet; its coefficient
is the exact product of the allowed local proportions. -/
theorem eventually_packetAvoidanceCount_upper (S : Finset ℕ) (Q : ℕ)
    (hp : ∀ l ∈ S, l.Prime) (hQ : ∀ l ∈ S, ¬(l : ℤ) ∣ (Q : ℤ)) :
    ∀ᶠ n : ℕ in atTop, packetAvoidanceCount S Q n ≤
      65*(∏ l ∈ S, (1-1/((l : ℝ)-1)))*((n : ℝ)/Real.log n) := by
  classical
  let R : ℕ := ∏ l : S, (l : ℕ)
  have hR : 0 < R := prod_pos (fun l _ => (hp l l.property).pos)
  let : NeZero (∏ l : S, (l : ℕ)) := ⟨hR.ne'⟩
  let U := AllowedUnits (fun l : S => (l : ℕ)) (Q : ℤ)
  let : Fintype U := Fintype.ofInjective (fun u : U => (u.val : ZMod R)) (by
    intro u v huv
    apply Subtype.ext
    apply Units.ext
    exact huv)
  have hcop : Pairwise (fun i j : S => Nat.Coprime (i : ℕ) (j : ℕ)) := by
    intro i j hij
    apply (hp i i.property).coprime_iff_not_dvd.mpr
    intro hdiv
    rcases (Nat.dvd_prime (hp j j.property)).mp hdiv with he | he
    · exact (hp i i.property).ne_one he
    · exact hij (Subtype.ext he)
  have hQz (l : S) : (Q : ZMod (l : ℕ)) ≠ 0 := by
    intro hz
    apply hQ l l.property
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (Q : ℤ) (l : ℕ)).mp
    simpa only [Int.cast_natCast] using hz
  have hratio : (Nat.card U : ℝ)/(Nat.totient R : ℝ) =
      ∏ l ∈ S, (1-1/((l : ℝ)-1)) := by
    have hh := allowedUnits_totient_proportion (fun l : S => (l : ℕ))
      (fun l => hp l l.property) hcop (Q : ℤ)
      (fun l => by simpa only [Int.cast_natCast] using hQz l)
    calc
      _ = ∏ l : S, (1-1/(((l : ℕ) : ℝ)-1)) := hh
      _ = _ := Finset.prod_coe_sort S (fun l => (1-1/((l : ℝ)-1)))
  filter_upwards [eventually_progressionPrimeCount_upper R hR] with n hn
  let A : Finset ℕ := n.primesBelow.filter (fun p => p ∉ S ∧
    ∀ l ∈ S, ¬(l : ℤ) ∣ ((p : ℤ)-(Q : ℤ)))
  let B : U → Finset ℕ := fun u => (Icc 1 n).filter (fun p =>
    Nat.ModEq R p (u.val : ZMod R).val ∧ p.Prime)
  have hsub : A ⊆ Finset.univ.biUnion B := by
    intro p hpA
    obtain ⟨hpn, hpS, havoid⟩ := mem_filter.mp hpA
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hpn
    obtain ⟨u, hu⟩ := exists_allowedUnit_of_prime_avoiding S hp Q p hpp hpS havoid
    have hmod : Nat.ModEq R p (u.val : ZMod R).val := by
      apply (ZMod.natCast_eq_natCast_iff p (u.val : ZMod R).val R).mp
      rw [ZMod.natCast_zmod_val, hu]
    apply mem_biUnion.mpr
    refine ⟨u, mem_univ _, ?_⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.pos, Nat.le_of_lt hplt⟩, hmod, hpp⟩
  have hcount : (A.card : ℝ) ≤ ∑ u : U,
      (progressionPrimeCount R (u.val : ZMod R).val n : ℝ) := by
    have hh := (card_le_card hsub).trans (card_biUnion_le (s := Finset.univ) (t := B))
    exact_mod_cast hh
  change (A.card : ℝ) ≤ _
  calc
    _ ≤ ∑ u : U, (progressionPrimeCount R (u.val : ZMod R).val n : ℝ) := hcount
    _ ≤ ∑ _u : U, 65*(n : ℝ)/((Nat.totient R : ℝ)*Real.log n) := by
      apply sum_le_sum
      intro u _
      exact hn (u.val : ZMod R).val
    _ = (Nat.card U : ℝ)*(65*(n : ℝ)/((Nat.totient R : ℝ)*Real.log n)) := by
      simp [Nat.card_eq_fintype_card]
    _ = 65*((Nat.card U : ℝ)/(Nat.totient R : ℝ))*((n : ℝ)/Real.log n) := by ring
    _ = _ := by rw [hratio]

#print axioms eventually_packetAvoidanceCount_upper

end QuantitativeArithmetic
