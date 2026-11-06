module

public import QuantitativeArithmeticShiftedSieveCRTV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Finset QuantitativeArithmeticShiftedSieveCRT
open scoped BigOperators

/-- A prime outside the auxiliary packet which avoids the shifted divisor
condition gives an actual allowed reduced residue class under the CRT. -/
theorem exists_allowedUnit_of_prime_avoiding
    (S : Finset ℕ) (hp : ∀ l ∈ S, l.Prime) (Q p : ℕ)
    (hpp : p.Prime) (hpS : p ∉ S)
    (havoid : ∀ l ∈ S, ¬ (l : ℤ) ∣ ((p : ℤ) - (Q : ℤ))) :
    ∃ u : AllowedUnits (fun l : S => (l : ℕ)) (Q : ℤ),
      (u.val : ZMod (∏ l : S, (l : ℕ))) = (p : ZMod (∏ l : S, (l : ℕ))) := by
  classical
  have hcop : Pairwise (fun i j : S => Nat.Coprime (i : ℕ) (j : ℕ)) := by
    intro i j hij
    exact (hp i i.property).coprime_iff_not_dvd.mpr (by
      intro hdiv
      rcases (Nat.dvd_prime (hp j j.property)).mp hdiv with he | he
      · exact (hp i i.property).ne_one he
      · exact hij (Subtype.ext he))
  have hnz (l : S) : (p : ZMod (l : ℕ)) ≠ 0 := by
    intro hz
    have hd : (l : ℕ) ∣ p := (ZMod.natCast_eq_zero_iff p (l : ℕ)).mp hz
    rcases (Nat.dvd_prime hpp).mp hd with he | he
    · exact (hp l l.property).ne_one he
    · exact hpS (he ▸ l.property)
  have hu : IsUnit (p : ZMod (∏ l : S, (l : ℕ))) := by
    apply (isUnit_iff_coordinates (fun l : S => (l : ℕ))
      (fun l => hp l l.property) hcop _).mpr
    intro l
    simpa only [map_natCast] using hnz l
  obtain ⟨u, hu⟩ := hu
  refine ⟨⟨u, ?_⟩, hu⟩
  intro l he
  rw [hu, map_natCast] at he
  have hz : (((p : ℤ) - (Q : ℤ) : ℤ) : ZMod (l : ℕ)) = 0 := by
    push_cast
    exact sub_eq_zero.mpr (by simpa only [Int.cast_natCast] using he)
  exact havoid l l.property ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)

#print axioms exists_allowedUnit_of_prime_avoiding

end QuantitativeArithmetic
