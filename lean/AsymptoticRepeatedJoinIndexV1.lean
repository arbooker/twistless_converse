module

public import AsymptoticDegeneracyContainmentV1
public import AsymptoticPrimeIndexJoinV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels AsymptoticRamifiedCosets AsymptoticIntegralSubgroup

/-- Index of the common containing group at a repeated prime factor. -/
theorem double_degeneracy_index (L p : ℕ) (hL : 0<L) (hp : 0<p) :
    (gamma (p*(p*L))).relIndex (degeneracyGroup L p hp)=
      p*(gamma (p*L)).relIndex (gamma L) := by
  have hi : (gamma (p*(p*L))).relIndex (degeneracyGroup (p*L) p hp)=p := by
    rw [degeneracyGroup_index (p*L) p (Nat.mul_pos hp hL) hp]
    exact projective_index (p*L) p (Nat.mul_pos hp hL) hp (Nat.dvd_mul_right p L)
  have he := Subgroup.relIndex_mul_relIndex (gamma (p*(p*L))) (degeneracyGroup (p*L) p hp)
    (degeneracyGroup L p hp) (gamma_le_degeneracyGroup (p*L) p (Nat.mul_pos hp hL) hp)
    (degeneracyGroup_mono hp (Nat.dvd_mul_left L p))
  rw [hi,degeneracyGroup_relIndex] at he
  exact he.symm

theorem lower_degeneracy_index (L p : ℕ) (hL : 0<L) (hp : 0<p) :
    (gamma (p*L)).relIndex (degeneracyGroup L p hp)=(gamma (p*L)).relIndex (gamma L) := by
  have he := Subgroup.relIndex_mul_relIndex (gamma (p*(p*L))) (gamma (p*L)) (degeneracyGroup L p hp)
    (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p)) (gamma_le_degeneracyGroup L p hL hp)
  rw [projective_index (p*L) p (Nat.mul_pos hp hL) hp (Nat.dvd_mul_right p L),
    double_degeneracy_index L p hL hp] at he
  exact Nat.eq_of_mul_eq_mul_left hp he

/-- The generated overgroup is the expected two-step degeneracy group
whenever the intervening relative index is prime. -/
theorem repeated_join_eq (L p : ℕ) [Fact p.Prime] (hL : 0<L)
    (hr : ((gamma (p*L)).relIndex (gamma L)).Prime) :
    gamma (p*L)⊔degeneracyGroup (p*L) p (Fact.out : p.Prime).pos=
      degeneracyGroup L p (Fact.out : p.Prime).pos := by
  apply AsymptoticPrimeIndexJoin.sup_eq_of_prime_relIndex
    (gamma (p*L)) (degeneracyGroup (p*L) p (Fact.out : p.Prime).pos)
    (degeneracyGroup L p (Fact.out : p.Prime).pos)
    (gamma_le_degeneracyGroup L p hL (Fact.out : p.Prime).pos)
    (degeneracyGroup_mono (Fact.out : p.Prime).pos (Nat.dvd_mul_left L p))
  · rwa [lower_degeneracy_index L p hL (Fact.out : p.Prime).pos]
  · intro h
    exact fractional_translation_not_mem (p*L) p
      (h (fractional_translation_mem_degeneracy (p*L) p (Fact.out : p.Prime).pos))

theorem repeated_join_index (L p : ℕ) [Fact p.Prime] (hL : 0<L)
    (hr : ((gamma (p*L)).relIndex (gamma L)).Prime) :
    (gamma (p*(p*L))).relIndex
      (gamma (p*L)⊔degeneracyGroup (p*L) p (Fact.out : p.Prime).pos)=
        p*(gamma (p*L)).relIndex (gamma L) := by
  rw [repeated_join_eq L p hL hr,double_degeneracy_index L p hL (Fact.out : p.Prime).pos]

/-- The index-six intersection correction at exponent two of 2. -/
theorem square_two_join_index (L : ℕ) (hL : 0<L) (hodd : ¬2∣L) :
    (gamma (2*(2*L))).relIndex
      (gamma (2*L)⊔degeneracyGroup (2*L) 2 (by norm_num))=6 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : (gamma (2*L)).relIndex (gamma L)=3 :=
    projective_index_coprime L 2 hL Nat.prime_two (Nat.prime_two.coprime_iff_not_dvd.mpr hodd)
  rw [repeated_join_index L 2 hL (by rw [hr]; norm_num),hr]

/-- At higher repeated exponents the generated group has index p². -/
theorem higher_join_index (L p : ℕ) [Fact p.Prime] (hL : 0<L) (hpL : p∣L) :
    (gamma (p*(p*L))).relIndex
      (gamma (p*L)⊔degeneracyGroup (p*L) p (Fact.out : p.Prime).pos)=p^2 := by
  have hr : (gamma (p*L)).relIndex (gamma L)=p :=
    projective_index L p hL (Fact.out : p.Prime).pos hpL
  rw [repeated_join_index L p hL (by rw [hr]; exact Fact.out),hr,pow_two]

#print axioms double_degeneracy_index
#print axioms lower_degeneracy_index
#print axioms repeated_join_eq
#print axioms repeated_join_index
#print axioms square_two_join_index
#print axioms higher_join_index

end AsymptoticCongruenceStrip
