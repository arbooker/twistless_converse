module

public import AsymptoticRepeatedJoinIndexV1
public import AsymptoticPrimeNewCornerV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticRegularTrace
open AsymptoticRamifiedCosets
open scoped ENNReal

/-- Exact local new trace, with the generated-overgroup index proved
from the literal degeneracy groups rather than supplied as an input. -/
theorem repeated_new_trace (L p : ℕ) [Fact p.Prime] (hL : 0<L)
    (hr : ((gamma (p*L)).relIndex (gamma L)).Prime)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    letI : NeZero (p*(p*L)) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos
      (Nat.mul_pos (Fact.out : p.Prime).pos hL)).ne'⟩
    (trace volume (fun z => (newSpace (p*(p*L)) (gamma (p*L))
      (frickeOldGroup (p*(p*L)) (p*L) (Nat.mul_pos (Fact.out : p.Prime).pos
        (Nat.mul_pos (Fact.out : p.Prime).pos hL)))
      (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p))
      (gamma_le_frickeOldGroup (Nat.mul_pos (Fact.out : p.Prime).pos
        (Nat.mul_pos (Fact.out : p.Prime).pos hL)) (Nat.dvd_mul_left (p*L) p)) hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection (p*(p*L)) hε ht)).toReal*
        (1-(p:ℝ)⁻¹*2+((p*(gamma (p*L)).relIndex (gamma L):ℕ):ℝ)⁻¹) := by
  have hp := (Fact.out : p.Prime).pos
  have hM := Nat.mul_pos hp hL
  have hN := Nat.mul_pos hp hM
  let : NeZero (p*(p*L)) := ⟨hN.ne'⟩
  let J := gamma (p*L)
  let K := frickeOldGroup (p*(p*L)) (p*L) hN
  have hi : (gamma (p*(p*L))).relIndex J=p := projective_index (p*L) p hM hp (Nat.dvd_mul_right p L)
  have hk : (gamma (p*(p*L))).relIndex K=p := by
    dsimp only [K]
    rw [frickeOldGroup_index]
    exact hi
  have hj : (gamma (p*(p*L))).relIndex (J⊔K)=p*(gamma (p*L)).relIndex (gamma L) := by
    dsimp only [J,K]
    rw [frickeOldGroup_eq_degeneracy (p*L) p hM hp]
    exact repeated_join_index L p hL hr
  let : Finite (↥(J⊔K) ⧸ (gamma (p*(p*L))).subgroupOf (J⊔K)) := by
    apply Subgroup.index_ne_zero_iff_finite.mp
    change (gamma (p*(p*L))).relIndex (J⊔K)≠0
    rw [hj]
    exact (Nat.mul_pos hp hr.pos).ne'
  have he := new_trace_finite_join (p*(p*L)) J K
    (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p))
    (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left (p*L) p)) hε ht hN
  have hi' : ((gamma (p*(p*L))).subgroupOf J).index=p := hi
  have hk' : ((gamma (p*(p*L))).subgroupOf K).index=p := hk
  have hj' : ((gamma (p*(p*L))).subgroupOf (J⊔K)).index=p*(gamma (p*L)).relIndex (gamma L) := hj
  rw [hi',hk',hj'] at he
  convert he using 1
  ring

/-- At the exponent-two factor of 2 the local new trace is one sixth
of the actual congruence quotient trace. -/
theorem square_two_new_trace (L : ℕ) (hL : 0<L) (hodd : ¬2∣L)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    letI : NeZero (2*(2*L)) := ⟨(Nat.mul_pos (by norm_num) (Nat.mul_pos (by norm_num) hL)).ne'⟩
    (trace volume (fun z => (newSpace (2*(2*L)) (gamma (2*L))
      (frickeOldGroup (2*(2*L)) (2*L) (by omega))
      (gamma_le_of_dvd (Nat.dvd_mul_left (2*L) 2))
      (gamma_le_frickeOldGroup (by omega) (Nat.dvd_mul_left (2*L) 2)) hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection (2*(2*L)) hε ht)).toReal/6 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero (2*(2*L)) := ⟨by omega⟩
  have hr : (gamma (2*L)).relIndex (gamma L)=3 :=
    projective_index_coprime L 2 hL Nat.prime_two (Nat.prime_two.coprime_iff_not_dvd.mpr hodd)
  have he := repeated_new_trace L 2 hL (by rw [hr]; norm_num) hε ht
  rw [hr] at he
  norm_num at he
  convert he using 1
  ring

/-- At higher exponents of 2, including the admissible exponent three,
the local new trace is one quarter of the quotient trace. -/
theorem higher_two_new_trace (L : ℕ) (hL : 0<L) (heven : 2∣L)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    letI : NeZero (2*(2*L)) := ⟨(Nat.mul_pos (by norm_num) (Nat.mul_pos (by norm_num) hL)).ne'⟩
    (trace volume (fun z => (newSpace (2*(2*L)) (gamma (2*L))
      (frickeOldGroup (2*(2*L)) (2*L) (by omega))
      (gamma_le_of_dvd (Nat.dvd_mul_left (2*L) 2))
      (gamma_le_frickeOldGroup (by omega) (Nat.dvd_mul_left (2*L) 2)) hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection (2*(2*L)) hε ht)).toReal/4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero (2*(2*L)) := ⟨by omega⟩
  have hr : (gamma (2*L)).relIndex (gamma L)=2 := projective_index L 2 hL (by norm_num) heven
  have he := repeated_new_trace L 2 hL (by rw [hr]; exact Nat.prime_two) hε ht
  rw [hr] at he
  norm_num at he
  convert he using 1
  ring

#print axioms repeated_new_trace
#print axioms square_two_new_trace
#print axioms higher_two_new_trace

end AsymptoticCongruenceOldSpace
