module

public import AsymptoticNewSpaceRootTraceV1
public import AsymptoticSimpleNewTraceV1
public import AsymptoticRepeatedNewTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticQuotientOperators

open AsymptoticCongruenceStrip AsymptoticCongruenceQuotient AsymptoticCongruenceOldSpace
open AsymptoticRegularTrace

/-- Exact fixed coset coefficient at a simply ramified prime. -/
theorem simple_new_root (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos hM).ne'⟩
    (matrix (AsymptoticQuotientOperators.newSpace
      (gamma_le_of_dvd (Nat.dvd_mul_left M p))
      (gamma_le_frickeOldGroup (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (Nat.dvd_mul_left M p))).starProjection
        (classOf (p*M) 1) (classOf (p*M) 1)).re=((p:ℝ)-1)/((p:ℝ)+1) := by
  have hN := Nat.mul_pos (Fact.out : p.Prime).pos hM
  let : NeZero (p*M) := ⟨hN.ne'⟩
  apply newSpace_root_of_trace (p*M) _ _ _ _ (ε:=1) (by norm_num) (t:=1) (by omega) hN
  have hh := simple_new_trace M p hM hpM (ε:=1) (by norm_num) (t:=1) (by omega)
  simpa only [div_eq_mul_inv,mul_assoc] using hh

/-- Exact fixed coset coefficient at conductor exponent two of 2. -/
theorem square_two_new_root (L : ℕ) (hL : 0<L) (hodd : ¬2∣L) :
    letI : NeZero (2*(2*L)) := ⟨by omega⟩
    (matrix (AsymptoticQuotientOperators.newSpace
      (gamma_le_of_dvd (Nat.dvd_mul_left (2*L) 2))
      (gamma_le_frickeOldGroup (by omega : 0<2*(2*L))
        (Nat.dvd_mul_left (2*L) 2))).starProjection
        (classOf (2*(2*L)) 1) (classOf (2*(2*L)) 1)).re=1/6 := by
  let : NeZero (2*(2*L)) := ⟨by omega⟩
  apply newSpace_root_of_trace (2*(2*L)) _ _ _ _ (ε:=1) (by norm_num) (t:=1) (by omega) (by omega)
  have hh := square_two_new_trace L hL hodd (ε:=1) (by norm_num) (t:=1) (by omega)
  simpa only [div_eq_mul_inv,one_mul] using hh

/-- Exact fixed coset coefficient at higher conductor exponents of 2. -/
theorem higher_two_new_root (L : ℕ) (hL : 0<L) (heven : 2∣L) :
    letI : NeZero (2*(2*L)) := ⟨by omega⟩
    (matrix (AsymptoticQuotientOperators.newSpace
      (gamma_le_of_dvd (Nat.dvd_mul_left (2*L) 2))
      (gamma_le_frickeOldGroup (by omega : 0<2*(2*L))
        (Nat.dvd_mul_left (2*L) 2))).starProjection
        (classOf (2*(2*L)) 1) (classOf (2*(2*L)) 1)).re=1/4 := by
  let : NeZero (2*(2*L)) := ⟨by omega⟩
  apply newSpace_root_of_trace (2*(2*L)) _ _ _ _ (ε:=1) (by norm_num) (t:=1) (by omega) (by omega)
  have hh := higher_two_new_trace L hL heven (ε:=1) (by norm_num) (t:=1) (by omega)
  simpa only [div_eq_mul_inv,one_mul] using hh

#print axioms simple_new_root
#print axioms square_two_new_root
#print axioms higher_two_new_root

end AsymptoticQuotientOperators
