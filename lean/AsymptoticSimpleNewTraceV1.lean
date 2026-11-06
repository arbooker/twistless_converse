module

public import AsymptoticSimpleJoinIndexV1
public import AsymptoticPrimeNewCornerV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticRegularTrace
open AsymptoticRamifiedCosets
open scoped ENNReal

/-- Exact simply ramified local new trace. The infinite index of the
actual generated old overgroup is proved, not supplied as a hypothesis. -/
theorem simple_new_trace (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos hM).ne'⟩
    (trace volume (fun z => (newSpace (p*M) (gamma M)
      (frickeOldGroup (p*M) M (Nat.mul_pos (Fact.out : p.Prime).pos hM))
      (gamma_le_of_dvd (Nat.dvd_mul_left M p))
      (gamma_le_frickeOldGroup (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (Nat.dvd_mul_left M p)) hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection (p*M) hε ht)).toReal*
        ((p:ℝ)-1)/((p:ℝ)+1) := by
  have hp := (Fact.out : p.Prime).pos
  have hN := Nat.mul_pos hp hM
  let : NeZero (p*M) := ⟨hN.ne'⟩
  let J := gamma M
  let K := frickeOldGroup (p*M) M hN
  have hi : (gamma (p*M)).relIndex J=p+1 :=
    projective_index_coprime M p hM Fact.out ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM)
  have hk : (gamma (p*M)).relIndex K=p+1 := by
    dsimp only [K]
    rw [frickeOldGroup_index]
    exact hi
  have hj : (gamma (p*M)).relIndex (J⊔K)=0 := by
    dsimp only [J,K]
    rw [frickeOldGroup_eq_degeneracy M p hM hp]
    exact AsymptoticSimpleJoin.simple_join_relIndex (p*M) M p hpM
  let : Infinite (↥(J⊔K) ⧸ (gamma (p*M)).subgroupOf (J⊔K)) :=
    Subgroup.index_eq_zero_iff_infinite.mp hj
  have he := new_trace_infinite_join (p*M) J K
    (gamma_le_of_dvd (Nat.dvd_mul_left M p))
    (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left M p)) hε ht hN
  have hi' : ((gamma (p*M)).subgroupOf J).index=p+1 := hi
  have hk' : ((gamma (p*M)).subgroupOf K).index=p+1 := hk
  rw [hi',hk',Nat.cast_add,Nat.cast_one] at he
  convert he using 1
  have hden : (p:ℝ)+1≠0 := by positivity
  field_simp
  ring

#print axioms simple_new_trace

end AsymptoticCongruenceOldSpace
