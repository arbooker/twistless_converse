module

public import AsymptoticSimpleJoinPowersV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticSimpleJoin

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticIntegralSubgroup
open AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open scoped MatrixGroups

noncomputable def witness (M p : ℕ) : AsymptoticRationalGroup.Group :=
  translationLabel (1/(p:ℚ))*integralLabel (lowerSL M 1)

theorem witness_mem_join (M p : ℕ) (hp : 0<p) :
    witness M p∈gamma M⊔degeneracyGroup M p hp := by
  apply Subgroup.mul_mem
  · exact (show degeneracyGroup M p hp ≤ gamma M⊔degeneracyGroup M p hp from le_sup_right)
      (fractional_translation_mem_degeneracy M p hp)
  · apply (show gamma M ≤ gamma M⊔degeneracyGroup M p hp from le_sup_left)
    exact ⟨lowerSL M 1,lowerSL_mem M 1,rfl⟩

theorem witness_pow_not_mem (N M p n : ℕ) [Fact p.Prime]
    (hpM : ¬p∣M) (hn : 0<n) : witness M p^n∉gamma N := by
  intro h
  have hd : ((witnessGL M p)^n).val.det=1 := by
    change ((witnessGL M p).val^n).det=1
    rw [Matrix.det_pow,witness_det,one_pow]
  have hpos : 0<(realMatrix ((witnessGL M p)^n)).det.val := by
    change 0<(((witnessGL M p)^n).val.map (fun r : ℚ => (r:ℝ))).det
    rw [← Rat.cast_det,hd,Rat.cast_one]
    norm_num
  have he : witness M p^n=ofMatrix ((witnessGL M p)^n) hpos := by
    apply Subtype.ext
    apply Subtype.ext
    change (rationalMap (AsymptoticMobiusFold.translation (1/(p:ℚ)))*
      rationalMap (rationalGL (lowerSL M 1)))^n=rationalMap ((witnessGL M p)^n)
    rw [←map_mul,←map_pow]
    rfl
  rw [he] at h
  exact witness_pow_not_integral M p n hpM hn
    (ofMatrix_mem_gamma_integral N ((witnessGL M p)^n) hd hpos h 0 0)

/-- At a simply ramified prime, the actual generated old overgroup
has infinite relative index. Zero is Mathlib's index for an infinite quotient. -/
theorem simple_join_relIndex (N M p : ℕ) [Fact p.Prime] (hpM : ¬p∣M) :
    (gamma N).relIndex (gamma M⊔degeneracyGroup M p (Fact.out : p.Prime).pos)=0 := by
  by_contra h
  obtain ⟨n,hn,_,hm⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero h
    (witness_mem_join M p (Fact.out : p.Prime).pos)
  exact witness_pow_not_mem N M p n hpM hn hm.1

#print axioms witness_mem_join
#print axioms witness_pow_not_mem
#print axioms simple_join_relIndex

end AsymptoticSimpleJoin
