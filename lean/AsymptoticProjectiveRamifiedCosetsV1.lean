module

public import AsymptoticFrickeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRamifiedCosets

open AsymptoticCongruenceLabels AsymptoticCongruenceStrip

noncomputable def projectiveRepresentative (M q : ℕ) (j : Fin q) : gamma M :=
  ⟨integralLabel (lowerSL M (j.val:ℤ)),⟨lowerSL M (j.val:ℤ),lowerSL_mem M (j.val:ℤ),rfl⟩⟩

noncomputable def projectiveCoset (M q : ℕ) (j : Fin q) :
    gamma M ⧸ (gamma (q*M)).subgroupOf (gamma M) :=
  QuotientGroup.mk (projectiveRepresentative M q j)

theorem projectiveCoset_injective (M q : ℕ) (hM : 0<M) (hq : 0<q) :
    Function.Injective (projectiveCoset M q) := by
  intro i j hij
  have hh := QuotientGroup.eq.mp hij
  change (integralLabel (lowerSL M (i.val:ℤ)))⁻¹*integralLabel (lowerSL M (j.val:ℤ))∈gamma (q*M) at hh
  rw [← map_inv,← map_mul,integralLabel_mem_gamma_iff] at hh
  exact representatives_distinct M q hM hq i j hh

theorem projectiveCoset_surjective (M q : ℕ) (hq : 0<q) (hqM : q∣M) :
    Function.Surjective (projectiveCoset M q) := by
  intro y
  induction y using Quotient.inductionOn with
  | h a =>
    obtain ⟨A,hA,hAa⟩ := a.property
    obtain ⟨j,hj⟩ := reduce_to_finer M q hq hqM A hA
    refine ⟨j,QuotientGroup.eq.mpr ?_⟩
    change (integralLabel (lowerSL M (j.val:ℤ)))⁻¹*a.val∈gamma (q*M)
    rw [← hAa,← map_inv,← map_mul,integralLabel_mem_gamma_iff]
    exact hj

noncomputable def projectiveCosetEquiv (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M) :
    Fin q ≃ (gamma M ⧸ (gamma (q*M)).subgroupOf (gamma M)) :=
  Equiv.ofBijective (projectiveCoset M q)
    ⟨projectiveCoset_injective M q hM hq,projectiveCoset_surjective M q hq hqM⟩

#print axioms projectiveCoset_injective
#print axioms projectiveCoset_surjective

end AsymptoticRamifiedCosets
