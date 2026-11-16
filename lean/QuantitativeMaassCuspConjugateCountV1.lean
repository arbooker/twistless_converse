module

public import QuantitativeMaassCuspBoxCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- Conjugation by an integral cusp chart embeds the actual congruence group
into the full projective modular group. -/
def cuspConjugateFull (N : ℕ) (A : SL(2,ℤ)) (g : gamma N) : gamma 1 :=
  ⟨(integralLabel A)⁻¹*g.val*integralLabel A,by
    apply Subgroup.mem_map.mpr
    refine ⟨A⁻¹*representative g*A,?_,?_⟩
    · rw [CongruenceSubgroup.Gamma0_mem]
      exact Subsingleton.elim _ _
    · simp only [map_mul,map_inv,representative_label]⟩

theorem cuspConjugateFull_injective (N : ℕ) (A : SL(2,ℤ)) :
    Function.Injective (cuspConjugateFull N A) := by
  intro g h he
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  change (integralLabel A)⁻¹*g.val*integralLabel A=(integralLabel A)⁻¹*h.val*integralLabel A at hh
  exact mul_left_cancel (mul_right_cancel hh)

theorem cuspConjugateFull_displacement (N : ℕ) (A : SL(2,ℤ)) (g : gamma N) (z : ℍ) :
    dist (cuspConjugateFull N A g•z) z=dist (g•(A•z)) (A•z) := by
  have he : cuspConjugateFull N A g•z=A⁻¹•(g•(A•z)) := by
    change ((integralLabel A)⁻¹*g.val*integralLabel A)•z=_
    rw [mul_smul,mul_smul,← map_inv,integralLabel_action,integralLabel_action]
    rfl
  rw [he]
  calc
    _ = dist (A⁻¹•(g•(A•z))) (A⁻¹•(A•z)) := by rw [inv_smul_smul]
    _ = _ := integral_action_dist A⁻¹ (g•(A•z)) (A•z)

/-- Return counts in every actual integral cusp chart are bounded by the
same full-level count in standard coordinates. -/
theorem diagonalOrbitSet_integral_chart_card (N : ℕ) (A : SL(2,ℤ)) (z : ℍ) (R : ℝ) :
    (diagonalOrbitSet N (A•z) R).card≤(diagonalOrbitSet 1 z R).card := by
  classical
  apply Finset.card_le_card_of_injOn (cuspConjugateFull N A)
  · intro g hg
    apply (mem_diagonalOrbitSet 1 z R _).mpr
    rw [cuspConjugateFull_displacement]
    exact (mem_diagonalOrbitSet N (A•z) R g).mp hg
  · exact (cuspConjugateFull_injective N A).injOn

/-- One linear-height bound applies in all integral cusp charts, uniformly
in the congruence level and truncation height. -/
theorem diagonalOrbitSet_all_cusp_charts_linear (R : ℝ) (hR : 0≤R) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) (A : SL(2,ℤ)) (H : ℝ) (z : ℍ),z∈wideBox H →
      ((diagonalOrbitSet N (A•z) R).card:ℝ)≤C*(1+z.im) := by
  obtain ⟨C,hC,hbound⟩ := diagonalOrbitSet_cusp_box_linear R hR
  refine ⟨C,hC,?_⟩
  intro N A H z hz
  have hh : ((diagonalOrbitSet N (A•z) R).card:ℝ)≤(diagonalOrbitSet 1 z R).card := by
    exact_mod_cast diagonalOrbitSet_integral_chart_card N A z R
  exact hh.trans (hbound 1 H z hz)

#print axioms cuspConjugateFull_injective
#print axioms cuspConjugateFull_displacement
#print axioms diagonalOrbitSet_integral_chart_card
#print axioms diagonalOrbitSet_all_cusp_charts_linear

end QuantitativeMaass
