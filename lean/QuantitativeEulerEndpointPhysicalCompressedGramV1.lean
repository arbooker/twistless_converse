module

public import QuantitativeEulerEndpointActualPhysicalGramV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPhysicalNormalization
open AsymptoticFiniteBranch QuantitativeHolomorphic QuantitativeEulerEndpointPrepared ContinuousLinearMap
open scoped Classical

theorem gram_sum_compression {ι 𝔄 : Type*} [Fintype ι] [Ring 𝔄] [StarRing 𝔄] [Algebra ℂ 𝔄]
    (E : ι → 𝔄) (a : ℂ) (U : 𝔄) :
    (∑ i,star (a • (E i*U))*(a • (E i*U)))=
      star U*(∑ i,star (a • E i)*(a • E i))*U := by
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [←smul_mul_assoc,star_mul]
  simp only [mul_assoc]

theorem holomorphic_combined_compression {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Expression) (F : κ → Expression) (a : ℂ) (u : Expression) (m : ℕ) :
    holomorphicSum (combinedGramExpression E F a u) m=
      star (holomorphicSum u m)*holomorphicSum (combinedGramExpression E F a [identity]) m*holomorphicSum u m := by
  rw [holomorphic_combinedGramExpression,holomorphic_combinedGramExpression]
  have hi : holomorphicSum [identity] m=1 := by
    simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,holomorphic_identity,add_zero]
  simp only [hi,mul_one]
  rw [gram_sum_compression,gram_sum_compression,mul_add,add_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem compression_difference (T U V : H →L[ℂ] H) (hT : ‖T‖≤1) (hU : ‖U‖≤1) (hV : ‖V‖≤1) :
    ‖star U*T*U-star V*T*V‖≤2*‖U-V‖ := by
  have hs := AsymptoticObservation.sandwich_sub_norm_le U.adjoint V.adjoint T T hT hT
  simp only [adjoint_adjoint,sub_self,norm_zero,mul_zero,add_zero,←map_sub,adjoint.norm_map] at hs
  change ‖star U*(T*U)-star V*(T*V)‖≤(‖U‖+‖V‖)*‖U-V‖ at hs
  rw [←mul_assoc,←mul_assoc] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right (by linarith : ‖U‖+‖V‖≤2) (norm_nonneg _))

theorem compression_residual (T U V E : H →L[ℂ] H) (hT : ‖T‖≤1) (hU : ‖U‖≤1) (hV : ‖V‖≤1)
    (hzero : (star V*T*V)*E=0) :
    ‖(star U*T*U)*E‖≤2*‖U-V‖*‖E‖ := by
  have he : (star U*T*U)*E=((star U*T*U)-(star V*T*V))*E := by rw [sub_mul,hzero,sub_zero]
  rw [he]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (compression_difference T U V hT hU hV) (norm_nonneg E))

theorem gram_sum_kills {ι : Type*} [Fintype ι] (D : ι → H →L[ℂ] H) (a : ℂ) (V E : H →L[ℂ] H)
    (hD : ∀ i,D i*V*E=0) : (∑ i,star (a • D i)*(a • D i))*V*E=0 := by
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  calc
    _ = star (a • D i)*(a • (D i*V*E)) := by simp only [smul_mul_assoc,mul_assoc]
    _ = 0 := by rw [hD i,smul_zero,mul_zero]

theorem original_gram_kills {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → H →L[ℂ] H) (S : κ → H →L[ℂ] H) (a : ℂ) (V E : H →L[ℂ] H)
    (hR : ∀ i,R i*V*E=0) (hS : ∀ i,S i*V*E=0) :
    (star V*((∑ i,star (a • R i)*(a • R i))+(∑ i,star (a • S i)*(a • S i)))*V)*E=0 := by
  have hr := gram_sum_kills R a V E hR
  have hs := gram_sum_kills S a V E hS
  calc
    _ = star V*((∑ i,star (a • R i)*(a • R i))*V*E+
        (∑ i,star (a • S i)*(a • S i))*V*E) := by simp only [mul_add,add_mul,mul_assoc]
    _ = 0 := by rw [hr,hs,add_zero,mul_zero]

#print axioms holomorphic_combined_compression
#print axioms compression_residual
#print axioms original_gram_kills
end QuantitativeEulerEndpointPhysicalNormalization
