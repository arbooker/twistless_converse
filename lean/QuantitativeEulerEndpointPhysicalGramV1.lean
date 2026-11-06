module

public import QuantitativeEulerEndpointWeightedExpressionV1
public import QuantitativeEulerEndpointBandExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPhysicalGram
open AsymptoticFiniteBranch QuantitativeHolomorphic QuantitativeEulerEndpointBandExpression

section Algebra
variable {A : Type*} [Ring A] [StarRing A] (P : A) (hP : IsStarProjection P)

include hP in
theorem gram_supported (T : A) (hT : T*P=T) :
    P*(star T*T)=star T*T ∧ (star T*T)*P=star T*T := by
  have hl : P*star T=star T := by
    have h := congrArg star hT
    simpa only [star_mul,hP.isSelfAdjoint.star_eq] using h
  exact ⟨by rw [←mul_assoc,hl],by rw [mul_assoc,hT]⟩

omit [StarRing A] in
theorem sum_supported {ι : Type*} [Fintype ι] (T : ι → A)
    (hT : ∀ i,P*T i=T i ∧ T i*P=T i) :
    P*(∑ i,T i)=∑ i,T i ∧ (∑ i,T i)*P=∑ i,T i := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (hT i).1)
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => (hT i).2)

end Algebra

variable (ε H : ℝ) (m : ℕ)
local notation "P" => holomorphicSum (unitExpression ε H) m

theorem unit_isStarProjection : IsStarProjection P := by
  constructor
  · change P*P=P
    rw [unit_holomorphic]
    apply ContinuousLinearMap.ext
    exact AsymptoticRegionL2.projection_idempotent _ _ _
  · change star P=P
    rw [unit_holomorphic]
    exact AsymptoticRegionL2.projection_adjoint _ _ _

theorem unit_order : 0≤P ∧ P≤1 := by
  have hp := unit_isStarProjection ε H m
  have h0 : 0≤P := by
    have hh := star_mul_self_nonneg P
    rwa [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at hh
  exact ⟨h0,(CStarAlgebra.norm_le_one_iff_of_nonneg P h0).mp
    ((holomorphicSum_norm_le _ _).trans (le_of_eq (unit_mass ε H)))⟩

theorem normalized_gram_supported (E : ℕ → Expression) (C : ℕ → ℝ) (n : ℕ) :
    P*holomorphicSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) m=
      holomorphicSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) m ∧
    holomorphicSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) m*P=
      holomorphicSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) m := by
  rw [QuantitativeEulerEndpointNormalizedExpression.holomorphic_gram]
  apply sum_supported
  intro i
  apply gram_supported P (unit_isStarProjection ε H m)
  rw [smul_mul_assoc,mul_assoc,(unit_isStarProjection ε H m).isIdempotentElem.eq]

theorem normalized_gram_order (E : ℕ → Expression) (C : ℕ → ℝ) (n : ℕ)
    (hE : ∀ i : Fin n,expressionBound (E i)≤C i) :
    0≤holomorphicSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) m ∧
    holomorphicSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) m≤1 := by
  have h0 : 0≤holomorphicSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) m := by
    rw [QuantitativeEulerEndpointNormalizedExpression.holomorphic_gram]
    exact Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
  have hm := QuantitativeEulerEndpointNormalizedExpression.gram_mass (le_of_eq (unit_mass ε H)) n hE
  exact ⟨h0,(CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mp ((holomorphicSum_norm_le _ _).trans hm)⟩

theorem weighted_gram_supported {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → κ → Expression) (w : ι → ℝ) (c : ℝ) :
    P*holomorphicSum (QuantitativeEulerEndpointWeightedExpression.weightedGram (unitExpression ε H) E w c) m=
      holomorphicSum (QuantitativeEulerEndpointWeightedExpression.weightedGram (unitExpression ε H) E w c) m ∧
    holomorphicSum (QuantitativeEulerEndpointWeightedExpression.weightedGram (unitExpression ε H) E w c) m*P=
      holomorphicSum (QuantitativeEulerEndpointWeightedExpression.weightedGram (unitExpression ε H) E w c) m := by
  rw [QuantitativeEulerEndpointWeightedExpression.holomorphic_weightedGram]
  have hr (r : ℝ) (T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) :
      r • T=(r:ℂ) • T := RCLike.real_smul_eq_coe_smul (K:=ℂ) r T
  simp only [hr]
  have hs (i : ι) := sum_supported P
    (fun j : κ => star (holomorphicSum (E i j) m*P)*(holomorphicSum (E i j) m*P))
    (fun j => gram_supported P (unit_isStarProjection ε H m) _
      (by rw [mul_assoc,(unit_isStarProjection ε H m).isIdempotentElem.eq]))
  have ht := sum_supported P
    (fun i : ι => (w i:ℂ) • (∑ j : κ,star (holomorphicSum (E i j) m*P)*(holomorphicSum (E i j) m*P)))
    (fun i => ⟨by rw [mul_smul_comm,(hs i).1],by rw [smul_mul_assoc,(hs i).2]⟩)
  exact ⟨by rw [mul_smul_comm,ht.1],by rw [smul_mul_assoc,ht.2]⟩

#print axioms unit_isStarProjection
#print axioms normalized_gram_order
#print axioms normalized_gram_supported
#print axioms weighted_gram_supported
end QuantitativeEulerEndpointPhysicalGram
