module

public import QuantitativeEulerEndpointPhysicalGramV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPhysicalGram
open AsymptoticFiniteBranch QuantitativeHolomorphic QuantitativeEulerEndpointBandExpression

variable (ε H : ℝ) (m : ℕ)
  (T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
local notation "P" => holomorphicSum (unitExpression ε H) m

theorem normalized_gram_kills (E : ℕ → Expression) (C : ℕ → ℝ) (n : ℕ)
    (hPT : P*T=T) (hET : ∀ i : Fin n,holomorphicSum (E i) m*T=0) :
    holomorphicSum (QuantitativeEulerEndpointNormalizedExpression.gram (unitExpression ε H) E C n) m*T=0 := by
  have hz (r : ℂ) : r • (0 : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)=0 := by
    apply ContinuousLinearMap.ext
    intro f
    change r • (0 : AsymptoticHyperbolicSlash.Space)=0
    exact smul_zero r
  rw [QuantitativeEulerEndpointNormalizedExpression.holomorphic_gram,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_assoc,smul_mul_assoc,mul_assoc,hPT,hET i]
  rw [hz,mul_zero]

theorem weighted_gram_kills {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → κ → Expression) (w : ι → ℝ) (c : ℝ)
    (hPT : P*T=T) (hET : ∀ i j,holomorphicSum (E i j) m*T=0) :
    holomorphicSum (QuantitativeEulerEndpointWeightedExpression.weightedGram (unitExpression ε H) E w c) m*T=0 := by
  rw [QuantitativeEulerEndpointWeightedExpression.holomorphic_weightedGram]
  have hr (r : ℝ) (U : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) :
      r • U=(r:ℂ) • U := RCLike.real_smul_eq_coe_smul (K:=ℂ) r U
  simp only [hr,smul_mul_assoc,Finset.sum_mul]
  have hi (i : ι) : (∑ j : κ, (star (holomorphicSum (E i j) m*P)*(holomorphicSum (E i j) m*P))*T)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [mul_assoc,mul_assoc,hPT,hET i j,mul_zero]
  have hz (r : ℂ) : r • (0 : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)=0 := by
    apply ContinuousLinearMap.ext
    intro f
    change r • (0 : AsymptoticHyperbolicSlash.Space)=0
    exact smul_zero r
  simp only [hi,hz,Finset.sum_const_zero]

#print axioms normalized_gram_kills
#print axioms weighted_gram_kills
end QuantitativeEulerEndpointPhysicalGram
