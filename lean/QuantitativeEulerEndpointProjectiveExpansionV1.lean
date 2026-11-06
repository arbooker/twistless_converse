module

public import QuantitativeEulerEndpointProjectiveGeneratorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode AsymptoticCongruenceLabels
open AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

theorem projective_inverse_letter_identity (γ : SL(2,ℤ)) (g : G) :
    (symbol (integralLabel γ)-1)*symbol g=
      -((symbol (integralLabel γ⁻¹)-1)*symbol (integralLabel γ*g)) := by
  have hi : symbol (integralLabel γ⁻¹)*symbol (integralLabel γ)=1 := by
    rw [←symbol.map_mul,←integralLabel.map_mul,inv_mul_cancel,map_one,map_one]
  rw [symbol.map_mul,sub_mul,sub_mul,one_mul,one_mul,←mul_assoc,hi,one_mul]
  abel

theorem projective_inverse_letter_norm (γ : SL(2,ℤ)) (g : G) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x ((symbol (integralLabel γ)-1)*symbol g) v‖=
    ‖compactAction hs hε t x ((symbol (integralLabel γ⁻¹)-1)*symbol (integralLabel γ*g)) v‖ := by
  rw [projective_inverse_letter_identity,map_neg,_root_.neg_apply,norm_neg]

theorem compact_expression_right_expand (A E : Ring) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (A*E)=
      ∑ g : ↥E.coeff.support, E.coeff g • compactAction hs hε t x (A*symbol g) := by
  rw [Finset.sum_coe_sort E.coeff.support
    (fun g => E.coeff g • compactAction hs hε t x (A*symbol g))]
  conv_lhs => rw [expression_eq_sum E]
  simp only [Finset.mul_sum,mul_smul_comm,map_sum,map_smul]

theorem compact_word_multiplier_expand (γ β : SL(2,ℤ)) (E : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x ((symbol (integralLabel γ)-1)*(symbol (integralLabel β)*E))=
      ∑ g : ↥E.coeff.support, E.coeff g • compactAction hs hε t x
        ((symbol (integralLabel γ)-1)*symbol (integralLabel β*g)) := by
  rw [←mul_assoc,compact_expression_right_expand]
  apply Finset.sum_congr rfl
  intro g _
  have he : ((symbol (integralLabel γ)-1)*symbol (integralLabel β))*symbol g=
      (symbol (integralLabel γ)-1)*symbol (integralLabel β*g) := by
    rw [symbol.map_mul,mul_assoc]
  exact congrArg (fun T : Space →L[ℂ] Space => E.coeff g • T)
    (congrArg (compactAction hs hε t x) he)

def coefficientSquareBound (E : Ring) : ℝ := 1+∑ g : ↥E.coeff.support, ‖E.coeff g‖^2

theorem coefficientSquareBound_pos (E : Ring) : 0<coefficientSquareBound E := by
  have h := Finset.sum_nonneg (fun g (_ : g∈(Finset.univ : Finset ↥E.coeff.support)) => sq_nonneg ‖E.coeff g‖)
  unfold coefficientSquareBound
  linarith

theorem coefficientSquareBound_le (E : Ring) (g : ↥E.coeff.support) :
    ‖E.coeff g‖^2≤coefficientSquareBound E := by
  have h := Finset.single_le_sum (fun a _ => sq_nonneg ‖E.coeff (a : ↥E.coeff.support)‖) (Finset.mem_univ g)
  unfold coefficientSquareBound
  linarith

#print axioms projective_inverse_letter_norm
#print axioms compact_word_multiplier_expand
end QuantitativeEulerEndpointPrepared
