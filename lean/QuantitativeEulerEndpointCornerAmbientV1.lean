module

public import QuantitativeEulerEndpointTerminalNestedV1
public import QuantitativeEulerEndpointBoundedTerminalSoftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCornerAmbient
open Polynomial QuantitativeEulerEndpointCornerPolynomial
open QuantitativeEulerEndpointUpdateExpression QuantitativeEulerEndpointSoftUpdate

variable {𝔄 : Type*} [Ring 𝔄]

theorem restricted_power (P c : 𝔄) (hP : P*P=P) (hl : P*c=c) (hr : c*P=c) (n : ℕ) :
    (P-c)^n*P=(1-c)^n*P := by
  have hc : Commute P (1-c) := by
    show P*(1-c)=(1-c)*P
    rw [mul_sub,sub_mul,mul_one,one_mul,hl,hr]
  have hs (j : ℕ) : P*((1-c)^j*P)=(1-c)^j*P := by
    rw [←mul_assoc,(hc.pow_right j).eq,mul_assoc,hP]
  induction n with
  | zero => simp only [pow_zero]
  | succ n ih =>
    calc
      _ = (P-c)*((P-c)^n*P) := by rw [pow_succ',mul_assoc]
      _ = (P-c)*((1-c)^n*P) := by rw [ih]
      _ = (1-c)*((1-c)^n*P) := by rw [sub_mul,sub_mul,hs,one_mul]
      _ = _ := by rw [pow_succ',mul_assoc]

/-- On the supported source, the corner update is exactly the ambient
unital formula used by the operator-norm perturbation theorem. -/
theorem corner_update_eq (P a g : 𝔄) (hP : P*P=P) (hl : P*a=a) (hr : a*P=a) (n : ℕ) :
    cornerUpdate P a g n=a-a*(1-(1-a*g*a)^n)*a := by
  have hcl : P*(a*g*a)=a*g*a := by rw [←mul_assoc,←mul_assoc,hl]
  have hcr : (a*g*a)*P=a*g*a := by rw [mul_assoc,hr]
  have hp := restricted_power P (a*g*a) hP hcl hcr n
  unfold cornerUpdate
  rw [hp]
  have he : (P-(1-a*g*a)^n*P)*a=(1-(1-a*g*a)^n)*a := by
    rw [sub_mul,sub_mul,mul_assoc,hl,one_mul]
  rw [mul_assoc a,he,←mul_assoc]

variable [Algebra ℝ 𝔄]

theorem polynomial_right_support (P a : 𝔄) (hr : a*P=a) (q : ℝ[X]) (hq : q.eval 0=0) :
    aeval a q*P=aeval a q := by
  have hp (i : ℕ) (hi : i≠0) : a^i*P=a^i := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [pow_succ,mul_assoc,hr]
  rw [aeval_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=0
  · subst i
    have h0 : q.coeff 0=0 := by rw [coeff_zero_eq_eval_zero]; exact hq
    simp only [h0,zero_smul,zero_mul]
  · rw [smul_mul_assoc,hp i hi]

theorem corner_sharpened_eq (P a g : 𝔄) (hP : P*P=P) (hl : P*a=a) (hr : a*P=a)
    (n : ℕ) (q : ℝ[X]) (hq : q.eval 0=0) :
    aeval (cornerUpdate P a g n) q*P=aeval (a-a*(1-(1-a*g*a)^n)*a) q := by
  have hu : cornerUpdate P a g n*P=cornerUpdate P a g n := by
    simp only [cornerUpdate,sub_mul,mul_assoc,hr]
  rw [polynomial_right_support P _ hu q hq,corner_update_eq P a g hP hl hr n]

#print axioms restricted_power
#print axioms corner_update_eq
#print axioms polynomial_right_support
#print axioms corner_sharpened_eq
end QuantitativeEulerEndpointCornerAmbient
