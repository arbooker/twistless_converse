module

public import QuantitativeEulerEndpointBandExpressionV1
public import QuantitativeEulerEndpointSoftUpdateV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointUpdateExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointPolynomialExpression

def cornerPower (u e : Expression) (n : ℕ) : Expression := composeExpression (powerExpression e n) u

def updateExpression (u a g : Expression) (n : ℕ) : Expression :=
  let energy := composeExpression (composeExpression a g) a
  let step := u++scaleExpression (-1) energy
  let cut := u++scaleExpression (-1) (cornerPower u step n)
  a++scaleExpression (-1) (composeExpression (composeExpression a cut) a)

def sharpenedExpression (u a g : Expression) (n : ℕ) (q : ℝ[X]) : Expression :=
  cornerPolynomial u (updateExpression u a g n) q

def cornerUpdate {A : Type*} [Ring A] (P a g : A) (n : ℕ) : A :=
  a-a*(P-(P-a*g*a)^n*P)*a

theorem regular_update (u a g : Expression) (n : ℕ) (x : UpperHalfPlane) :
    regularSum (updateExpression u a g n) x=
      cornerUpdate (regularSum u x) (regularSum a x) (regularSum g x) n := by
  simp only [updateExpression,cornerPower,regularSum_append,regularSum_scale,
    regularSum_compose,regularSum_power]
  change regularSum a x + (-1:ℂ) • (regularSum a x *
    (regularSum u x + (-1:ℂ) • ((regularSum u x + (-1:ℂ) • (regularSum a x*regularSum g x*regularSum a x))^n*regularSum u x))*regularSum a x) = _
  have hn (T : AsymptoticFiniteBranch.RegularSpace →L[ℂ] AsymptoticFiniteBranch.RegularSpace) : (-1:ℂ) • T = -T := neg_one_smul ℂ T
  simp only [hn,cornerUpdate,sub_eq_add_neg]

theorem holomorphic_update (u a g : Expression) (n m : ℕ) :
    holomorphicSum (updateExpression u a g n) m=
      cornerUpdate (holomorphicSum u m) (holomorphicSum a m) (holomorphicSum g m) n := by
  simp only [updateExpression,cornerPower,holomorphicSum_append,holomorphicSum_scale,
    holomorphicSum_compose,holomorphicSum_power]
  change holomorphicSum a m + (-1:ℂ) • (holomorphicSum a m *
    (holomorphicSum u m + (-1:ℂ) • ((holomorphicSum u m + (-1:ℂ) • (holomorphicSum a m*holomorphicSum g m*holomorphicSum a m))^n*holomorphicSum u m))*holomorphicSum a m) = _
  have hn (T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) : (-1:ℂ) • T = -T := neg_one_smul ℂ T
  simp only [hn,cornerUpdate,sub_eq_add_neg]

theorem map_update {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]
    (ρ : A →ₗ[ℝ] B) (hmul : ∀ a b,ρ (a*b)=ρ a*ρ b) (a g : A) (n : ℕ) :
    ρ (a-a*(1-(1-a*g*a)^n)*a)=cornerUpdate (ρ 1) (ρ a) (ρ g) n := by
  simp only [map_sub,hmul,QuantitativeEulerEndpointCornerPolynomial.map_pow_corner ρ hmul,cornerUpdate]

variable (u a g : Expression)

theorem update_mass {A G : ℝ} (hA : 1≤A) (hG : 1≤G)
    (hu : expressionBound u≤1) (ha : expressionBound a≤A) (hg : expressionBound g≤G) (n : ℕ) :
    expressionBound (updateExpression u a g n)≤3*A^2*(2*A^2*G)^n := by
  have hA0 : 0≤A := by linarith
  have hG0 : 0≤G := by linarith
  let energy := composeExpression (composeExpression a g) a
  let step := u++scaleExpression (-1) energy
  let cut := u++scaleExpression (-1) (cornerPower u step n)
  have henergy : expressionBound energy≤A^2*G := by
    dsimp only [energy]
    rw [expressionBound_compose,expressionBound_compose]
    have h := mul_le_mul (mul_le_mul ha hg (expressionBound_nonneg _) hA0) ha
      (expressionBound_nonneg _) (by positivity : 0≤A*G)
    nlinarith only [h]
  have hbase : 1≤A^2*G := by
    have hAA : 1≤A^2 := one_le_pow₀ hA
    nlinarith [mul_le_mul hAA hG (by norm_num : (0:ℝ)≤1) (sq_nonneg A)]
  have hstep : expressionBound step≤2*A^2*G := by
    dsimp only [step]
    rw [expressionBound_append,expressionBound_scale]
    norm_num only [norm_neg,norm_one,one_mul]
    linarith
  have hpower : expressionBound (cornerPower u step n)≤(2*A^2*G)^n := by
    rw [cornerPower,expressionBound_compose,expressionBound_power]
    have h := mul_le_mul (pow_le_pow_left₀ (expressionBound_nonneg _) hstep n) hu
      (expressionBound_nonneg _) (by positivity : 0≤(2*A^2*G)^n)
    simpa only [mul_one] using h
  have hcut : expressionBound cut≤1+(2*A^2*G)^n := by
    dsimp only [cut]
    rw [expressionBound_append,expressionBound_scale]
    norm_num only [norm_neg,norm_one,one_mul]
    linarith
  have hsandwich : expressionBound (composeExpression (composeExpression a cut) a)≤
      A^2*(1+(2*A^2*G)^n) := by
    rw [expressionBound_compose,expressionBound_compose]
    have h := mul_le_mul (mul_le_mul ha hcut (expressionBound_nonneg _) hA0) ha
      (expressionBound_nonneg _) (by positivity : 0≤A*(1+(2*A^2*G)^n))
    nlinarith only [h]
  change expressionBound (a++scaleExpression (-1) (composeExpression (composeExpression a cut) a))≤_
  rw [expressionBound_append,expressionBound_scale]
  norm_num only [norm_neg,norm_one,one_mul]
  have hp : 1≤(2*A^2*G)^n := one_le_pow₀ (by linarith)
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg A)
  have hAA : A≤A^2 := by nlinarith
  nlinarith only [ha,hsandwich,hm,hAA]

theorem sharpened_mass {A G : ℝ} (hA : 1≤A) (hG : 1≤G)
    (hu : expressionBound u≤1) (ha : expressionBound a≤A) (hg : expressionBound g≤G)
    (n : ℕ) (q : ℝ[X]) :
    expressionBound (sharpenedExpression u a g n q)≤
      (∑ i∈q.support, |q.coeff i|)*(3*A^2*(2*A^2*G)^n)^q.natDegree := by
  have hb := update_mass u a g hA hG hu ha hg n
  have hA0 : 0≤A := by linarith
  have hG0 : 0≤G := by linarith
  have hbase : 1≤3*A^2*(2*A^2*G)^n := by
    have hAA : 1≤A^2 := one_le_pow₀ hA
    have hprod : 1≤A^2*G := by nlinarith [mul_le_mul hAA hG (by norm_num : (0:ℝ)≤1) (sq_nonneg A)]
    have hp : 1≤(2*A^2*G)^n := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul hAA hp (by norm_num : (0:ℝ)≤1) (sq_nonneg A)]
  have hm := corner_mass_le u (updateExpression u a g n) q
  have hmax : max 1 (expressionBound (updateExpression u a g n))≤3*A^2*(2*A^2*G)^n := max_le hbase hb
  have hcoeff : 0≤∑ i∈q.support, |q.coeff i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax q.natDegree) hcoeff
  exact hm.trans ((mul_le_mul hp hu (expressionBound_nonneg u) (by positivity)).trans_eq (mul_one _))

#print axioms regular_update
#print axioms holomorphic_update
#print axioms map_update
#print axioms sharpened_mass
end QuantitativeEulerEndpointUpdateExpression
