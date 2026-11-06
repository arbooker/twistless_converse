module

public import QuantitativeEulerEndpointNestedPerturbationV1
public import QuantitativeEulerEndpointReconstructionAccuracyV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedPerturbation
open Polynomial QuantitativeEulerEndpointResidual

/-- Accumulated operator-norm perturbation, as opposed to fixed-vector
residual. It pays changes in both compressed factors at every step. -/
def comparisonBudget (L : ℕ → ℕ) (q : ℕ → ℝ[X]) : ℕ → ℝ
  | 0 => 1
  | n+1 => (1+slopeMass (q n))*(4+3*(L n:ℝ))*comparisonBudget L q n

theorem comparisonBudget_ge_one (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) :
    1≤comparisonBudget L q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := slopeMass_nonneg (q n)
    have hL : (0:ℝ)≤L n := Nat.cast_nonneg _
    have hf : 1≤(1+slopeMass (q n))*(4+3*(L n:ℝ)) := by nlinarith
    dsimp only [comparisonBudget]
    nlinarith

theorem comparisonBudget_le_square (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) :
    comparisonBudget L q n≤(errorBudget L q n)^2 := by
  induction n with
  | zero => norm_num [comparisonBudget,errorBudget]
  | succ n ih =>
    have hs := slopeMass_nonneg (q n)
    have hL : (0:ℝ)≤L n := Nat.cast_nonneg _
    have hq : 1+slopeMass (q n)≤(1+slopeMass (q n))^2 := by nlinarith
    have hd : 4+3*(L n:ℝ)≤(4+2*(L n:ℝ))^2 := by nlinarith
    have hf := mul_le_mul hq hd (by positivity : 0≤4+3*(L n:ℝ)) (by positivity : 0≤(1+slopeMass (q n))^2)
    rw [←mul_pow] at hf
    have hb : 0≤comparisonBudget L q n := by linarith [comparisonBudget_ge_one L q n]
    have hh := mul_le_mul hf ih hb (sq_nonneg _)
    simpa only [comparisonBudget,errorBudget,mul_pow] using hh

theorem comparisonBudget_step (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) {δ r s : ℝ}
    (hδ : 0≤δ) (hr : r≤comparisonBudget L q n*δ) (hs : s≤δ) :
    slopeMass (q n)*((3+2*(L n:ℝ))*r+(L n:ℝ)*s)≤comparisonBudget L q (n+1)*δ := by
  have hb := comparisonBudget_ge_one L q n
  have hq := slopeMass_nonneg (q n)
  have hL : (0:ℝ)≤L n := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hr (by positivity : 0≤3+2*(L n:ℝ)))
    (mul_le_mul_of_nonneg_left hs hL)) hq
  have hbig : slopeMass (q n)*((3+2*(L n:ℝ))*comparisonBudget L q n+(L n:ℝ))≤
      (1+slopeMass (q n))*(4+3*(L n:ℝ))*comparisonBudget L q n := by
    have hb0 : 0≤comparisonBudget L q n := by linarith
    nlinarith [mul_nonneg hq (mul_nonneg hL (sub_nonneg.mpr hb)),
      mul_nonneg hq hb0,mul_nonneg hL hb0]
  have hfinal := mul_le_mul_of_nonneg_right hbig hδ
  dsimp only [comparisonBudget]
  nlinarith

theorem squared_double_exp {K R D : ℝ} (hR : 1≤R) (hD0 : 0≤D)
    (hD : D≤Real.exp (Real.exp (K*R))) :
    D^2≤Real.exp (Real.exp ((K+2)*R)) := by
  have hp := pow_le_pow_left₀ hD0 hD 2
  have he : (Real.exp (Real.exp (K*R)))^2=Real.exp (2*Real.exp (K*R)) := by
    simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (Real.exp (K*R)) 2).symm
  rw [he] at hp
  have hs := QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le (a:=K) (by norm_num : (0:ℝ)≤2) hR
  rw [add_comm 2 K] at hs
  exact hp.trans (Real.exp_le_exp.mpr hs)

#print axioms comparisonBudget_le_square
#print axioms comparisonBudget_step
#print axioms squared_double_exp
end QuantitativeEulerEndpointNestedPerturbation
