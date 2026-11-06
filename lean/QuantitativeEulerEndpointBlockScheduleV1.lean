module

public import QuantitativeEulerEndpointBlockIterationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlocks
open Finset

/-- Logarithmic approximation effort for block j of a packet ending at J.
The block's geometric size is 4^j; effort is their geometric mean 2^(J+j). -/
def blockEffort (J j : ℕ) : ℝ := (2:ℝ)^(J+j)
def blockRelativeLoss (J j : ℕ) : ℝ := (2:ℝ)^j/(2:ℝ)^J
def blockAdditiveLoss (J j : ℕ) : ℝ := 1/blockEffort J j

theorem blockEffort_pos (J j : ℕ) : 0<blockEffort J j := by unfold blockEffort; positivity
theorem blockRelativeLoss_nonneg (J j : ℕ) : 0≤blockRelativeLoss J j := by
  unfold blockRelativeLoss; positivity
theorem blockAdditiveLoss_nonneg (J j : ℕ) : 0≤blockAdditiveLoss J j := by
  unfold blockAdditiveLoss; exact div_nonneg (by norm_num) (blockEffort_pos J j).le

theorem sum_two_powers (J : ℕ) : (∑ j ∈ range J, (2:ℝ)^j)=(2:ℝ)^J-1 := by
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ,ih,pow_succ]; ring

theorem blockRelativeLoss_sum_le (J : ℕ) : (∑ j ∈ range J, blockRelativeLoss J j)≤1 := by
  simp only [blockRelativeLoss,←sum_div,sum_two_powers]
  apply (div_le_one (by positivity : 0<(2:ℝ)^J)).mpr
  linarith

theorem blockEffort_total_le (J : ℕ) : (∑ j ∈ range J, blockEffort J j)≤(4:ℝ)^J := by
  simp only [blockEffort,pow_add,←mul_sum,sum_two_powers]
  have hpow : (4:ℝ)^J=(2:ℝ)^J*(2:ℝ)^J := by rw [←mul_pow]; norm_num
  rw [hpow]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) J]

theorem blockEffort_ratio (J j : ℕ) : (4:ℝ)^j/blockEffort J j=blockRelativeLoss J j := by
  have hpow : (4:ℝ)^j=(2:ℝ)^j*(2:ℝ)^j := by rw [←mul_pow]; norm_num
  simp only [blockEffort,blockRelativeLoss,pow_add,hpow]
  field_simp

theorem weighted_blockAdditiveLoss (J j : ℕ) :
    (4:ℝ)^(j+1)*blockAdditiveLoss J j=4*blockRelativeLoss J j := by
  rw [pow_succ]
  dsimp only [blockAdditiveLoss]
  have h := blockEffort_ratio J j
  calc
    _ = 4*((4:ℝ)^j/blockEffort J j) := by ring
    _ = _ := by rw [h]

theorem weighted_blockAdditiveLoss_sum_le (J : ℕ) :
    (∑ j ∈ range J, (4:ℝ)^(j+1)*blockAdditiveLoss J j)≤4 := by
  simp_rw [weighted_blockAdditiveLoss]
  rw [←mul_sum]
  nlinarith [blockRelativeLoss_sum_le J]

/-- A finite-horizon block schedule can pay both relative determinant loss
and additive regularization error at the exact endpoint, using only O(4^J)
total logarithmic effort. This is a scalar scheduling theorem: the displayed
recurrence must still be proved for the actual block filters. -/
theorem finite_horizon_block_endpoint (J : ℕ) (e bad : ℕ → ℝ)
    {A B C : ℝ} (hA : 0≤A) (hB : 0≤B)
    (he : ∀ j, 0≤e j) (hbad : ∀ j, 0≤bad j)
    (hbudget : (∑ j ∈ range J, bad j)≤C)
    (hstep : ∀ j, e (j+1)≤
      (Real.exp (bad j)/4+A*blockRelativeLoss J j)*e j+B*blockAdditiveLoss J j) :
    e J≤Real.exp (C+4*A)*(e 0+4*B)/(4:ℝ)^J := by
  let loss := fun j => bad j+4*A*blockRelativeLoss J j
  let err := fun j => B*blockAdditiveLoss J j
  have hloss (j : ℕ) : 0≤loss j := by
    exact add_nonneg (hbad j) (mul_nonneg (mul_nonneg (by norm_num) hA) (blockRelativeLoss_nonneg J j))
  have herr (j : ℕ) : 0≤err j := mul_nonneg hB (blockAdditiveLoss_nonneg J j)
  have hcoef (j : ℕ) :
      Real.exp (bad j)/4+A*blockRelativeLoss J j≤Real.exp (loss j)/4 := by
    have hexp : 1≤Real.exp (bad j) := Real.one_le_exp_iff.mpr (hbad j)
    have hn : 0≤A*blockRelativeLoss J j := mul_nonneg hA (blockRelativeLoss_nonneg J j)
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (4*A*blockRelativeLoss J j))
      (show 0≤Real.exp (bad j)/4 by positivity)
    calc
      _ ≤ Real.exp (bad j)/4*(4*A*blockRelativeLoss J j+1) := by nlinarith
      _ ≤ Real.exp (bad j)/4*Real.exp (4*A*blockRelativeLoss J j) := hh
      _ = _ := by dsimp only [loss]; rw [Real.exp_add]; ring
  have hstep' (j : ℕ) : e (j+1)≤Real.exp (loss j)/4*e j+err j :=
    (hstep j).trans (add_le_add (mul_le_mul_of_nonneg_right (hcoef j) (he j)) le_rfl)
  have hnorm := normalized_block_iteration e loss err (by norm_num : (0:ℝ)<4)
    (he 0) hloss herr hstep' J
  have hl : (∑ j ∈ range J, loss j)≤C+4*A := by
    simp only [loss,sum_add_distrib,←mul_sum]
    have h := mul_le_mul_of_nonneg_left (blockRelativeLoss_sum_le J)
      (show 0≤4*A by positivity)
    nlinarith
  have herrsum : (∑ j ∈ range J, (4:ℝ)^(j+1)*err j)≤4*B := by
    have hid : (∑ j ∈ range J, (4:ℝ)^(j+1)*err j)=
        B*∑ j ∈ range J, (4:ℝ)^(j+1)*blockAdditiveLoss J j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      dsimp only [err]
      ring
    rw [hid]
    nlinarith [mul_le_mul_of_nonneg_left (weighted_blockAdditiveLoss_sum_le J) hB]
  have hnonneg : 0≤e 0+∑ j ∈ range J, (4:ℝ)^(j+1)*err j :=
    add_nonneg (he 0) (sum_nonneg (fun j _ => mul_nonneg (by positivity) (herr j)))
  have hm := mul_le_mul (Real.exp_le_exp.mpr hl) (add_le_add le_rfl herrsum)
    hnonneg (Real.exp_pos _).le
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(4:ℝ)^J)).mpr
  simpa only [mul_comm] using hnorm.trans hm

#print axioms blockEffort_total_le
#print axioms blockEffort_ratio
#print axioms weighted_blockAdditiveLoss_sum_le
#print axioms finite_horizon_block_endpoint
end QuantitativeEulerEndpointBlocks
