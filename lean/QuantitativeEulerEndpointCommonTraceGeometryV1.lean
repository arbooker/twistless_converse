module

public import QuantitativeEulerEndpointSandwichCostV1
public import QuantitativeHolomorphicGrowingScaledTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticFiniteBranch
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The SAME common lower and upper cutoffs, the matrix separation cost,
and the mass bound all have one horizon envelope. -/
theorem exists_horizon_trace_geometry {K a : ℝ} (hK : 0≤K) (ha : 0≤a) :
    ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      let H := Real.exp (16*s)
      let Y := lowerHeight A P s
      let M := Real.exp (Real.exp (a*(4:ℝ)^n))
      let L := Real.exp (Real.exp (C*(4:ℝ)^n))
      M*(H+2)≤L ∧ H≤L ∧ Y⁻¹≤L ∧ M≤L := by
  let d := abs (lowerInverseGrowthConstant A P 0)
  let b := d+4*(K+1)+(K+17)
  have hd : 0≤d := abs_nonneg _
  have hb : 0≤b := by dsimp only [b]; positivity
  refine ⟨a+b+7,by positivity,?_⟩
  intro n s H Y M L
  let R : ℝ := (4:ℝ)^n
  let V := Real.exp (Real.exp (b*R))
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hR0 : 0≤R := by linarith
  have hs : 1≤s := Real.one_le_exp (by positivity)
  have hV : 1≤V := Real.one_le_exp (Real.exp_pos _).le
  have hH : H≤V := by
    apply Real.exp_le_exp.mpr
    have hh := QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le
      (a:=K+1) (by norm_num : (0:ℝ)≤16) hR
    apply hh.trans
    apply Real.exp_le_exp.mpr
    dsimp only [b]
    nlinarith
  have hY : Y⁻¹≤V := by
    have hh := growing_lower_inverse A P (by norm_num : (0:ℝ)≤0) hs 0 (by norm_num)
    norm_num only [Nat.cast_zero,mul_zero,zero_add] at hh
    apply hh.trans
    apply Real.exp_le_exp.mpr
    have he : s^4=Real.exp ((4*(K+1))*R) := by
      dsimp only [s,R]
      rw [←Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    have hpow : lowerInverseGrowthConstant A P 0*s^4≤d*s^4 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by linarith : 0≤s) 4)
    apply hpow.trans
    rw [he]
    apply (QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le hd hR).trans
    apply Real.exp_le_exp.mpr
    dsimp only [b]
    nlinarith
  have hVL : V≤L := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith))
  have hML : M≤L := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith))
  refine ⟨?_,hH.trans hVL,hY.trans hVL,hML⟩
  have hp : H+2≤4*V^2 := by nlinarith [sq_nonneg (V-1)]
  have hh := mul_le_mul_of_nonneg_left hp (Real.exp_pos (Real.exp (a*R))).le
  have hc := double_exp_sandwich_cost ha hb hR
  apply hh.trans
  convert hc using 1
  ring

#print axioms exists_horizon_trace_geometry
end QuantitativeEulerEndpointCommonReconstruction
