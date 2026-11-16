module

public import QuantitativeMaassRationalExpressionHeightV1
public import QuantitativeHolomorphicExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticFiniteBranch QuantitativeHolomorphic
namespace QuantitativeMaass

/-- Simultaneous coefficient mass and integer matrix height control. -/
def ExponentialExpressionGrowth (E : ℕ→Expression) : Prop :=
  ∃ C : ℝ,0≤C ∧ ∀ m : ℕ,
    expressionBound (E m)≤Real.exp (C*((m:ℝ)+1)) ∧
    ExpressionMatrixBound (E m) (Real.exp (C*((m:ℝ)+1)))

theorem ExponentialExpressionGrowth.constant (E : Expression) :
    ExponentialExpressionGrowth (fun _ => E) := by
  obtain ⟨B,hB,hE⟩ := expression_matrix_bound_exists E
  let C := B+expressionBound E
  have hc : 0≤C := add_nonneg (zero_le_one.trans hB) (expressionBound_nonneg E)
  have hb : B≤C := le_add_of_nonneg_right (expressionBound_nonneg E)
  have he : expressionBound E≤C := le_add_of_nonneg_left (zero_le_one.trans hB)
  refine ⟨C,hc,?_⟩
  intro m
  have hh : C≤Real.exp (C*((m:ℝ)+1)) := by
    have h := Real.add_one_le_exp (C*((m:ℝ)+1))
    nlinarith [mul_nonneg hc (Nat.cast_nonneg m : (0:ℝ)≤m)]
  exact ⟨he.trans hh,hE.mono (hb.trans hh)⟩

theorem ExponentialExpressionGrowth.power (E : Expression) :
    ExponentialExpressionGrowth (powerExpression E) := by
  obtain ⟨B,hB,hE⟩ := expression_matrix_bound_exists E
  let C := 2*(B+expressionBound E)
  have he0 := expressionBound_nonneg E
  have hc : 0≤C := by dsimp only [C];positivity
  have hb : 2*B≤C := by dsimp only [C];linarith
  have he : expressionBound E≤C := by dsimp only [C];linarith
  have hce : C≤Real.exp C := by linarith [Real.add_one_le_exp C]
  refine ⟨C,hc,?_⟩
  intro m
  have hp : C^m≤Real.exp (C*((m:ℝ)+1)) := by
    calc
      _ ≤ (Real.exp C)^m := pow_le_pow_left₀ hc hce m
      _ = Real.exp ((m:ℝ)*C) := (Real.exp_nat_mul C m).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  constructor
  · rw [expressionBound_power]
    exact (pow_le_pow_left₀ he0 he m).trans hp
  · exact (hE.power (zero_le_one.trans hB) m).mono
      ((pow_le_pow_left₀ (by positivity : 0≤2*B) hb m).trans hp)

theorem ExponentialExpressionGrowth.compose {E F : ℕ→Expression}
    (hE : ExponentialExpressionGrowth E) (hF : ExponentialExpressionGrowth F) :
    ExponentialExpressionGrowth (fun m => composeExpression (E m) (F m)) := by
  obtain ⟨C,hC,hE⟩ := hE
  obtain ⟨D,hD,hF⟩ := hF
  refine ⟨C+D+1,by positivity,?_⟩
  intro m
  let X := Real.exp (C*((m:ℝ)+1))
  let Y := Real.exp (D*((m:ℝ)+1))
  have hx : 0≤X := (Real.exp_pos _).le
  have hy : 0≤Y := (Real.exp_pos _).le
  have htwo : 2≤Real.exp ((m:ℝ)+1) := by
    have hh := Real.add_one_le_exp ((m:ℝ)+1)
    have hm : (0:ℝ)≤m := Nat.cast_nonneg m
    linarith
  have hz : 2*X*Y≤Real.exp ((C+D+1)*((m:ℝ)+1)) := by
    calc
      _ ≤ Real.exp ((m:ℝ)+1)*X*Y := by gcongr
      _ = _ := by
        dsimp only [X,Y]
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
  constructor
  · rw [expressionBound_compose]
    have hh := mul_le_mul (hE m).1 (hF m).1 (expressionBound_nonneg (F m)) hx
    have hxy : X*Y≤2*X*Y := by nlinarith [mul_nonneg hx hy]
    exact hh.trans (hxy.trans hz)
  · exact ((hE m).2.compose (hF m).2 hy).mono hz

#print axioms ExponentialExpressionGrowth.constant
#print axioms ExponentialExpressionGrowth.power
#print axioms ExponentialExpressionGrowth.compose
end QuantitativeMaass
