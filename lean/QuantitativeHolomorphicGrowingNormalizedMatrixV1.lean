module

public import QuantitativeHolomorphicGrowingMatrixV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem normalizedCountMatrixHeight_growth (hN : 0<N) (j J n : ℕ) {a b u : ℝ}
    (ha : 0≤a) (_hb : 0≤b) (hu : 1≤u)
    (hR : rawCountMatrixHeight A hN j J≤Real.exp (a*u^2))
    (hn : (4:ℝ)^n≤b*u) :
    normalizedCountMatrixHeight A hN j J n≤Real.exp ((2+a+b*(16+2*a))*u^3) := by
  let R := rawCountMatrixHeight A hN j J
  have hR0 : 0≤R := le_trans zero_le_one (rawCountMatrixHeight_one_le A hN j J)
  have hu2 : 1≤u^2 := by nlinarith
  have hu23 : u^2≤u^3 := by nlinarith [mul_nonneg (by nlinarith : 0≤u-1) (sq_nonneg u)]
  have hR2 : R^2≤Real.exp ((2*a)*u^2) := by
    have hm := mul_self_le_mul_self hR0 hR
    have he : Real.exp (a*u^2)*Real.exp (a*u^2)=Real.exp ((2*a)*u^2) := by
      rw [←Real.exp_add]; congr 1; ring
    nlinarith only [hm,he]
  have hbase : 16*R^2≤Real.exp ((16+2*a)*u^2) :=
    (mul_le_mul_of_nonneg_left hR2 (by norm_num)).trans (constant_mul_exp_le (by norm_num) hu2)
  have hn' : ((4^n:ℕ):ℝ)≤b*u := by exact_mod_cast hn
  have hp : (16*R^2)^(4^n)≤Real.exp (b*(16+2*a)*u^3) := by
    apply (pow_le_pow_left₀ (by positivity) hbase (4^n)).trans
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hn' (by positivity : 0≤(16+2*a)*u^2)
    nlinarith only [hm]
  have hfront : 2*R≤Real.exp ((2+a)*u^3) := by
    apply (mul_le_mul_of_nonneg_left hR (by norm_num)).trans
    apply (constant_mul_exp_le (c:=2) (a:=a) (by norm_num) hu2).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu23 (by positivity))
  have hm := mul_le_mul hfront hp (by positivity) (Real.exp_nonneg _)
  apply hm.trans_eq
  rw [←Real.exp_add]
  congr 1
  ring

def normalizedMatrixGrowthConstant (hN : 0<N) (P : Parameters A) (C : ℝ) : ℝ :=
  let a := rawMatrixGrowthConstant A hN (reconstructionGrowthConstant A P C) (foldGrowthConstant A P C)
  let b := 4*(newtonGrowthConstant A P C+2)^2
  2+a+b*(16+2*a)

/-- The actual normalized reconstruction integer matrix height has exponent
O((log X)^12), with all constants obtained from the fixed certificate. -/
theorem growing_normalized_matrix_height (hN : 0<N) (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    let j := reconstructionDepth A P D (Real.exp (-8*s)) n
    let J := foldCutoff A P D (Real.exp (-8*s)) j n
    normalizedCountMatrixHeight A hN j J n≤Real.exp (normalizedMatrixGrowthConstant A hN P C*s^12) := by
  let D : ℝ := 2*d+2
  let n := newtonDepth A P D (Real.exp (-8*s))
  let j := reconstructionDepth A P D (Real.exp (-8*s)) n
  let J := foldCutoff A P D (Real.exp (-8*s)) j n
  let a := rawMatrixGrowthConstant A hN (reconstructionGrowthConstant A P C) (foldGrowthConstant A P C)
  let b := 4*(newtonGrowthConstant A P C+2)^2
  have hL := reconstructionGrowthConstant_nonneg A P hC
  have hF := foldGrowthConstant_nonneg A P hC
  have hc : 0≤certificateMatrixBase A hN := le_trans zero_le_one
    (Classical.choose_spec (scaledCutCountExpression_uniform_matrix_height A hN)).1
  have ha : 0≤a := by dsimp [a,rawMatrixGrowthConstant]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hs4 : 1≤s^4 := by nlinarith [sq_nonneg (s^2-1)]
  have hraw := rawCountMatrixHeight_growth A hN hL hF hs4
    (growing_reconstruction_depth A P hC hs d hd) (growing_fold_cutoff A P hC hs d hd)
  have hn : (4:ℝ)^n≤b*s^4 := (growing_newton_complexity A P hC hs d hd).2.1
  have hh := normalizedCountMatrixHeight_growth A hN j J n ha hb hs4 hraw hn
  convert hh using 1
  congr 1
  dsimp [normalizedMatrixGrowthConstant,a,b]
  ring

#print axioms normalizedCountMatrixHeight_growth
#print axioms growing_normalized_matrix_height

end QuantitativeHolomorphic.Schedule
