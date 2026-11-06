module

public import QuantitativeHolomorphicGrowingRawLengthV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

theorem constant_mul_exp_le {c a u : ℝ} (hc : 0≤c) (hu : 1≤u) :
    c*Real.exp (a*u)≤Real.exp ((c+a)*u) := by
  have he : c≤Real.exp c := by linarith [Real.add_one_le_exp c]
  apply (mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)).trans
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hu hc]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def rawMatrixGrowthConstant (hN : 0<N) (a b : ℝ) : ℝ :=
  let K := 4*certificateMatrixBase A hN+b
  10+a*(2+K)+K

/-- Bound the literal integer representative height, including the actual
fixed certificate height and every growing depth/fold parameter. -/
theorem rawCountMatrixHeight_growth (hN : 0<N) {j J : ℕ} {a b u : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hu : 1≤u)
    (hj : (j:ℝ)≤a*u) (hJ : (J:ℝ)≤Real.exp (b*u)) :
    rawCountMatrixHeight A hN j J≤Real.exp (rawMatrixGrowthConstant A hN a b*u^2) := by
  let c := certificateMatrixBase A hN
  let B := 2*(1+(J:ℝ))*c
  let K := 4*c+b
  have hc1 : 1≤c := (Classical.choose_spec (scaledCutCountExpression_uniform_matrix_height A hN)).1
  have hc : 0≤c := by linarith
  have hB : 0≤B := by dsimp [B]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  have hu0 : 0≤u := by linarith
  have hu2 : 1≤u^2 := by nlinarith
  have huu : u≤u^2 := by nlinarith
  have hE : 1≤Real.exp (b*u) := Real.one_le_exp (mul_nonneg hb hu0)
  have hBE : B≤Real.exp (K*u) := by
    have h : B≤4*c*Real.exp (b*u) := by
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_left hJ hc,mul_le_mul_of_nonneg_left hE hc]
    exact h.trans (constant_mul_exp_le (by positivity) hu)
  have h2BE : 2*B≤Real.exp ((2+K)*u) :=
    (mul_le_mul_of_nonneg_left hBE (by norm_num)).trans (constant_mul_exp_le (by norm_num) hu)
  have hpow : (2*B)^j≤Real.exp (a*(2+K)*u^2) := by
    apply (pow_le_pow_left₀ (by positivity) h2BE j).trans
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hj (by positivity : 0≤(2+K)*u)
    nlinarith only [hm]
  have hBE2 : B≤Real.exp (K*u^2) :=
    hBE.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huu hK))
  have hprod : 2*(2*B)^j*B≤Real.exp ((2+a*(2+K)+K)*u^2) := by
    have hm := mul_le_mul hpow hBE2 hB (Real.exp_nonneg _)
    have hm' := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤2)
    have he : 2*(Real.exp (a*(2+K)*u^2)*Real.exp (K*u^2))=
        2*Real.exp ((a*(2+K)+K)*u^2) := by rw [←Real.exp_add]; congr 1; congr 1; ring
    have hh : 2*(2*B)^j*B≤2*Real.exp ((a*(2+K)+K)*u^2) := by
      calc
        _ = 2*((2*B)^j*B) := by ring
        _ ≤ 2*(Real.exp (a*(2+K)*u^2)*Real.exp (K*u^2)) := hm'
        _ = _ := he
    apply hh.trans
    convert constant_mul_exp_le (c:=2) (a:=a*(2+K)+K) (by norm_num) hu2 using 1
    congr 1
    ring
  have hmax : max 1 (2*(2*B)^j*B)≤Real.exp ((2+a*(2+K)+K)*u^2) := by
    apply max_le _ hprod
    apply Real.one_le_exp
    positivity
  change 8*max 1 (2*(2*B)^j*B)≤_
  apply (mul_le_mul_of_nonneg_left hmax (by norm_num)).trans
  convert constant_mul_exp_le (c:=8) (a:=2+a*(2+K)+K) (by norm_num) hu2 using 1
  congr 1
  dsimp [rawMatrixGrowthConstant,K,c]
  ring

#print axioms rawCountMatrixHeight_growth

end QuantitativeHolomorphic.Schedule
