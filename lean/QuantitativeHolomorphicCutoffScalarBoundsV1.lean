module

public import QuantitativeHolomorphicGrowingScheduledTraceRateV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open AsymptoticCylinderModeComparison AsymptoticFourierNorm AsymptoticCylinder

theorem reciprocal_exp_gap_le {a : ℝ} (ha : 0<a) :
    1/(1-Real.exp (-a))≤1+1/a := by
  have he : 1<Real.exp a := Real.one_lt_exp_iff.mpr ha
  have hgap : 0<1-Real.exp (-a) := by
    have hn : Real.exp (-a)<1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  apply (div_le_iff₀ hgap).mpr
  rw [Real.exp_neg]
  have h := Real.add_one_le_exp a
  have hid : (1+1/a)*(1-(Real.exp a)⁻¹)-1=
      (Real.exp a-(a+1))/(a*Real.exp a) := by field_simp; ring
  have hn : 0≤(Real.exp a-(a+1))/(a*Real.exp a) := div_nonneg (by linarith) (by positivity)
  linarith

def localizedCoefficient (t : ℕ) (scale : ℝ) : ℝ :=
  1+2*(4*((2*t).factorial:ℝ)*(2*t+3)*Real.log 2+1)/scale

def slopeCoefficient (t : ℕ) (scale : ℝ) : ℝ :=
  1+2*((2*t+1:ℝ)*Real.log 2+1)/scale

theorem localizedCoefficient_nonneg (t : ℕ) {scale : ℝ} (hs : 0<scale) :
    0≤localizedCoefficient t scale := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  unfold localizedCoefficient
  positivity

theorem slopeCoefficient_nonneg (t : ℕ) {scale : ℝ} (hs : 0<scale) :
    0≤slopeCoefficient t scale := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  unfold slopeCoefficient
  positivity

theorem localizedErrorBound_le_inverse (t : ℕ) {scale Y : ℝ}
    (hs : 0<scale) (hY : 0<Y) :
    localizedErrorBound t scale Y≤localizedCoefficient t scale*(1+Y⁻¹) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hg := reciprocal_exp_gap_le (by positivity : 0<scale*Y/2)
  have hfirst : 4*(((2*t).factorial:ℝ)-1)*(2*t+3)*Real.log 2/(scale*Y/2)≤
      4*((2*t).factorial:ℝ)*(2*t+3)*Real.log 2/(scale*Y/2) := by gcongr; linarith
  unfold localizedErrorBound
  apply (add_le_add hfirst hg).trans
  have hid : 4*((2*t).factorial:ℝ)*(2*t+3)*Real.log 2/(scale*Y/2)+(1+1/(scale*Y/2))=
      1+(2*(4*((2*t).factorial:ℝ)*(2*t+3)*Real.log 2+1)/scale)*Y⁻¹ := by field_simp; ring
  rw [hid]
  unfold localizedCoefficient
  have hc : 0≤2*(4*((2*t).factorial:ℝ)*(2*t+3)*Real.log 2+1)/scale := by positivity
  have hy : 0≤Y⁻¹ := by positivity
  nlinarith

theorem massSlope_le_inverse (t : ℕ) {scale Y : ℝ} (hs : 0<scale) (hY : 0<Y) :
    massSlope t scale Y≤slopeCoefficient t scale*(1+Y⁻¹) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hg := reciprocal_exp_gap_le (by positivity : 0<scale*Y/2)
  unfold massSlope
  apply (add_le_add le_rfl hg).trans
  have hid : (2*t+1:ℝ)*Real.log 2/(scale*Y/2)+(1+1/(scale*Y/2))=
      1+(2*((2*t+1:ℝ)*Real.log 2+1)/scale)*Y⁻¹ := by field_simp; ring
  rw [hid]
  unfold slopeCoefficient
  have hc : 0≤2*((2*t+1:ℝ)*Real.log 2+1)/scale := by positivity
  have hy : 0≤Y⁻¹ := by positivity
  nlinarith

theorem localized_sqrt_product_le (t : ℕ) {scale Y : ℝ} (hs : 0<scale) (hY : 0<Y) :
    2*Real.sqrt (localizedErrorBound t scale Y)*Real.sqrt (massSlope t scale Y)≤
      (localizedCoefficient t scale+slopeCoefficient t scale)*(1+Y⁻¹) := by
  let L := localizedCoefficient t scale*(1+Y⁻¹)
  let S := slopeCoefficient t scale*(1+Y⁻¹)
  have hL : 0≤L := mul_nonneg (localizedCoefficient_nonneg t hs) (by positivity)
  have hS : 0≤S := mul_nonneg (slopeCoefficient_nonneg t hs) (by positivity)
  have h1 := Real.sqrt_le_sqrt (localizedErrorBound_le_inverse t hs hY)
  have h2 := Real.sqrt_le_sqrt (massSlope_le_inverse t hs hY)
  have hm := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have ha : 2*Real.sqrt L*Real.sqrt S≤L+S := by
    nlinarith [sq_nonneg (Real.sqrt L-Real.sqrt S),Real.sq_sqrt hL,Real.sq_sqrt hS]
  calc
    _ ≤ 2*Real.sqrt L*Real.sqrt S := by nlinarith only [hm]
    _ ≤ L+S := ha
    _ = _ := by dsimp [L,S]; ring

theorem inverse_sqrt_weight_le_trace_power (h : ℕ) :
    (Real.sqrt (2*h+2:ℝ))⁻¹≤(h+1:ℝ)^(-(1/3:ℝ)) := by
  have hpos : (0:ℝ)<h+1 := by positivity
  have hroot : (Real.sqrt (2*h+2:ℝ))⁻¹≤(Real.sqrt (h+1:ℝ))⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hpos) (Real.sqrt_le_sqrt (by nlinarith [(Nat.cast_nonneg h : (0:ℝ)≤h)]))
  apply hroot.trans
  rw [Real.sqrt_eq_rpow,←Real.rpow_neg hpos.le]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg h : (0:ℝ)≤h)]) (by norm_num)

#print axioms localized_sqrt_product_le
#print axioms inverse_sqrt_weight_le_trace_power

end QuantitativeHolomorphic.Schedule
