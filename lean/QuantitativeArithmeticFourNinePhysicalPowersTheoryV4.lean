module

public import QuantitativeArithmeticComplexHornerBoundsTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticFourNinePhysicalPowers. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticFourNinePhysicalPowersV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticFourNinePhysicalPowers
open Complex

theorem log_bounds : 15*Real.log 4<10*Real.log 9 ∧ 10*Real.log 9<16*Real.log 4 := by
  constructor
  · have h := Real.log_lt_log (by norm_num : (0:ℝ)<4^15) (by norm_num : (4:ℝ)^15<9^10)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  · have h := Real.log_lt_log (by norm_num : (0:ℝ)<9^10) (by norm_num : (9:ℝ)^10<4^16)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h

theorem norm_power_formula (b : ℝ) (hb : 0<b) (h : ℂ) (n : ℕ) :
    (‖(b:ℂ)^h‖^2)^n=Real.exp ((2*h.re)*(n*Real.log b)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb,Real.rpow_def_of_pos hb,
    ←Real.exp_nat_mul,←Real.exp_nat_mul]
  congr 1
  ring

theorem physical_power_bounds (h : ℂ) :
    (1≤‖(4:ℂ)^h‖^2 → (‖(4:ℂ)^h‖^2)^15≤(‖(9:ℂ)^h‖^2)^10 ∧
      (‖(9:ℂ)^h‖^2)^10≤(‖(4:ℂ)^h‖^2)^16) ∧
    (‖(4:ℂ)^h‖^2≤1 → (‖(4:ℂ)^h‖^2)^16≤(‖(9:ℂ)^h‖^2)^10 ∧
      (‖(9:ℂ)^h‖^2)^10≤(‖(4:ℂ)^h‖^2)^15) := by
  have hf : ‖(4:ℂ)^h‖^2=Real.exp ((2*h.re)*Real.log 4) := by
    simpa using norm_power_formula 4 (by norm_num) h 1
  have hlog : 0<Real.log 4 := Real.log_pos (by norm_num)
  have h4 (n : ℕ) : (‖(4:ℂ)^h‖^2)^n=Real.exp ((2*h.re)*(n*Real.log 4)) := by
    simpa only [Complex.ofReal_ofNat] using norm_power_formula 4 (by norm_num) h n
  have h9 (n : ℕ) : (‖(9:ℂ)^h‖^2)^n=Real.exp ((2*h.re)*(n*Real.log 9)) := by
    simpa only [Complex.ofReal_ofNat] using norm_power_formula 9 (by norm_num) h n
  have hb := log_bounds
  constructor
  · intro hx
    have ht : 0≤2*h.re := by
      rw [hf,Real.one_le_exp_iff] at hx
      nlinarith
    constructor
    · rw [h4,h9,Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left hb.1.le ht
    · rw [h9,h4,Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left hb.2.le ht
  · intro hx
    have ht : 2*h.re≤0 := by
      rw [hf,Real.exp_le_one_iff] at hx
      nlinarith
    constructor
    · rw [h4,h9,Real.exp_le_exp]
      exact mul_le_mul_of_nonpos_left hb.2.le ht
    · rw [h9,h4,Real.exp_le_exp]
      exact mul_le_mul_of_nonpos_left hb.1.le ht
#print axioms physical_power_bounds
end QuantitativeArithmeticFourNinePhysicalPowers
end
end

/-! ## QuantitativeArithmeticFourNineIntervalV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticFourNinePhysicalPowers

def IntervalExcluded (xl xh yl yh : ℚ) : Prop :=
  (1<xl ∧ (yh^10<xl^15 ∨ xh^16<yl^10)) ∨
  (xh<1 ∧ (yh^10<xl^16 ∨ xh^15<yl^10))

theorem excluded_interval (h : ℂ) (xl xh yl yh : ℚ)
    (hxl : 0≤xl) (hyl : 0≤yl) (hex : IntervalExcluded xl xh yl yh)
    (hx : (xl:ℝ)≤‖(4:ℂ)^h‖^2 ∧ ‖(4:ℂ)^h‖^2≤(xh:ℝ))
    (hy : (yl:ℝ)≤‖(9:ℂ)^h‖^2 ∧ ‖(9:ℂ)^h‖^2≤(yh:ℝ)) : False := by
  have hxl' : (0:ℝ)≤(xl:ℝ) := by exact_mod_cast hxl
  have hyl' : (0:ℝ)≤(yl:ℝ) := by exact_mod_cast hyl
  have hxp (n : ℕ) := pow_le_pow_left₀ hxl' hx.1 n
  have pxh (n : ℕ) := pow_le_pow_left₀ (sq_nonneg ‖(4:ℂ)^h‖) hx.2 n
  have hyp (n : ℕ) := pow_le_pow_left₀ hyl' hy.1 n
  have pyh (n : ℕ) := pow_le_pow_left₀ (sq_nonneg ‖(9:ℂ)^h‖) hy.2 n
  rcases hex with ⟨habove,ha | hb⟩ | ⟨hbelow,ha | hb⟩
  · have ht : (1:ℝ)<(xl:ℝ) := by exact_mod_cast habove
    have hp := (physical_power_bounds h).1 (by linarith)
    have hn := (hxp 15).trans (hp.1.trans (pyh 10))
    have hc : (yh:ℝ)^10<(xl:ℝ)^15 := by exact_mod_cast ha
    exact (not_lt_of_ge hn) hc
  · have ht : (1:ℝ)<(xl:ℝ) := by exact_mod_cast habove
    have hp := (physical_power_bounds h).1 (by linarith)
    have hn := (hyp 10).trans (hp.2.trans (pxh 16))
    have hc : (xh:ℝ)^16<(yl:ℝ)^10 := by exact_mod_cast hb
    exact (not_lt_of_ge hn) hc
  · have ht : (xh:ℝ)<1 := by exact_mod_cast hbelow
    have hp := (physical_power_bounds h).2 (by linarith)
    have hn := (hxp 16).trans (hp.1.trans (pyh 10))
    have hc : (yh:ℝ)^10<(xl:ℝ)^16 := by exact_mod_cast ha
    exact (not_lt_of_ge hn) hc
  · have ht : (xh:ℝ)<1 := by exact_mod_cast hbelow
    have hp := (physical_power_bounds h).2 (by linarith)
    have hn := (hyp 10).trans (hp.2.trans (pxh 15))
    have hc : (xh:ℝ)^15<(yl:ℝ)^10 := by exact_mod_cast hb
    exact (not_lt_of_ge hn) hc
#print axioms excluded_interval
end QuantitativeArithmeticFourNinePhysicalPowers
end
end
