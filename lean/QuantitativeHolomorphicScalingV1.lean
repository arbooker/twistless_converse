module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

/-!
Elementary, unconditional parameter estimates for the quantitative
holomorphic argument.  No trace estimate or Euler-count estimate is
postulated in this file.  The analytic estimate to which these parameters
are applied belongs in a separate, explicitly conditional reduction.
-/

namespace QuantitativeHolomorphic

def observationScale (a k : ℝ) : ℝ :=
  Real.exp (a * Real.sqrt (Real.log (Real.log k)))

def bridgeError (C k X : ℝ) : ℝ :=
  Real.exp (Real.exp (C * (Real.log X) ^ 2) - Real.log k / 2)

def remainderScale (δ k : ℝ) : ℝ :=
  k * (Real.log (Real.log k)) ^ (-δ)

theorem parameter_exponents {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    0 < 2 * δ ∧ 2 * δ < 1 ∧
      0 < (1 - 2 * δ) / 2 ∧ 2 * δ < 1 - (1 - 2 * δ) / 2 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem log_observationScale (a k : ℝ) :
    Real.log (observationScale a k) = a * Real.sqrt (Real.log (Real.log k)) := by
  simp [observationScale]

theorem log_observationScale_sq (a k : ℝ)
    (hL : 0 ≤ Real.log (Real.log k)) :
    (Real.log (observationScale a k)) ^ 2 = a ^ 2 * Real.log (Real.log k) := by
  rw [log_observationScale, mul_pow, Real.sq_sqrt hL]

theorem regular_error_at_scale {a k : ℝ} (ha : 0 ≤ a)
    (hL : 0 ≤ Real.log (Real.log k)) (δ : ℝ) :
    (Real.log (observationScale a k)) ^ (-(2 * δ)) =
      a ^ (-(2 * δ)) * (Real.log (Real.log k)) ^ (-δ) := by
  rw [log_observationScale, Real.mul_rpow ha (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow, ← Real.rpow_mul hL]
  congr 2
  ring

theorem exp_ge_four_mul {L : ℝ} (hL : 16 ≤ L) : 4 * L ≤ Real.exp L := by
  have he := Real.add_one_le_exp (L / 2)
  have hs : (1 + L / 2) ^ 2 ≤ (Real.exp (L / 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hid : (Real.exp (L / 2)) ^ 2 = Real.exp L := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hl : 0 ≤ L * (L - 16) := mul_nonneg (by linarith) (by linarith)
  rw [hid] at hs
  nlinarith

theorem exp_half_le_quarter_exp {L : ℝ} (hL : 16 ≤ L) :
    Real.exp (L / 2) ≤ Real.exp L / 4 := by
  have he := Real.add_one_le_exp (L / 2)
  have hp := Real.exp_pos (L / 2)
  have hm : 0 ≤ Real.exp (L / 2) * (Real.exp (L / 2) - 4) :=
    mul_nonneg hp.le (by linarith)
  have hid : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid]
  nlinarith

/-- The double exponential in the finite-branch error is absorbed with an
explicit fixed power saving, once the small observation-scale constant
satisfies `C * a² ≤ 1/2`. -/
theorem bridgeError_at_scale {a C k : ℝ} (hk : 1 < k)
    (hL : 16 ≤ Real.log (Real.log k)) (hCa : C * a ^ 2 ≤ 1 / 2) :
    bridgeError C k (observationScale a k) ≤ Real.exp (-Real.log k / 4) := by
  have hlog : 0 < Real.log k := Real.log_pos hk
  have hL0 : 0 ≤ Real.log (Real.log k) := by linarith
  have hi : Real.exp (C * (Real.log (observationScale a k)) ^ 2) ≤
      Real.log k / 4 := by
    rw [log_observationScale_sq a k hL0]
    calc
      Real.exp (C * (a ^ 2 * Real.log (Real.log k))) ≤
          Real.exp (Real.log (Real.log k) / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hCa hL0]
      _ ≤ Real.exp (Real.log (Real.log k)) / 4 := exp_half_le_quarter_exp hL
      _ = Real.log k / 4 := by rw [Real.exp_log hlog]
  apply Real.exp_le_exp.mpr
  linarith

theorem power_saving_le_loglog {δ k : ℝ} (hk : 1 < k)
    (hL : 16 ≤ Real.log (Real.log k)) (hδ' : δ ≤ 1) :
    Real.exp (-Real.log k / 4) ≤ (Real.log (Real.log k)) ^ (-δ) := by
  let L := Real.log (Real.log k)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by dsimp [L]; linarith)
  have hlogL' : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hLp]
  have hm : δ * Real.log L ≤ L :=
    (mul_le_mul_of_nonneg_right hδ' hlogL).trans (by simpa using hlogL')
  have he : 4 * L ≤ Real.log k := by
    have hh := exp_ge_four_mul hL
    rw [Real.exp_log (Real.log_pos hk)] at hh
    exact hh
  change Real.exp (-Real.log k / 4) ≤ L ^ (-δ)
  rw [Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem exists_scale_constant {C : ℝ} (hC : 0 ≤ C) :
    ∃ a : ℝ, 0 < a ∧ C * a ^ 2 ≤ 1 / 2 := by
  refine ⟨1 / (2 * (C + 1)), by positivity, ?_⟩
  have hp : 0 < 2 * (C + 1) := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  field_simp
  nlinarith [sq_nonneg C]

#print axioms parameter_exponents
#print axioms regular_error_at_scale
#print axioms bridgeError_at_scale
#print axioms power_saving_le_loglog
#print axioms exists_scale_constant

end QuantitativeHolomorphic
