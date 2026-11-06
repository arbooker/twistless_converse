module

public import QuantitativeHolomorphicTerminalClosedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open AsymptoticFourierNorm AsymptoticCylinderModeComparison

/-- The literal normalized Fourier cusp mass has a reciprocal-height term
and a reciprocal-weight term, with no hidden uniformity constant. -/
theorem normalized_massBound_le (h t : ℕ) {scale H : ℝ}
    (hs : 0<scale) (hH : 0<H) (hcut : Real.log 2≤scale*H/2) :
    massBound (2*h) t scale H/(2*h+2:ℝ)≤
      (2*t+1:ℝ)*Real.log 2/(scale*H/2)+2/(2*h+2:ℝ) := by
  let k : ℝ := 2*h+2
  let a := scale*H/2
  have hk : 0<k := by dsimp [k]; positivity
  have ha : 0<a := by dsimp [a]; positivity
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have he : Real.exp (-a)≤1/2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by dsimp [a]; linarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
  have hden : 0<1-Real.exp (-a) := by linarith
  have ht : 1/(1-Real.exp (-a))≤2 := (div_le_iff₀ hden).mpr (by linarith)
  have hcoef : (2*h+2*t+1:ℝ)≤(2*t+1:ℝ)*k := by
    dsimp [k]
    nlinarith [mul_nonneg (Nat.cast_nonneg h : (0:ℝ)≤h) (Nat.cast_nonneg t : (0:ℝ)≤t)]
  have hfirst := mul_le_mul_of_nonneg_right hcoef (div_nonneg hlog ha.le)
  have htotal : massBound (2*h) t scale H≤((2*t+1:ℝ)*Real.log 2/a)*k+2 := by
    unfold massBound
    push_cast
    dsimp [a] at ht hfirst ⊢
    convert add_le_add hfirst ht using 1 <;> ring
  have hr := div_le_div_of_nonneg_right htotal hk.le
  apply hr.trans_eq
  change (((2*t+1:ℝ)*Real.log 2/a)*k+2)/k = _
  rw [add_div,mul_div_cancel_right₀ _ hk.ne']

/-- Explicit upper height and weight thresholds make the actual normalized
Fourier mass at most any prescribed positive budget. -/
theorem normalized_massBound_budget (h t : ℕ) {scale H r : ℝ}
    (hs : 0<scale) (hH : 0<H)
    (hcut : Real.log 2≤scale*H/2)
    (hheight : 2*((2*t+1:ℝ)*Real.log 2)≤r*(scale*H/2))
    (hweight : 4≤r*(2*h+2:ℝ)) :
    massBound (2*h) t scale H/(2*h+2:ℝ)≤r := by
  have h1 : (2*t+1:ℝ)*Real.log 2/(scale*H/2)≤r/2 :=
    (div_le_iff₀ (by positivity : 0<scale*H/2)).mpr (by nlinarith)
  have h2 : 2/(2*h+2:ℝ)≤r/2 :=
    (div_le_iff₀ (by positivity : 0<(2*h+2:ℝ))).mpr (by nlinarith)
  exact (normalized_massBound_le h t hs hH hcut).trans (by linarith)

#print axioms normalized_massBound_le
#print axioms normalized_massBound_budget

end QuantitativeHolomorphic.Schedule
