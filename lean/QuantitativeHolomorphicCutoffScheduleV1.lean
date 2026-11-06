module

public import QuantitativeHolomorphicTerminalClosedTraceV1
public import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

/-- The least binary exponent exceeding a real threshold, with a positive
integer argument even when the threshold is negative. -/
def binaryDepth (x : ℝ) : ℕ := Nat.clog 2 (⌈x⌉₊+1)

theorem binaryDepth_lower (x : ℝ) : x≤(2:ℝ)^binaryDepth x := by
  have hc : x≤(⌈x⌉₊:ℝ) := Nat.le_ceil x
  have hp := Nat.le_pow_clog (by norm_num : 1<2) (⌈x⌉₊+1)
  have hp' : (⌈x⌉₊:ℝ)+1≤(2:ℝ)^binaryDepth x := by exact_mod_cast hp
  linarith

theorem binaryDepth_power_upper (x : ℝ) (hx : 0≤x) :
    (2:ℝ)^binaryDepth x≤2*(x+2) := by
  let M := ⌈x⌉₊+1
  have hM : 0<M := by dsimp [M]; omega
  have hc : (M:ℝ)≤x+2 := by
    have ht := Nat.ceil_lt_add_one hx
    dsimp [M]
    push_cast
    linarith
  have hp : 2^Nat.clog 2 M≤2*M := by
    by_cases hm : M=1
    · simp [hm]
    · have hm1 : 1<M := by omega
      have ht := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hm1
      have hn := Nat.clog_pos (by norm_num : 1<2) hm1
      have he : Nat.clog 2 M=(Nat.clog 2 M).pred+1 := (Nat.succ_pred_eq_of_pos hn).symm
      rw [he,pow_succ]
      omega
  have hp' : (2:ℝ)^binaryDepth x≤2*(M:ℝ) := by exact_mod_cast hp
  linarith

theorem binaryDepth_complexity (x : ℝ) (hx : 0≤x) :
    (4:ℝ)^binaryDepth x≤4*(x+2)^2 := by
  have hp := binaryDepth_power_upper x hx
  have he : (4:ℝ)^binaryDepth x=((2:ℝ)^binaryDepth x)^2 := by
    rw [←pow_mul, mul_comm, pow_mul]
    norm_num
  rw [he]
  nlinarith [mul_self_le_mul_self (by positivity : 0≤(2:ℝ)^binaryDepth x) hp]

theorem geometric_depth_bound {B t : ℝ} (ht : 0<t) :
    B*(1/2:ℝ)^binaryDepth (B/t)≤t := by
  have hp := binaryDepth_lower (B/t)
  have hp0 : 0<(2:ℝ)^binaryDepth (B/t) := by positivity
  have hb : B≤(2:ℝ)^binaryDepth (B/t)*t := (div_le_iff₀ ht).mp hp
  rw [one_div_pow,mul_one_div]
  exact (div_le_iff₀ hp0).mpr (by nlinarith)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- A literal efficient Newton cutoff. Its binary exponent grows only
linearly in the logarithm of the requested accuracy. -/
def newtonDepth (P : Parameters A) (D t : ℝ) : ℕ :=
  binaryDepth (Real.log (4*D/(t*Real.sqrt (countGramLower A P)))/countGramLower A P)

theorem newtonDepth_error (P : Parameters A) {D t : ℝ} (hD : 0<D) (ht : 0<t) :
    D*((1-countGramLower A P)^(2^newtonDepth A P D t)/Real.sqrt (countGramLower A P))≤t/4 := by
  let c := countGramLower A P
  have hc : 0<c := countGramLower_pos A P
  have hc1 : c≤1 := countGramLower_le_one A P
  have hs : 0<Real.sqrt c := Real.sqrt_pos.2 hc
  let n := newtonDepth A P D t
  let R := 4*D/(t*Real.sqrt c)
  have hR : 0<R := by dsimp [R]; positivity
  have hp : Real.log R≤c*(2:ℝ)^n := by
    have h := binaryDepth_lower (Real.log R/c)
    exact (div_le_iff₀ hc).mp h |>.trans_eq (mul_comm _ _)
  have hpow : (1-c)^(2^n)≤Real.exp (-(c*(2:ℝ)^n)) := by
    calc
      _ ≤ (Real.exp (-c))^(2^n) := pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg c) _
      _ = _ := by rw [←Real.exp_nat_mul]; push_cast; congr 1; ring
  have hexp : Real.exp (-(c*(2:ℝ)^n))≤1/R := by
    calc
      _ ≤ Real.exp (-Real.log R) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log hR,one_div]
  have hf := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hpow.trans hexp) hs.le) hD.le
  apply hf.trans_eq
  dsimp [R]
  field_simp

#print axioms binaryDepth_complexity
#print axioms newtonDepth_error

end QuantitativeHolomorphic.Schedule
