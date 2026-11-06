module

public import QuantitativeEulerEndpointCommonEnvelopeV1
public import QuantitativeEulerEndpointInitialEffortV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrimeBlocks

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)

theorem envelopeConstant_nonneg {M : ℝ} (hM : 1≤M) :
    0≤envelopeConstant N hN excluded threshold M := by
  have hm := Real.log_nonneg hM
  have h4 := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
  have h3 := Real.log_nonneg (by norm_num : (1:ℝ)≤3)
  have hc := (QuantitativeEulerEndpointSparsePrefix.preparedPrefix N hN excluded threshold).constant_pos.le
  unfold envelopeConstant
  positivity

theorem envelope_log_diagonal {M : ℝ} (hM : 1≤M) (n : ℕ) :
    Real.log (envelope N hN excluded threshold M n n)≤
      (2*envelopeConstant N hN excluded threshold M)*(4:ℝ)^n := by
  have h := envelope_log N hN excluded threshold hM n n
  have hn2 : ((n+1:ℕ):ℝ)≤(2:ℝ)^n := by
    exact_mod_cast Nat.succ_le_of_lt (show n<2^n from Nat.lt_two_pow_self)
  have hn : (n:ℝ)+1≤(4:ℝ)^n := by
    push_cast at hn2
    exact hn2.trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (2:ℝ)≤4) n)
  have hh := mul_le_mul_of_nonneg_left hn (envelopeConstant_nonneg N hN excluded threshold hM)
  nlinarith only [h,hh]

theorem log_polynomial_envelope {M A x : ℝ} (hM : 1≤M) (hA : 1≤A)
    (hx : 0<x) (r n : ℕ)
    (hbound : x≤A*(envelope N hN excluded threshold M n n)^r) :
    Real.log x≤(Real.log A+2*(r:ℝ)*envelopeConstant N hN excluded threshold M)*(4:ℝ)^n := by
  have hV : 0<envelope N hN excluded threshold M n n :=
    (show 0<M by linarith).trans_le (envelope_base N hN excluded threshold (by linarith) n n)
  have hh := Real.log_le_log hx hbound
  rw [Real.log_mul (show A≠0 by linarith) (pow_pos hV r).ne',Real.log_pow] at hh
  have hlog := mul_le_mul_of_nonneg_left (envelope_log_diagonal N hN excluded threshold hM n) (Nat.cast_nonneg r : (0:ℝ)≤r)
  have ha := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) (Real.log_nonneg hA)
  nlinarith only [hh,hlog,ha]

#print axioms envelope_log_diagonal
#print axioms log_polynomial_envelope
end QuantitativeEulerEndpointPrimeBlocks

namespace QuantitativeEulerEndpointInitialWeighted

theorem cap_ge_one {ι : Type*} [Fintype ι] (C a : ι → ℝ) (ha : ∀ i, 0<a i) : 1≤cap C a := by
  have hh : 0≤∑ i,(a i)⁻¹*(C i)^2 := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (inv_nonneg.mpr (ha i).le) (sq_nonneg _))
  unfold cap
  linarith

theorem effort_log_bound {ι : Type*} [Fintype ι] (C a : ι → ℝ) (ha : ∀ i, 0<a i) :
    Real.log ((effort C a:ℝ)+1)≤Real.log 4+Real.log (cap C a) := by
  have hc := cap_ge_one C a ha
  have hpos : 0<cap C a := by linarith
  have hh := Nat.ceil_lt_add_one (show 0≤2*cap C a by positivity)
  change (effort C a:ℝ)<2*cap C a+1 at hh
  have he : (effort C a:ℝ)+1≤4*cap C a := by linarith
  have hlog := Real.log_le_log (show 0<(effort C a:ℝ)+1 by positivity) he
  rwa [Real.log_mul (by norm_num) hpos.ne'] at hlog

#print axioms effort_log_bound
end QuantitativeEulerEndpointInitialWeighted
