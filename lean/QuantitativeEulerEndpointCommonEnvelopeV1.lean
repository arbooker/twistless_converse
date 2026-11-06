module

public import QuantitativeEulerEndpointPrimeSizesV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrimeBlocks
open QuantitativeEulerEndpointSparsePrefix

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)

def envelope (M : ℝ) (n j : ℕ) : ℝ := M*(4:ℝ)^n*bound N hN excluded threshold j

def envelopeConstant (M : ℝ) : ℝ :=
  Real.log M+Real.log 4+Real.log 3+4*(preparedPrefix N hN excluded threshold).constant

theorem envelope_base {M : ℝ} (hM : 0≤M) (n j : ℕ) : M≤envelope N hN excluded threshold M n j := by
  have hX : 1≤bound N hN excluded threshold j := by linarith [bound_ge_three N hN excluded threshold j]
  have hh := mul_le_mul (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) hX (by norm_num) (by positivity)
  have hh' := mul_le_mul_of_nonneg_left hh hM
  simpa only [envelope,one_mul,mul_one,←mul_assoc] using hh'

theorem envelope_height {M H : ℝ} (hM : 0≤M) (hH : H≤M) (n j : ℕ) :
    H*(4:ℝ)^n≤envelope N hN excluded threshold M n j := by
  have hX : 1≤bound N hN excluded threshold j := by linarith [bound_ge_three N hN excluded threshold j]
  have hh := mul_le_mul_of_nonneg_left hX (show 0≤M*(4:ℝ)^n by positivity)
  exact (mul_le_mul_of_nonneg_right hH (by positivity)).trans (by simpa only [envelope,mul_one] using hh)

theorem envelope_cutoff {M : ℝ} (hM : 1≤M) (n j : ℕ) :
    bound N hN excluded threshold j≤envelope N hN excluded threshold M n j := by
  have hh : 1≤M*(4:ℝ)^n := by
    have h := mul_le_mul hM (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) (by norm_num : (0:ℝ)≤1) (by linarith : 0≤M)
    simpa only [mul_one] using h
  have hX : 0≤bound N hN excluded threshold j := by linarith [bound_ge_three N hN excluded threshold j]
  simpa only [envelope,one_mul] using mul_le_mul_of_nonneg_right hh hX

theorem envelope_log {M : ℝ} (hM : 1≤M) (n j : ℕ) :
    Real.log (envelope N hN excluded threshold M n j)≤
      envelopeConstant N hN excluded threshold M*((4:ℝ)^j+n+1) := by
  have hMpos : 0<M := by linarith
  have hXpos : 0<bound N hN excluded threshold j := by linarith [bound_ge_three N hN excluded threshold j]
  rw [envelope,Real.log_mul (mul_pos hMpos (by positivity)).ne' hXpos.ne',
    Real.log_mul hMpos.ne' (by positivity),Real.log_pow]
  have hXlog := bound_log N hN excluded threshold j
  have hMlog : 0≤Real.log M := Real.log_nonneg hM
  have h4 : 0≤Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have h3 : 0≤Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
  have hC := (preparedPrefix N hN excluded threshold).constant_pos.le
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hj : 0≤(4:ℝ)^j := by positivity
  unfold envelopeConstant
  nlinarith [mul_nonneg hMlog hj,mul_nonneg hMlog hn,
    mul_nonneg h4 hj,mul_nonneg (add_nonneg h3 (mul_nonneg (by norm_num : (0:ℝ)≤4) hC)) hn]

#print axioms envelope_base
#print axioms envelope_height
#print axioms envelope_cutoff
#print axioms envelope_log
end QuantitativeEulerEndpointPrimeBlocks
