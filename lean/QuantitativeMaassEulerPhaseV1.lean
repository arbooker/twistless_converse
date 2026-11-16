module

public import QuantitativeMaassEulerMomentSeriesV1
public import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- The actual two-sided Fourier phase with reflection parity (-1)^sigma. -/
def eulerParityPhase (σ n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I)+
    (-1:ℂ)^σ*Complex.exp (-(((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I))

theorem eulerParityPhase_norm_le (σ n : ℕ) (x : ℝ) : ‖eulerParityPhase σ n x‖≤2 := by
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  rw [Complex.norm_exp_ofReal_mul_I]
  have hh : -(((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I)=
      ((-(2*Real.pi*(n:ℝ)*x):ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [hh,Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem eulerParityPhase_continuous (σ n : ℕ) : Continuous (eulerParityPhase σ n) := by
  unfold eulerParityPhase
  fun_prop

theorem eulerParityPhase_periodic (σ n : ℕ) : Function.Periodic (eulerParityPhase σ n) 1 := by
  intro x
  have hh : (((2*Real.pi*(n:ℝ)*(x+1):ℝ):ℂ)*Complex.I)=
      (((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I)+(n:ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
  unfold eulerParityPhase
  rw [hh,neg_add,Complex.exp_add,Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,
    Complex.exp_neg ((n:ℂ)*(2*Real.pi*Complex.I)),Complex.exp_nat_mul_two_pi_mul_I,inv_one,mul_one,mul_one]

theorem eulerParityPhase_reflection (σ n : ℕ) (x : ℝ) :
    eulerParityPhase σ n (-x)=(-1:ℂ)^σ*eulerParityPhase σ n x := by
  have hs : ((-1:ℂ)^σ)^2=1 := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  have hh : (((2*Real.pi*(n:ℝ)*(-x):ℝ):ℂ)*Complex.I)=
      -(((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I) := by push_cast; ring
  unfold eulerParityPhase
  rw [hh,neg_neg,mul_add,←mul_assoc,←pow_two,hs,one_mul,add_comm]

theorem eulerParityPhase_add_two (σ n : ℕ) (x : ℝ) :
    eulerParityPhase (σ+2) n x=eulerParityPhase σ n x := by
  simp only [eulerParityPhase,pow_add,neg_sq,one_pow,mul_one]

/-- Differentiation switches parity and multiplies by the literal Fourier frequency. -/
theorem eulerParityPhase_hasDerivAt (σ n : ℕ) (x : ℝ) :
    HasDerivAt (eulerParityPhase σ n)
      ((((2*Real.pi*(n:ℝ):ℝ):ℂ)*Complex.I)*eulerParityPhase (σ+1) n x) x := by
  let ω : ℂ := ((2*Real.pi*(n:ℝ):ℝ):ℂ)*Complex.I
  have hd : HasDerivAt (fun y : ℝ => ((2*Real.pi*(n:ℝ)*y:ℝ):ℂ)*Complex.I) ω x := by
    simpa only [id_eq,mul_one,ω] using
      (((hasDerivAt_id x).const_mul (2*Real.pi*(n:ℝ))).ofReal_comp.mul_const Complex.I)
  have hh := hd.cexp.add (hd.neg.cexp.const_mul ((-1:ℂ)^σ))
  convert hh using 1
  · rfl
  · unfold eulerParityPhase
    rw [pow_succ]
    dsimp [ω]
    ring

#print axioms eulerParityPhase_norm_le
#print axioms eulerParityPhase_continuous
#print axioms eulerParityPhase_periodic
#print axioms eulerParityPhase_reflection
#print axioms eulerParityPhase_add_two
#print axioms eulerParityPhase_hasDerivAt

end QuantitativeMaass
