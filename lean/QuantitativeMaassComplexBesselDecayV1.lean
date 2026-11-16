module

public import QuantitativeMaassComplexBesselV1
public import QuantitativeMaassEulerPhaseV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- The actual complex Bessel moment is dominated by the nonoscillatory
real moment at the real part of its argument. -/
theorem principalComplexMoment_norm_bound (j : ℕ) (r : ℝ) (z : ℂ) (hz : 0<z.re) :
    ‖principalComplexMoment j r z‖≤MaassKBessel.moment j 0 z.re := by
  calc
    _ ≤ ∫ u in Ioi (0:ℝ),‖principalComplexKernel j r z u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0:ℝ),Real.cosh u^j*Real.exp (-z.re*Real.cosh u) :=
      integral_mono (principalComplexKernel_integrable j r z hz).norm
        (MaassKBessel.zero_moment_integrable j hz) (fun u => principalComplexKernel_norm_bound j r z u)
    _ = _ := by simp only [MaassKBessel.moment,zero_mul,Real.cos_zero,mul_one]

theorem principalComplexMoment_decay_from (j : ℕ) (r a : ℝ) (z : ℂ) (ha : 0<a) (hz : a≤z.re) :
    ‖principalComplexMoment j r z‖≤Real.exp (a-z.re)*MaassKBessel.moment j 0 a := by
  have hh := bessel_moment_decay_from j 0 a z.re ha hz
  rw [Real.norm_eq_abs,abs_of_nonneg (MaassKBessel.zero_moment_nonneg j z.re)] at hh
  exact (principalComplexMoment_norm_bound j r z (ha.trans_le hz)).trans hh

/-- Entire extension of the literal parity Fourier phase. -/
def complexEulerPhase (σ n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (((2*Real.pi*(n:ℝ):ℝ):ℂ)*Complex.I*z)+
    (-1:ℂ)^σ*Complex.exp (-(((2*Real.pi*(n:ℝ):ℝ):ℂ)*Complex.I*z))

theorem complexEulerPhase_differentiable (σ n : ℕ) : Differentiable ℂ (complexEulerPhase σ n) := by
  unfold complexEulerPhase
  fun_prop

theorem complexEulerPhase_ofReal (σ n : ℕ) (x : ℝ) :
    complexEulerPhase σ n (x:ℂ)=eulerParityPhase σ n x := by
  unfold complexEulerPhase eulerParityPhase
  have hh : (((2*Real.pi*(n:ℝ):ℝ):ℂ)*Complex.I*(x:ℂ))=
      (((2*Real.pi*(n:ℝ)*x:ℝ):ℂ)*Complex.I) := by push_cast; ring
  rw [hh]

theorem complexEulerPhase_norm_bound (σ n : ℕ) (z : ℂ) :
    ‖complexEulerPhase σ n z‖≤2*Real.exp ((2*Real.pi*(n:ℝ))*|z.im|) := by
  let v := 2*Real.pi*(n:ℝ)
  have hv : 0≤v := by dsimp [v]; positivity
  have hp : (((v:ℂ)*Complex.I*z)).re= -v*z.im := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,neg_zero,zero_mul,add_zero,zero_sub,neg_mul]
  have hn : (-((v:ℂ)*Complex.I*z)).re=v*z.im := by rw [Complex.neg_re,hp]; ring
  have h1 : Real.exp (-v*z.im)≤Real.exp (v*|z.im|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs z.im) hv]
  have h2 : Real.exp (v*z.im)≤Real.exp (v*|z.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self z.im) hv)
  change ‖Complex.exp ((v:ℂ)*Complex.I*z)+(-1:ℂ)^σ*Complex.exp (-((v:ℂ)*Complex.I*z))‖≤_
  calc
    _ ≤ ‖Complex.exp ((v:ℂ)*Complex.I*z)‖+‖(-1:ℂ)^σ*Complex.exp (-((v:ℂ)*Complex.I*z))‖ := norm_add_le _ _
    _ = Real.exp (-v*z.im)+Real.exp (v*z.im) := by
      rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,Complex.norm_exp,Complex.norm_exp,hp,hn]
    _ ≤ _ := by change _≤2*Real.exp (v*|z.im|); linarith

#print axioms principalComplexMoment_norm_bound
#print axioms principalComplexMoment_decay_from
#print axioms complexEulerPhase_differentiable
#print axioms complexEulerPhase_ofReal
#print axioms complexEulerPhase_norm_bound

end QuantitativeMaass
