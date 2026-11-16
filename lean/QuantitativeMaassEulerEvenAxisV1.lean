module

public import QuantitativeMaassEulerFourierV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Physical height corresponding to the conductor-normalized Mellin coordinate. -/
def principalEulerHeight (L l : ℝ) : ℝ := Real.exp (l-Real.log L/2)

theorem principalEulerHeight_pos (L l : ℝ) : 0<principalEulerHeight L l := Real.exp_pos _

theorem principalEulerHeight_frequency (L l : ℝ) (n : ℕ) :
    Real.exp (l+MaassOriginal.frequencies L n)=((n+1:ℕ):ℝ)*principalEulerHeight L l := by
  unfold MaassOriginal.frequencies principalEulerHeight
  rw [show l+(Real.log (n+1)-Real.log L/2)=Real.log (n+1)+(l-Real.log L/2) by ring,
    Real.exp_add,Real.exp_log (by positivity : (0:ℝ)<n+1)]
  norm_cast

theorem principalEulerHeight_inverse (L : ℝ) (hL : 0<L) (l : ℝ) :
    principalEulerHeight L (-l)=1/(L*principalEulerHeight L l) := by
  apply (eq_div_iff (mul_pos hL (principalEulerHeight_pos L l)).ne').mpr
  unfold principalEulerHeight
  rw [mul_left_comm _ L,←Real.exp_add,
    show (-l-Real.log L/2)+(l-Real.log L/2)=-Real.log L by ring,
    Real.exp_neg,Real.exp_log hL]
  field_simp

theorem principalEulerHeight_sqrt_balance (L l : ℝ) :
    Real.sqrt (principalEulerHeight L l)*Real.exp (-l)=Real.sqrt (principalEulerHeight L (-l)) := by
  unfold principalEulerHeight
  rw [←Real.exp_half,←Real.exp_half,←Real.exp_add]
  congr 1
  ring

/-- The inverse Mellin series equals twice the actual even Fourier core on the axis. -/
theorem principalEuler_even_axisSum (L l r : ℝ) (b : ℕ → ℂ) :
    MaassOriginal.axisSum L (.principal r) 0 b l=
      2*principalEulerCore b r 0 (0,principalEulerHeight L l) := by
  unfold MaassOriginal.axisSum principalEulerCore
  rw [←tsum_mul_left]
  apply tsum_congr
  intro n
  rw [principalEulerHeight_frequency]
  simp only [MaassMellin.parityKernel,principalEulerTerm,eulerParityPhase,MaassSpectral.K,
    pow_zero,mul_zero,Complex.ofReal_zero,zero_mul,neg_zero,Complex.exp_zero,one_mul,
    MaassKBessel.moment_zero]
  rw [←mul_assoc (2*Real.pi) ((n+1:ℕ):ℝ) (principalEulerHeight L l)]
  ring

/-- The original untwisted continuation and individual growth give the actual
even Fourier--Bessel reflection on the imaginary axis. -/
theorem principalEulerWave_even_axis_inversion {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (ε : ℂ)
    (hε : ‖ε‖=1) (hcont : MaassOriginal.Continuation L (.principal r) 0 b ε) (l : ℝ) :
    principalEulerWave b r 0 (0,principalEulerHeight L l)=
      ε*principalEulerWave b r 0 (0,principalEulerHeight L (-l)) := by
  have hh := MaassOriginal.axis_inversion hL (.principal r) 0 hb hε hcont l
  rw [principalEuler_even_axisSum,principalEuler_even_axisSum] at hh
  have hs : (Real.sqrt (principalEulerHeight L l):ℂ)*(Real.exp (-l):ℂ)=
      (Real.sqrt (principalEulerHeight L (-l)):ℂ) := by
    rw [←Complex.ofReal_mul,principalEulerHeight_sqrt_balance]
  unfold principalEulerWave
  calc
    _ = ((Real.sqrt (principalEulerHeight L l):ℂ)/2)*
        (2*principalEulerCore b r 0 (0,principalEulerHeight L l)) := by ring
    _ = ((Real.sqrt (principalEulerHeight L l):ℂ)/2)*
        (ε*(Real.exp (-l):ℂ)*(2*principalEulerCore b r 0 (0,principalEulerHeight L (-l)))) := by rw [hh]
    _ = ε*((Real.sqrt (principalEulerHeight L l):ℂ)*(Real.exp (-l):ℂ))*
        principalEulerCore b r 0 (0,principalEulerHeight L (-l)) := by ring
    _ = _ := by rw [hs]; ring

#print axioms principalEulerHeight_pos
#print axioms principalEulerHeight_frequency
#print axioms principalEulerHeight_inverse
#print axioms principalEulerHeight_sqrt_balance
#print axioms principalEuler_even_axisSum
#print axioms principalEulerWave_even_axis_inversion

end QuantitativeMaass
