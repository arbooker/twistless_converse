module

public import QuantitativeMaassEulerHorizontalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- The odd Mellin datum is the physical normal derivative with its exact
archimedean normalization. -/
def principalEulerOddAxis (b : ℕ → ℂ) (r y : ℝ) : ℂ :=
  (y:ℂ)/(2*Real.pi*Complex.I)*deriv (fun x => principalEulerWave b r 1 (x,y)) 0

theorem principalEuler_odd_axisSum (L l r : ℝ) (b : ℕ → ℂ) :
    (Real.pi:ℂ)*Complex.I*MaassOriginal.axisSum L (.principal r) 1 b l=
      (principalEulerHeight L l:ℂ)*(∑' n,principalEulerTermDx b r 1 n 0 (principalEulerHeight L l)) := by
  unfold MaassOriginal.axisSum
  rw [←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro n
  rw [principalEulerHeight_frequency]
  simp [MaassMellin.parityKernel,principalEulerTermDx,eulerParityPhase,MaassSpectral.K,
    MaassKBessel.moment_zero,mul_assoc]
  ring

/-- Exact inverse-Mellin identification of the actual odd normal derivative. -/
theorem principalEulerOddAxis_eq_axisSum {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (L l r : ℝ) :
    principalEulerOddAxis b r (principalEulerHeight L l)=
      ((Real.sqrt (principalEulerHeight L l):ℂ)/2)*MaassOriginal.axisSum L (.principal r) 1 b l := by
  unfold principalEulerOddAxis
  rw [(principalEulerWave_hasDerivAt_x hb r 1 0 (principalEulerHeight L l) (principalEulerHeight_pos L l)).deriv]
  calc
    _ = ((Real.sqrt (principalEulerHeight L l):ℂ)/(2*Real.pi*Complex.I))*
        ((principalEulerHeight L l:ℂ)*(∑' n,principalEulerTermDx b r 1 n 0 (principalEulerHeight L l))) := by ring
    _ = _ := by
      rw [←principalEuler_odd_axisSum]
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The original odd functional equation supplies the correct normalized
normal-derivative reflection, independently of modularity. -/
theorem principalEulerOddAxis_inversion {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (ε : ℂ)
    (hε : ‖ε‖=1) (hcont : MaassOriginal.Continuation L (.principal r) 1 b ε) (l : ℝ) :
    principalEulerOddAxis b r (principalEulerHeight L l)=
      ε*principalEulerOddAxis b r (principalEulerHeight L (-l)) := by
  rw [principalEulerOddAxis_eq_axisSum hb,principalEulerOddAxis_eq_axisSum hb,
    MaassOriginal.axis_inversion hL (.principal r) 1 hb hε hcont l]
  have hs : (Real.sqrt (principalEulerHeight L l):ℂ)*(Real.exp (-l):ℂ)=
      (Real.sqrt (principalEulerHeight L (-l)):ℂ) := by
    rw [←Complex.ofReal_mul,principalEulerHeight_sqrt_balance]
  calc
    _ = (ε/2)*((Real.sqrt (principalEulerHeight L l):ℂ)*(Real.exp (-l):ℂ))*
        MaassOriginal.axisSum L (.principal r) 1 b (-l) := by ring
    _ = _ := by rw [hs]; ring

theorem principalEulerWave_odd_axis_zero (b : ℕ → ℂ) (r y : ℝ) :
    principalEulerWave b r 1 (0,y)=0 := by
  simp [principalEulerWave,principalEulerCore,principalEulerTerm,eulerParityPhase]

theorem principalEulerWave_even_normal_zero {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r y : ℝ) (hy : 0<y) : deriv (fun x => principalEulerWave b r 0 (x,y)) 0=0 := by
  rw [(principalEulerWave_hasDerivAt_x hb r 0 0 y hy).deriv]
  simp [principalEulerTermDx,eulerParityPhase]

#print axioms principalEuler_odd_axisSum
#print axioms principalEulerOddAxis_eq_axisSum
#print axioms principalEulerOddAxis_inversion
#print axioms principalEulerWave_odd_axis_zero
#print axioms principalEulerWave_even_normal_zero

end QuantitativeMaass
