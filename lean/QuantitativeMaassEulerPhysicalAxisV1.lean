module

public import QuantitativeMaassFrickeCauchyV1
public import QuantitativeMaassEulerOddAxisV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem principalEulerHeight_log (L y : ℝ) (hy : 0<y) :
    principalEulerHeight L (Real.log y+Real.log L/2)=y := by
  unfold principalEulerHeight
  rw [add_sub_cancel_right,Real.exp_log hy]

theorem principalEulerWave_even_physical_axis {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (ε : ℂ)
    (hε : ‖ε‖=1) (hcont : MaassOriginal.Continuation L (.principal r) 0 b ε)
    (y : ℝ) (hy : 0<y) :
    principalEulerWave b r 0 (0,y)=ε*principalEulerWave b r 0 (0,1/(L*y)) := by
  have hh := principalEulerWave_even_axis_inversion hb L hL r ε hε hcont (Real.log y+Real.log L/2)
  rw [principalEulerHeight_inverse L hL,principalEulerHeight_log L y hy] at hh
  exact hh

theorem principalEulerOddAxis_physical_inversion {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (ε : ℂ)
    (hε : ‖ε‖=1) (hcont : MaassOriginal.Continuation L (.principal r) 1 b ε)
    (y : ℝ) (hy : 0<y) :
    principalEulerOddAxis b r y=ε*principalEulerOddAxis b r (1/(L*y)) := by
  have hh := principalEulerOddAxis_inversion hb L hL r ε hε hcont (Real.log y+Real.log L/2)
  rw [principalEulerHeight_inverse L hL,principalEulerHeight_log L y hy] at hh
  exact hh

/-- The odd functional equation gives the exact unnormalized normal derivative
relation, with the opposite sign to the Fricke normal-coordinate derivative. -/
theorem principalEulerWave_odd_physical_normal {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0<L) (r : ℝ) (ε : ℂ)
    (hε : ‖ε‖=1) (hcont : MaassOriginal.Continuation L (.principal r) 1 b ε)
    (y : ℝ) (hy : 0<y) :
    deriv (fun x => principalEulerWave b r 1 (x,y)) 0=
      ε*((1/(L*y^2):ℝ):ℂ)*deriv (fun x => principalEulerWave b r 1 (x,1/(L*y))) 0 := by
  have hh := principalEulerOddAxis_physical_inversion hb L hL r ε hε hcont y hy
  unfold principalEulerOddAxis at hh
  have hyc : (y:ℂ)≠0 := by exact_mod_cast hy.ne'
  have hLc : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have hpc : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  calc
    _ = ((2*Real.pi*Complex.I)/(y:ℂ))*
        ((y:ℂ)/(2*Real.pi*Complex.I)*deriv (fun x => principalEulerWave b r 1 (x,y)) 0) := by
      field_simp
    _ = ((2*Real.pi*Complex.I)/(y:ℂ))*
        (ε*((1/(L*y):ℝ):ℂ)/(2*Real.pi*Complex.I)*deriv (fun x => principalEulerWave b r 1 (x,1/(L*y))) 0) := by
      rw [hh]
      ring
    _ = _ := by
      push_cast
      field_simp

#print axioms principalEulerHeight_log
#print axioms principalEulerWave_even_physical_axis
#print axioms principalEulerOddAxis_physical_inversion
#print axioms principalEulerWave_odd_physical_normal

end QuantitativeMaass
