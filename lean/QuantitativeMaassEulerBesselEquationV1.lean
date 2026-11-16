module

public import QuantitativeMaassEulerPartialsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem principalWeightedTerm_bessel_equation (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ)
    (x y : ℝ) (hy : 0<y) :
    ((2*Real.pi:ℝ):ℂ)^2*(y:ℂ)^2*
        (principalWeightedTerm b r 2 2 σ n (x,y)-principalWeightedTerm b r 0 2 σ n (x,y))-
      ((2*Real.pi:ℝ):ℂ)*(y:ℂ)*principalWeightedTerm b r 1 1 σ n (x,y)+
      (r:ℂ)^2*principalWeightedTerm b r 0 0 σ n (x,y)=0 := by
  have hpos : 0<2*Real.pi*((n+1:ℕ):ℝ)*y := by positivity
  have hm := MaassKBessel.moment_ode r hpos
  rw [←MaassKBessel.moment_zero] at hm
  have hh := congrArg (fun u : ℝ => (u:ℂ)) hm
  push_cast at hh
  simp only [principalWeightedTerm,pow_zero,pow_one,mul_one]
  push_cast
  linear_combination (b (n+1)*eulerParityPhase σ (n+1) x)*hh

/-- Summing the literal Bessel ODE is justified by the already proved weighted
absolute convergence. This is the core PDE before the sqrt(y) rescaling. -/
theorem principalWeightedSeries_bessel_equation {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0<y) :
    ((2*Real.pi:ℝ):ℂ)^2*(y:ℂ)^2*
        (principalWeightedSeries b r 2 2 σ (x,y)-principalWeightedSeries b r 0 2 σ (x,y))-
      ((2*Real.pi:ℝ):ℂ)*(y:ℂ)*principalWeightedSeries b r 1 1 σ (x,y)+
      (r:ℂ)^2*principalEulerCore b r σ (x,y)=0 := by
  have h22 := (principalWeightedTerm_summable hb r 2 2 σ (x,y) hy).hasSum
  have h02 := (principalWeightedTerm_summable hb r 0 2 σ (x,y) hy).hasSum
  have h11 := (principalWeightedTerm_summable hb r 1 1 σ (x,y) hy).hasSum
  have h00 := (principalWeightedTerm_summable hb r 0 0 σ (x,y) hy).hasSum
  have hh := (((h22.sub h02).mul_left (((2*Real.pi:ℝ):ℂ)^2*(y:ℂ)^2)).sub
    (h11.mul_left (((2*Real.pi:ℝ):ℂ)*(y:ℂ)))).add (h00.mul_left ((r:ℂ)^2))
  have hzero : HasSum (fun _ : ℕ => (0:ℂ))
      (((2*Real.pi:ℝ):ℂ)^2*(y:ℂ)^2*
        (principalWeightedSeries b r 2 2 σ (x,y)-principalWeightedSeries b r 0 2 σ (x,y))-
      ((2*Real.pi:ℝ):ℂ)*(y:ℂ)*principalWeightedSeries b r 1 1 σ (x,y)+
      (r:ℂ)^2*principalWeightedSeries b r 0 0 σ (x,y)) := by
    convert! hh using 1
    · funext n
      exact (principalWeightedTerm_bessel_equation b r σ n x y hy).symm
  rw [principalWeightedSeries_zero] at hzero
  exact hzero.unique hasSum_zero

#print axioms principalWeightedTerm_bessel_equation
#print axioms principalWeightedSeries_bessel_equation

end QuantitativeMaass
