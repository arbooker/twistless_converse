module

public import QuantitativeMaassEulerEvenAxisV1
public import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Literal horizontal derivative of one original Fourier--Bessel summand. -/
def principalEulerTermDx (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) (x y : ℝ) : ℂ :=
  (b (n+1)*(MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y):ℂ))*
    ((((2*Real.pi*((n+1:ℕ):ℝ):ℝ):ℂ)*Complex.I)*eulerParityPhase (σ+1) (n+1) x)

theorem principalEulerTerm_hasDerivAt_x (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) (x y : ℝ) :
    HasDerivAt (fun u => principalEulerTerm b r σ n (u,y)) (principalEulerTermDx b r σ n x y) x := by
  exact (eulerParityPhase_hasDerivAt σ (n+1) x).const_mul
    (b (n+1)*(MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y):ℂ))

theorem principalEulerTermDx_bound (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) (x y a : ℝ)
    (ha : 0<a) (hy : a≤y) :
    ‖principalEulerTermDx b r σ n x y‖≤(4*Real.pi)*principalMomentMajorant b 0 1 (2*Real.pi) a n := by
  have hω : ‖(((2*Real.pi*((n+1:ℕ):ℝ):ℝ):ℂ)*Complex.I)‖=2*Real.pi*((n+1:ℕ):ℝ) := by
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  unfold principalEulerTermDx
  rw [norm_mul,norm_mul,norm_mul,hω,Complex.norm_real,Real.norm_eq_abs]
  have hm := principalMomentMajorant_bound b 0 1 r (2*Real.pi) a (by positivity) ha n y hy
  simp only [pow_one,Real.norm_eq_abs] at hm
  calc
    _ ≤ (‖b (n+1)‖*|MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y)|)*
        ((2*Real.pi*((n+1:ℕ):ℝ))*2) := by
      gcongr
      exact eulerParityPhase_norm_le (σ+1) (n+1) x
    _ = (4*Real.pi)*(‖b (n+1)‖*((n+1:ℕ):ℝ)*|MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y)|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

/-- Horizontal termwise differentiation is justified by an explicit summable
majorant, not presumed from formal Fourier manipulations. -/
theorem principalEulerCore_hasDerivAt_x {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0<y) :
    HasDerivAt (fun u => principalEulerCore b r σ (u,y))
      (∑' n,principalEulerTermDx b r σ n x y) x := by
  apply hasDerivAt_tsum
    ((principalMomentMajorant_summable hb 0 1 (2*Real.pi) y (by positivity) hy).mul_left (4*Real.pi))
    (fun n u => principalEulerTerm_hasDerivAt_x b r σ n u y)
    (fun n u => principalEulerTermDx_bound b r σ n u y y hy le_rfl)
    (principalEulerTerm_summable hb r σ (0,y) hy)

theorem principalEulerWave_hasDerivAt_x {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0<y) :
    HasDerivAt (fun u => principalEulerWave b r σ (u,y))
      ((Real.sqrt y:ℂ)*(∑' n,principalEulerTermDx b r σ n x y)) x := by
  simpa only [principalEulerWave] using
    (principalEulerCore_hasDerivAt_x hb r σ x y hy).const_mul (Real.sqrt y:ℂ)

#print axioms principalEulerTerm_hasDerivAt_x
#print axioms principalEulerTermDx_bound
#print axioms principalEulerCore_hasDerivAt_x
#print axioms principalEulerWave_hasDerivAt_x

end QuantitativeMaass
