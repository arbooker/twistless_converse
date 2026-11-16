module

public import QuantitativeMaassEulerSmoothV1
public import MaassKBesselODEV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem principalWeightedSeries_hasDerivAt_x {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (j k σ : ℕ) (x y : ℝ) (hy : 0<y) :
    HasDerivAt (fun u => principalWeightedSeries b r j k σ (u,y))
      (((2*Real.pi:ℝ):ℂ)*Complex.I*principalWeightedSeries b r j (k+1) (σ+1) (x,y)) x := by
  have hh : HasDerivAt (fun u => principalWeightedSeries b r j k σ (u,y)) _ x :=
    (principalWeightedSeries_hasFDerivAt hb r j k σ (x,y) hy).comp_hasDerivAt (l:=principalWeightedSeries b r j k σ) x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  simpa [eulerGradient] using hh

theorem principalWeightedSeries_hasDerivAt_y {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (j k σ : ℕ) (x y : ℝ) (hy : 0<y) :
    HasDerivAt (fun u => principalWeightedSeries b r j k σ (x,u))
      (-((2*Real.pi:ℝ):ℂ)*principalWeightedSeries b r (j+1) (k+1) σ (x,y)) y := by
  have hh : HasDerivAt (fun u => principalWeightedSeries b r j k σ (x,u)) _ y :=
    (principalWeightedSeries_hasFDerivAt hb r j k σ (x,y) hy).comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  simpa [eulerGradient] using hh

theorem principalWeightedSeries_add_two (b : ℕ → ℂ) (r : ℝ) (j k σ : ℕ) (z : ℝ × ℝ) :
    principalWeightedSeries b r j k (σ+2) z=principalWeightedSeries b r j k σ z := by
  unfold principalWeightedSeries
  apply tsum_congr
  intro n
  simp only [principalWeightedTerm,eulerParityPhase_add_two]

/-- Second horizontal derivative of the actual core; differentiation is
justified at every stage by the preceding joint-series theorem. -/
theorem principalEulerCore_second_x {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0<y) :
    deriv (deriv (fun u => principalEulerCore b r σ (u,y))) x =
      -((2*Real.pi:ℝ):ℂ)^2*principalWeightedSeries b r 0 2 σ (x,y) := by
  have hfirst : deriv (fun u => principalEulerCore b r σ (u,y))=
      fun u => ((2*Real.pi:ℝ):ℂ)*Complex.I*principalWeightedSeries b r 0 1 (σ+1) (u,y) := by
    funext u
    rw [←principalWeightedSeries_zero]
    exact (principalWeightedSeries_hasDerivAt_x hb r 0 0 σ u y hy).deriv
  rw [hfirst]
  have hh := (principalWeightedSeries_hasDerivAt_x hb r 0 1 (σ+1) x y hy).const_mul
    (((2*Real.pi:ℝ):ℂ)*Complex.I)
  rw [hh.deriv]
  simp only [Nat.add_assoc,one_add_one_eq_two,principalWeightedSeries_add_two]
  calc
    _ = -((2*Real.pi:ℝ):ℂ)^2*principalWeightedSeries b r 0 2 σ (x,y) := by
      linear_combination (((2*Real.pi:ℝ):ℂ)^2*principalWeightedSeries b r 0 2 σ (x,y))*Complex.I_sq

/-- The vertical derivative is represented by the next literal Bessel moment. -/
theorem principalEulerCore_first_y {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℝ) (hy : 0<y) :
    HasDerivAt (fun u => principalEulerCore b r σ (x,u))
      (-((2*Real.pi:ℝ):ℂ)*principalWeightedSeries b r 1 1 σ (x,y)) y := by
  rw [←principalWeightedSeries_zero]
  exact principalWeightedSeries_hasDerivAt_y hb r 0 0 σ x y hy

#print axioms principalWeightedSeries_hasDerivAt_x
#print axioms principalWeightedSeries_hasDerivAt_y
#print axioms principalWeightedSeries_add_two
#print axioms principalEulerCore_second_x
#print axioms principalEulerCore_first_y

end QuantitativeMaass
