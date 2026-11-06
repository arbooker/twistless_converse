module
public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentySixWeightZeroChart

def firstCoefficient (x y a : ℂ) : ℂ :=
  2*a*y+a*x^2-y*x^2-2*y*x-2*y-2*x^4-2*x^3-3*x^2

def secondCoefficient (x y a : ℂ) : ℂ :=
  a^2+a*y-a*x-y*x-y-x-1

def obstruction {R : Type*} [CommRing R] (x y : R) : R :=
  4*x^8+6*x^7+6*x^6*y+14*x^6+8*x^5*y+8*x^5+6*x^4*y^2+
    18*x^4*y+8*x^4+4*x^3*y^2+8*x^3*y+2*x^2*y^3+8*x^2*y^2+8*x^2*y

theorem obstruction_identity (x y a : ℂ) :
    obstruction x y = (2*y+x^2)^2*secondCoefficient x y a-
      ((2*y+x^2)*a+(y-x)*(2*y+x^2)-
        (-y*x^2-2*y*x-2*y-2*x^4-2*x^3-3*x^2))*firstCoefficient x y a := by
  unfold obstruction firstCoefficient secondCoefficient
  ring

theorem obstruction_positive (x y : ℝ) (hx : 2≤x) (hy : 0≤y) :
    0<obstruction x y := by
  have hp : 0<x := by linarith
  unfold obstruction
  positivity

theorem obstruction_reflected_positive (x y : ℝ) (hx : 2≤x) (hy : 0≤y) :
    0<obstruction (-x) y := by
  have hp : 0<x := by linarith
  have h2 : 0<2*x-3 := by linarith
  have h3 : 0<3*x-4 := by linarith
  have h7 : 0<7*x-4 := by linarith
  have h32 : 0<3*x-2 := by linarith
  have h9 : 0<9*x-4 := by linarith
  have he : obstruction (-x) y =
      2*x^7*(2*x-3)+2*x^5*y*(3*x-4)+2*x^5*(7*x-4)+
      2*x^3*y^2*(3*x-2)+2*x^3*y*(9*x-4)+8*x^4+
      2*x^2*y^3+8*x^2*y^2+8*x^2*y := by unfold obstruction; ring
  rw [he]
  positivity

/-- The second projective chart is impossible for either sign of the
prime-two parameter at every positive integer exponent. The stronger
real inequalities stated here avoid an Abel certificate for this chart. -/
theorem no_zero_chart (x y : ℝ) (hx : 2≤x ∨ x≤ -2) (hy : 0≤y) (a : ℂ)
    (h1 : firstCoefficient x y a=0) (h2 : secondCoefficient x y a=0) : False := by
  have hz : obstruction (x:ℂ) (y:ℂ)=0 := by
    rw [obstruction_identity,h1,h2]
    ring
  have hr : obstruction x y=0 := by
    have hc : ((obstruction x y : ℝ):ℂ)=obstruction (x:ℂ) (y:ℂ) := by
      simp only [obstruction]
      push_cast
      rfl
    rw [←hc] at hz
    exact Complex.ofReal_eq_zero.mp hz
  have hp : 0<obstruction x y := by
    rcases hx with hx|hx
    · exact obstruction_positive x y hx hy
    · simpa using obstruction_reflected_positive (-x) y (by linarith) hy
  linarith

#print axioms obstruction_identity
#print axioms no_zero_chart
end SmallLevelTwentySixWeightZeroChart
