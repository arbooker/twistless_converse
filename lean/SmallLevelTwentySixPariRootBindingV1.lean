module
public import SmallLevelTwentySixPariIdentityFamilyV4
public import SmallLevelTwentySixPariFirstChartTheoryV4
public import SmallLevelTwentySixRootTheoryV4
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariRootBinding
open SmallLevelTwentySixPariIdentity041 SmallLevelTwentySixRoot
open SmallLevelPolynomialCoefficientCertificate QuantitativeArithmeticComplexHornerBounds

theorem low_curve_binding (x y z w a b u : ℂ) :
    p0 x y z w a b u = SmallLevelTwentySixPariFirstChart.lowCurve x y z w a b u := by
  norm_num [p0, coefficients0, c0_0, c0_1, c0_2, c0_3, evaluate,
    SmallLevelTwentySixPariFirstChart.lowCurve, SmallLevelTwentySixPariIdentity007.p1]
  ring

/-- The modulus in the lifted PARI identity is the already verified root polynomial. -/
theorem modulus_binding (x y z w a b u : ℂ) :
    p5 x y z w a b u = 42507 * p21.eval x := by
  norm_num [p5, coefficients5, c5_0, evaluate, p21,
    eval_hornerPolynomial, hornerValue, pCoefficient]
  ring

/-- The Bezout remainder is exactly the previously certified interpolation relation. -/
theorem remainder_binding (x y z w a b u : ℂ) :
    p4 x y z w a b u = y - q20.eval x := by
  norm_num [p4, coefficients4, c4_0, c4_1, evaluate, q20,
    eval_hornerPolynomial, hornerValue, qCoefficient]
  ring

/-- This conditional endpoint does not assert that the original source equations
imply its three polynomial premises. Those implications are separate obligations. -/
theorem root_relation (x y z w a b u : ℂ)
    (h0 : p0 x y z w a b u = 0) (h2 : p2 x y z w a b u = 0)
    (h5 : p5 x y z w a b u = 0) :
    p21.eval x = 0 ∧ q20.eval x = y := by
  have hi := identity x y z w a b u
  rw [h0,h2,h5] at hi
  have h4 : p4 x y z w a b u = 0 := by simpa using hi.symm
  rw [modulus_binding] at h5
  rw [remainder_binding] at h4
  constructor
  · exact (mul_eq_zero.mp h5).resolve_left (by norm_num)
  · exact (sub_eq_zero.mp h4).symm

theorem physical_exclusion (h z w a b u : ℂ)
    (h0 : p0 ((2:ℂ)^h) ((9:ℂ)^h) z w a b u = 0)
    (h2 : p2 ((2:ℂ)^h) ((9:ℂ)^h) z w a b u = 0)
    (h5 : p5 ((2:ℂ)^h) ((9:ℂ)^h) z w a b u = 0) : False := by
  obtain ⟨hp,hq⟩ := root_relation _ _ _ _ _ _ _ h0 h2 h5
  exact no_physical_locus h hp hq

theorem reflected_physical_exclusion (h z w a b u : ℂ)
    (h0 : p0 (-((2:ℂ)^h)) ((9:ℂ)^h) z w a b u = 0)
    (h2 : p2 (-((2:ℂ)^h)) ((9:ℂ)^h) z w a b u = 0)
    (h5 : p5 (-((2:ℂ)^h)) ((9:ℂ)^h) z w a b u = 0) : False := by
  obtain ⟨hp,hq⟩ := root_relation _ _ _ _ _ _ _ h0 h2 h5
  exact no_physical_locus_reflected h hp hq

#print axioms low_curve_binding
#print axioms modulus_binding
#print axioms remainder_binding
#print axioms root_relation
#print axioms physical_exclusion
#print axioms reflected_physical_exclusion
end SmallLevelTwentySixPariRootBinding
