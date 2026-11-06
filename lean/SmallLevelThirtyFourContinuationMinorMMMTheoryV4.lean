module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import SmallLevelFourPrimeRatesV1

/-! Consolidated chapter: SmallLevelThirtyFourContinuationMinorMMM. Original declarations and local scopes are retained. -/

/-! ## SmallLevelThirtyFourContinuationMinorMMMDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourContinuationMinorMMM
open Complex Matrix SmallLevelFourPrimeRates SmallLevelPrimeRates
def powers : Fin 167→ℤ×ℤ×ℤ×ℤ :=
  ![(0,0,0,0),(1,0,0,0),(0,1,0,0),(2,0,0,0),(1,1,0,0),(3,0,0,0),(2,1,0,0),(4,0,0,0),(0,0,1,0),(1,2,0,0),(2,0,0,1),(0,3,0,0),(5,0,0,0),(1,0,1,0),(2,2,0,0),(3,0,0,1),(4,1,0,0),(1,0,0,2),(0,1,1,0),(1,3,0,0),(6,0,0,0),(2,0,1,0),(3,2,0,0),(4,0,0,1),(0,4,0,0),(5,1,0,0),(2,0,0,2),(1,1,1,0),(2,3,0,0),(7,0,0,0),(3,0,1,0),(4,2,0,0),(5,0,0,1),(1,4,0,0),(6,1,0,0),(3,0,0,2),(2,1,1,0),(3,3,0,0),(4,1,0,1),(8,0,0,0),(4,0,1,0),(5,2,0,0),(2,1,0,2),(1,2,1,0),(6,0,0,1),(2,4,0,0),(2,0,1,1),(7,1,0,0),(4,0,0,2),(4,3,0,0),(0,3,1,0),(9,0,0,0),(5,0,1,0),(6,2,0,0),(3,1,0,2),(2,2,1,0),(3,4,0,0),(3,0,1,1),(4,2,0,1),(8,1,0,0),(1,0,1,2),(5,3,0,0),(2,2,0,2),(1,3,1,0),(6,1,0,1),(6,0,1,0),(7,2,0,0),(2,0,2,0),(4,1,0,2),(3,2,1,0),(4,4,0,0),(4,0,1,1),(0,4,1,0),(6,0,0,2),(5,1,1,0),(2,0,1,2),(6,3,0,0),(3,2,0,2),(2,3,1,0),(3,5,0,0),(7,0,1,0),(8,2,0,0),(5,1,0,2),(4,2,1,0),(5,4,0,0),(5,0,1,1),(1,4,1,0),(6,2,0,1),(7,0,0,2),(6,1,1,0),(3,0,1,2),(7,3,0,0),(2,1,2,0),(4,2,0,2),(3,3,1,0),(4,5,0,0),(4,1,1,1),(8,0,1,0),(9,2,0,0),(4,0,2,0),(6,1,0,2),(5,2,1,0),(2,1,1,2),(6,4,0,0),(6,0,1,1),(2,4,1,0),(7,1,1,0),(4,0,1,2),(8,3,0,0),(5,2,0,2),(4,3,1,0),(5,5,0,0),(9,0,1,0),(10,2,0,0),(7,1,0,2),(6,2,1,0),(3,1,1,2),(2,2,2,0),(3,4,1,0),(4,6,0,0),(4,2,1,1),(8,1,1,0),(9,3,0,0),(4,1,2,0),(6,2,0,2),(5,3,1,0),(2,2,1,2),(6,5,0,0),(6,1,1,1),(7,2,1,0),(4,1,1,2),(8,4,0,0),(4,4,1,0),(6,0,1,2),(10,3,0,0),(7,2,0,2),(6,3,1,0),(3,2,1,2),(3,5,1,0),(8,2,1,0),(5,1,1,2),(4,2,2,0),(5,4,1,0),(6,6,0,0),(6,2,1,1),(7,0,1,2),(7,3,1,0),(4,2,1,2),(4,5,1,0),(9,2,1,0),(6,1,1,2),(10,4,0,0),(6,4,1,0),(8,3,1,0),(5,2,1,2),(5,5,1,0),(10,2,1,0),(7,1,1,2),(4,6,1,0),(9,3,1,0),(6,2,1,2),(6,5,1,0),(8,4,1,0),(10,3,1,0),(7,2,1,2),(6,6,1,0),(10,4,1,0)]

def rates : Fin 167→ℚ :=
  ![1,2,3,4,6,8,12,16,17,18,20,27,32,34,36,40,48,50,51,54,64,68,72,80,81,96,100,102,108,128,136,144,160,162,192,200,204,216,240,256,272,288,300,306,320,324,340,384,400,432,459,512,544,576,600,612,648,680,720,768,850,864,900,918,960,1088,1152,1156,1200,1224,1296,1360,1377,1600,1632,1700,1728,1800,1836,1944,2176,2304,2400,2448,2592,2720,2754,2880,3200,3264,3400,3456,3468,3600,3672,3888,4080,4352,4608,4624,4800,4896,5100,5184,5440,5508,6528,6800,6912,7200,7344,7776,8704,9216,9600,9792,10200,10404,11016,11664,12240,13056,13824,13872,14400,14688,15300,15552,16320,19584,20400,20736,22032,27200,27648,28800,29376,30600,33048,39168,40800,41616,44064,46656,48960,54400,58752,61200,66096,78336,81600,82944,88128,117504,122400,132192,156672,163200,198288,235008,244800,264384,352512,470016,489600,793152,1410048]

def coefficients (a b : ℂ) : Fin 167→ℂ :=
  ![(((-1))),(((-2))),(((-1)*a)),(((-7))),(((-2)*a)),(((-3))),(((-3)*a)),((8)),(((1)/(2))),((9) + ((-2)*a^2)),(((-2)*b)),(((-1)*a)),((7)),((1)),((12) + ((-4)*a^2)),(((-2)*b)),((2*a)),((2)),(((1*a)/(2))),(((-3)*a)),(((-1))),(((5)/(2))),(((-5)) + (1*a^2)),((1*b)),(((-1))),((3*a)),((2)),((1*a)),(((-3)*a)),(((-3))),(((3)/(2))),(((-12)) + (2*a^2)),((2*b)),(((-1))),((1*a)),(((-3))),(((1*a)/(2))),((2*a)),(((-1)*a*b)),((1)),(((-3))),(((-6)) + (2*a^2)),((2*a)),((((-9))/(2)) + (1*a^2)),((1*b)),((3)),((1*b)),(((-1)*a)),(((-5))),((4*a)),(((1*a)/(2))),((1)),((((-7))/(2))),((2*a^2)),((1*a)),(((-7)) + (2*a^2)),((4) + ((-1)*a^2)),((1*b)),(((-1)*b)),((1*a)),(((-1))),((2*a)),((2)),(((3*a)/(2))),((1*a*b)),(((1)/(2))),((5) + ((-2)*a^2)),(((1)/(2))),(((-3)*a)),(((5)/(2)) + (((-1)*a^2)/(2))),((1)),((((-1)*b)/(2))),(((1)/(2))),((3)),((((-3)*a)/(2))),(((-1))),(((-1)*a)),((1)),(((3*a)/(2))),(((-1)*a)),(((3)/(2))),((1)),(((-2)*a)),((7) + ((-1)*a^2)),(((-3)) + (1*a^2)),(((-1)*b)),(((1)/(2))),((1*b)),((1)),((((-1)*a)/(2))),(((3)/(2))),(((-2)*a)),(((1*a)/(2))),(((-3))),(((-1)*a)),((1*a)),(((1*a*b)/(2))),((((-1))/(2))),(((-3)) + (1*a^2)),((((-1))/(2))),((1*a)),((3) + ((-1)*a^2)),(((-1)*a)),(((-4))),((((-1)*b)/(2))),((((-3))/(2))),(((1*a)/(2))),(((5)/(2))),((2*a)),(((-2))),(((-2)*a)),((1*a)),((((-1))/(2))),(((-1))),((1*a)),(((-1)*a^2)),((((-1)*a)/(2))),(((1)/(2))),(((-2)) + ((1*a^2)/(2))),((1)),(((1*b)/(2))),((((-1)*a)/(2))),((1*a)),((((-1)*a)/(2))),((1)),(((-1)*a)),(((-1))),(((-1)*a)),((((-1)*a*b)/(2))),((((-5))/(2)) + (1*a^2)),(((3*a)/(2))),((2)),((((-1))/(2))),((((-3))/(2))),(((-1)*a)),((1)),(((1*a)/(2))),((((-1))/(2))),(((1*a)/(2))),((((-1))/(2))),((1*a)),((((-1))/(2))),(((3)/(2)) + (((-1)*a^2)/(2))),(((-1))),((((-1)*b)/(2))),((((-1))/(2))),((1*a)),(((3)/(2))),((((-1)*a)/(2))),(((3)/(2)) + (((-1)*a^2)/(2))),((((-1)*a)/(2))),(((-1))),((2)),(((-1)*a)),((1)),((((-1)*a)/(2))),(((1)/(2))),((((-1)*a)/(2))),((((-1))/(2))),((((-1)*a)/(2))),((((-1))/(2))),(((1*a)/(2))),(((-1))),(((1*a)/(2))),((((-1))/(2))),(((1)/(2))),(((1)/(2)))]

def minor (X Y Z W a b : ℂ) : ℂ :=
  ((-1)) + ((1*Z)/(2)) + ((-1)*Y*a) + ((1*Y*Z*a)/(2)) + ((-1)*Y^3*a) + ((1*Y^3*Z*a)/(2)) + ((-1)*Y^4) + ((1*Y^4*Z)/(2)) + ((-2)*X) + (2*X*W^2) + (1*X*Z) + ((-1)*X*Z*W^2) + ((-2)*X*Y*a) + (1*X*Y*Z*a) + (9*X*Y^2) + ((-2)*X*Y^2*a^2) + (((-9)*X*Y^2*Z)/(2)) + (1*X*Y^2*Z*a^2) + ((-3)*X*Y^3*a) + ((3*X*Y^3*Z*a)/(2)) + ((-1)*X*Y^4) + ((1*X*Y^4*Z)/(2)) + ((-7)*X^2) + ((-2)*X^2*W*b) + (2*X^2*W^2) + ((5*X^2*Z)/(2)) + (1*X^2*Z*W*b) + ((-1)*X^2*Z*W^2) + ((1*X^2*Z^2)/(2)) + ((-3)*X^2*Y*a) + (2*X^2*Y*W^2*a) + ((1*X^2*Y*Z*a)/(2)) + ((-1)*X^2*Y*Z*W^2*a) + ((1*X^2*Y*Z^2*a)/(2)) + (12*X^2*Y^2) + ((-4)*X^2*Y^2*a^2) + (2*X^2*Y^2*W^2) + ((-7)*X^2*Y^2*Z) + (2*X^2*Y^2*Z*a^2) + ((-1)*X^2*Y^2*Z*W^2) + ((1*X^2*Y^2*Z^2)/(2)) + ((-3)*X^2*Y^3*a) + ((3*X^2*Y^3*Z*a)/(2)) + (3*X^2*Y^4) + (((-3)*X^2*Y^4*Z)/(2)) + ((-3)*X^3) + ((-2)*X^3*W*b) + ((-3)*X^3*W^2) + ((3*X^3*Z)/(2)) + (1*X^3*Z*W*b) + ((3*X^3*Z*W^2)/(2)) + (1*X^3*Y*W^2*a) + (((-1)*X^3*Y*Z*W^2*a)/(2)) + ((-5)*X^3*Y^2) + (1*X^3*Y^2*a^2) + (1*X^3*Y^2*W^2) + ((5*X^3*Y^2*Z)/(2)) + (((-1)*X^3*Y^2*Z*a^2)/(2)) + (((-1)*X^3*Y^2*Z*W^2)/(2)) + (2*X^3*Y^3*a) + ((-1)*X^3*Y^3*Z*a) + (4*X^3*Y^4) + ((-1)*X^3*Y^4*a^2) + ((-2)*X^3*Y^4*Z) + ((1*X^3*Y^4*Z*a^2)/(2)) + ((-1)*X^3*Y^5*a) + ((1*X^3*Y^5*Z*a)/(2)) + (8*X^4) + (1*X^4*W*b) + ((-5)*X^4*W^2) + ((-3)*X^4*Z) + (((-1)*X^4*Z*W*b)/(2)) + ((5*X^4*Z*W^2)/(2)) + (((-1)*X^4*Z^2)/(2)) + (2*X^4*Y*a) + ((-1)*X^4*Y*W*a*b) + ((-3)*X^4*Y*W^2*a) + ((1*X^4*Y*Z*W*a*b)/(2)) + ((3*X^4*Y*Z*W^2*a)/(2)) + (((-1)*X^4*Y*Z^2*a)/(2)) + ((-12)*X^4*Y^2) + (2*X^4*Y^2*a^2) + ((-1)*X^4*Y^2*W*b) + ((-3)*X^4*Y^2*W^2) + (7*X^4*Y^2*Z) + ((-1)*X^4*Y^2*Z*a^2) + ((1*X^4*Y^2*Z*W*b)/(2)) + ((3*X^4*Y^2*Z*W^2)/(2)) + (((-1)*X^4*Y^2*Z^2)/(2)) + (4*X^4*Y^3*a) + ((-2)*X^4*Y^3*Z*a) + (1*X^4*Y^4) + (((-1)*X^4*Y^4*Z)/(2)) + (1*X^4*Y^5*a) + (((-1)*X^4*Y^5*Z*a)/(2)) + (1*X^4*Y^6) + (((-1)*X^4*Y^6*Z)/(2)) + (7*X^5) + (2*X^5*W*b) + (((-7)*X^5*Z)/(2)) + ((-1)*X^5*Z*W*b) + (3*X^5*Y*a) + ((-2)*X^5*Y*W^2*a) + (((-3)*X^5*Y*Z*a)/(2)) + (1*X^5*Y*Z*W^2*a) + ((-6)*X^5*Y^2) + (2*X^5*Y^2*a^2) + ((-2)*X^5*Y^2*W^2) + (3*X^5*Y^2*Z) + ((-1)*X^5*Y^2*Z*a^2) + (1*X^5*Y^2*Z*W^2) + (2*X^5*Y^3*a) + ((-1)*X^5*Y^3*Z*a) + ((-3)*X^5*Y^4) + (1*X^5*Y^4*a^2) + ((3*X^5*Y^4*Z)/(2)) + (((-1)*X^5*Y^4*Z*a^2)/(2)) + (1*X^5*Y^5*a) + (((-1)*X^5*Y^5*Z*a)/(2)) + ((-1)*X^6) + (1*X^6*W*b) + (3*X^6*W^2) + ((1*X^6*Z)/(2)) + (((-1)*X^6*Z*W*b)/(2)) + (((-3)*X^6*Z*W^2)/(2)) + (1*X^6*Y*a) + (1*X^6*Y*W*a*b) + (1*X^6*Y*W^2*a) + (((-1)*X^6*Y*Z*a)/(2)) + (((-1)*X^6*Y*Z*W*a*b)/(2)) + (((-1)*X^6*Y*Z*W^2*a)/(2)) + (2*X^6*Y^2*a^2) + (1*X^6*Y^2*W*b) + (1*X^6*Y^2*W^2) + ((-1)*X^6*Y^2*Z*a^2) + (((-1)*X^6*Y^2*Z*W*b)/(2)) + (((-1)*X^6*Y^2*Z*W^2)/(2)) + ((-1)*X^6*Y^3*a) + ((1*X^6*Y^3*Z*a)/(2)) + ((-4)*X^6*Y^4) + (2*X^6*Y^4*Z) + ((-1)*X^6*Y^5*a) + ((1*X^6*Y^5*Z*a)/(2)) + ((-1)*X^6*Y^6) + ((1*X^6*Y^6*Z)/(2)) + ((-3)*X^7) + (1*X^7*W^2) + ((3*X^7*Z)/(2)) + (((-1)*X^7*Z*W^2)/(2)) + ((-1)*X^7*Y*a) + (1*X^7*Y*W^2*a) + ((1*X^7*Y*Z*a)/(2)) + (((-1)*X^7*Y*Z*W^2*a)/(2)) + (5*X^7*Y^2) + ((-2)*X^7*Y^2*a^2) + (1*X^7*Y^2*W^2) + (((-5)*X^7*Y^2*Z)/(2)) + (1*X^7*Y^2*Z*a^2) + (((-1)*X^7*Y^2*Z*W^2)/(2)) + ((-2)*X^7*Y^3*a) + (1*X^7*Y^3*Z*a) + (1*X^8) + (((-1)*X^8*Z)/(2)) + (1*X^8*Y*a) + (((-1)*X^8*Y*Z*a)/(2)) + (1*X^8*Y^2) + (((-1)*X^8*Y^2*Z)/(2)) + (2*X^8*Y^3*a) + ((-1)*X^8*Y^3*Z*a) + (2*X^8*Y^4) + ((-1)*X^8*Y^4*Z) + (1*X^9) + (((-1)*X^9*Z)/(2)) + ((-3)*X^9*Y^2) + (1*X^9*Y^2*a^2) + ((3*X^9*Y^2*Z)/(2)) + (((-1)*X^9*Y^2*Z*a^2)/(2)) + (1*X^9*Y^3*a) + (((-1)*X^9*Y^3*Z*a)/(2)) + ((-1)*X^10*Y^2) + ((1*X^10*Y^2*Z)/(2)) + ((-1)*X^10*Y^3*a) + ((1*X^10*Y^3*Z*a)/(2)) + ((-1)*X^10*Y^4) + ((1*X^10*Y^4*Z)/(2))

def residualMatrix (X Y Z W a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)),((1)/(X)) + ((2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)),(((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2));
    0,(((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)),((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + (((-1)*X^2*Z)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2));
    (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)),((1)/(X^2)) + ((4)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((5)/(W^2)) + (((-1)*b)/(W)) + ((-2)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)),(((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + (((-3))/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((4*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-8)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((1*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((2*X*Y^2)/(W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + (((-10)*X^2)/(W^2)) + ((3*X^2)/(2)) + ((3*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-11)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-2)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-9)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^3*a)/(W^2))]

end SmallLevelThirtyFourContinuationMinorMMM
end
end

/-! ## SmallLevelThirtyFourContinuationMinorMMMRatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourContinuationMinorMMM
open Complex Matrix SmallLevelFourPrimeRates SmallLevelPrimeRates
theorem rates_injective : Function.Injective rates := by
  have hs : StrictMono rates := Fin.strictMono_iff_lt_succ.mpr (by decide +kernel)
  exact hs.injective

theorem rates_factor (i : Fin 167) :
    rates i=(2:ℚ)^(powers i).1*(3:ℚ)^(powers i).2.1*
      (17:ℚ)^(powers i).2.2.1*(5:ℚ)^(powers i).2.2.2 := by
  revert i
  decide +kernel

theorem sum_curve (c : Fin 167→ℂ) (m : ℕ) (s : ℂ) :
    (∑ i,c i*(rates i:ℂ)^(s-(m:ℂ)))=
      ∑ i,c i*SmallLevelFourPrimeRates.monomial (powers i)
        (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [rational_power 2 3 17 5 (by decide) (by decide) (by decide) (by decide) _ _ (rates_factor i)]
  rfl

#print axioms rates_injective
#print axioms rates_factor
#print axioms sum_curve

end SmallLevelThirtyFourContinuationMinorMMM
end
end

/-! ## SmallLevelThirtyFourContinuationMinorMMMNonzeroV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourContinuationMinorMMM
open Complex Matrix SmallLevelFourPrimeRates SmallLevelPrimeRates
theorem minor_sum (X Y Z W a b : ℂ) :
    (∑ i,coefficients a b i*SmallLevelFourPrimeRates.monomial (powers i) X Y Z W)=minor X Y Z W a b := by
  norm_num [Fin.sum_univ_succ,coefficients,powers,SmallLevelFourPrimeRates.monomial,minor] <;> ring

theorem minor_nonzero_on_curve (a b : ℂ) (m : ℕ) :
    ∃ s : ℂ,minor (parameter 2 m s) (parameter 3 m s) (parameter 17 m s) (parameter 5 m s) a b≠0 := by
  obtain ⟨s,hs⟩:=exponential_sum_nonzero rates rates_injective (coefficients a b) 0 (by norm_num [coefficients]) m
  refine ⟨s,?_⟩
  rw [sum_curve,minor_sum] at hs
  exact hs

#print axioms minor_sum
#print axioms minor_nonzero_on_curve

end SmallLevelThirtyFourContinuationMinorMMM
end
end

/-! ## SmallLevelThirtyFourContinuationMinorMMMV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourContinuationMinorMMM
open Complex Matrix SmallLevelFourPrimeRates SmallLevelPrimeRates
theorem minor_determinant (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) :
    minor X Y Z W a b = X^3*W^4 * (residualMatrix X Y Z W a b).det := by
  norm_num [minor,residualMatrix,Matrix.det_fin_three]
  field_simp [hX,hY,hZ,hW]
  ring

#print axioms minor_determinant

end SmallLevelThirtyFourContinuationMinorMMM
end
end
