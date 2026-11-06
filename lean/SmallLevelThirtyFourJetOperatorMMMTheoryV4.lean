module

public import SmallLevelThirtyFourUnitMMMInhomogeneousTheoryV4

/-! Consolidated chapter: SmallLevelThirtyFourJetOperatorMMM. Original declarations and local scopes are retained. -/

/-! ## SmallLevelThirtyFourJetOperatorMMMDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourJetOperatorMMM
open Complex SmallLevelThirtyFourUnitMMMInhomogeneous
def initialValues (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : Fin 546→ℂ
  | 1 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 2 => (0)*v 0 + (0)*v 1 + ((((-1020))/(W^2)))*v 2
  | 3 => (0)*v 0 + ((((-1020)*X)/(Y^2*W^2)))*v 1 + (0)*v 2
  | 4 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 6 => (0)*v 0 + (0)*v 1 + (((238)/(5)))*v 2
  | 7 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 8 => (0)*v 0 + (((1785)/(Y^2*W^2)))*v 1 + ((((-1785)*X^2)/(Y^2*W^2)) + (((-1785)*X^3)/(2*Y^2*W^2)) + (((-1785)*X^3*a)/(2*Y*W^2)) + (((-1785)*X^3)/(2*W^2)))*v 2
  | 9 => (0)*v 0 + (0)*v 1 + (((1190)/(3*W^2)))*v 2
  | 10 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 12 => (0)*v 0 + (0)*v 1 + (((1173*X)/(5*Y^2)))*v 2
  | 14 => (0)*v 0 + (0)*v 1 + (((170)/(3)))*v 2
  | 15 => (0)*v 0 + ((((-85)*Y^2)/(W^2)))*v 1 + (((85*X)/(2*W^2)) + ((85*X*Y*a)/(2*W^2)) + (((-85)*X*Y^2)/(2*W^2)) + ((85*X^2)/(W^2)) + ((85*X^2*Y*a)/(2*W^2)) + ((85*X^2*Y^2*a^2)/(2*W^2)) + ((85*X^2*Y^3*a)/(2*W^2)))*v 2
  | 16 => (0)*v 0 + ((((-170))/(X*W^2)))*v 1 + (((170*X)/(W^2)))*v 2
  | 18 => (0)*v 0 + (0)*v 1 + ((((-255))/(Y^2*W^2)) + (((-255)*a)/(Y*W^2)) + (((-255))/(W^2)))*v 2
  | 19 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 21 => (0)*v 0 + (0)*v 1 + (((170)/(W^2)))*v 2
  | 22 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 23 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 24 => (0)*v 0 + (0)*v 1 + ((((-85)*X*Z)/(3*W^2)))*v 2
  | 25 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 26 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 27 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 29 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 30 => (0)*v 0 + (0)*v 1 + ((((-544))/(15)))*v 2
  | 32 => (0)*v 0 + (((1530)/(Y^2*W^2)))*v 1 + ((((-1530)*X^2)/(Y^2*W^2)))*v 2
  | 33 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 37 => (0)*v 0 + (0)*v 1 + (((17*X)/(5)))*v 2
  | 38 => (0)*v 0 + ((((-34))/(15)))*v 1 + (0)*v 2
  | 39 => (0)*v 0 + (0)*v 1 + ((((-17)*X)/(15)) + (((-17)*X^2)/(30)) + (((-17)*X^2*Y*a)/(30)) + (((-17)*X^2*Y^2)/(30)))*v 2
  | 40 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 42 => (0)*v 0 + (0)*v 1 + (((102)/(5*Y^2)) + ((51*X)/(5*Y^2)) + ((51*X*a)/(5*Y)) + ((51*X)/(5)))*v 2
  | 43 => (0)*v 0 + (0)*v 1 + ((((-51)*X)/(Y^2)))*v 2
  | 44 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 45 => (0)*v 0 + (0)*v 1 + (((255*X)/(W^2)))*v 2
  | 47 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 49 => (0)*v 0 + ((((-255))/(Y^2*W^2)))*v 1 + (0)*v 2
  | 51 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 52 => (0)*v 0 + (((51)/(5*Y^2)))*v 1 + ((((-51)*X^2)/(5*Y^2)))*v 2
  | 53 => (0)*v 0 + (((34)/(3*X)))*v 1 + ((((-34)*X)/(3)) + (((-17)*X^2)/(3)) + (((-17)*X^2*Y*a)/(3)) + (((-17)*X^2*Y^2)/(3)))*v 2
  | 54 => (0)*v 0 + ((((-102))/(5*X*Y^2)) + ((102*a)/(5*X*Y)) + (((-102))/(5*X)))*v 1 + ((((-102))/(5*Y^2)) + (((-102)*X*a)/(5*Y)))*v 2
  | 55 => (0)*v 0 + (((85)/(3*W^2)) + (((-85)*Y*a)/(3*W^2)) + ((85*Y^2)/(3*W^2)))*v 1 + (((85*X)/(3*W^2)) + ((85*X^2*Y*a)/(3*W^2)))*v 2
  | 56 => (0)*v 0 + (0)*v 1 + ((34))*v 2
  | 57 => (0)*v 0 + ((((-51))/(Y^2)))*v 1 + (((51*X^2)/(Y^2)) + ((51*X^3)/(2*Y^2)) + ((51*X^3*a)/(2*Y)) + ((51*X^3)/(2)))*v 2
  | 58 => (0)*v 0 + ((((-170))/(3*X*W^2)))*v 1 + (((170*X)/(3*W^2)))*v 2
  | 59 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 62 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 63 => (0)*v 0 + (0)*v 1 + ((((-51))/(Y^2)) + (((-51)*a)/(Y)) + ((-51)))*v 2
  | 66 => (0)*v 0 + (((51*X)/(Y^2)))*v 1 + (0)*v 2
  | 67 => (0)*v 0 + (((34)/(X)))*v 1 + (0)*v 2
  | 70 => (0)*v 0 + (((-17)))*v 1 + (0)*v 2
  | 72 => (0)*v 0 + (0)*v 1 + (((17)/(5)) + ((17*Y*a)/(5)) + ((17*Y^2)/(5)))*v 2
  | 73 => (0)*v 0 + (0)*v 1 + (((17*X)/(6)) + ((17*X*Y*a)/(6)) + ((17*X*Y^2)/(6)))*v 2
  | 74 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 75 => (0)*v 0 + (((34)/(15*X)))*v 1 + ((((-34)*X)/(15)))*v 2
  | 78 => (0)*v 0 + (((136)/(15)))*v 1 + ((((-136)*X^2)/(15)) + (((-68)*X^3)/(15)) + (((-68)*X^3*Y*a)/(15)) + (((-68)*X^3*Y^2)/(15)))*v 2
  | 79 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 82 => (0)*v 0 + ((((-680))/(X*W^2)))*v 1 + (0)*v 2
  | 83 => (0)*v 0 + (0)*v 1 + (((408)/(5*Y^2)) + ((204*X)/(5*Y^2)) + ((204*X*a)/(5*Y)) + ((204*X)/(5)))*v 2
  | 85 => (0)*v 0 + (0)*v 1 + ((((-115)*X*Z)/(3*W^2)))*v 2
  | 90 => (0)*v 0 + (((6*Z)/(5*Y^2)))*v 1 + ((((-6)*X^2*Z)/(5*Y^2)) + (((-3)*X^3*Z)/(5*Y^2)) + (((-3)*X^3*Z*a)/(5*Y)) + (((-3)*X^3*Z)/(5)))*v 2
  | 91 => (0)*v 0 + ((((-6)*Z)/(Y^2)))*v 1 + (((6*X^2*Z)/(Y^2)) + ((3*X^3*Z)/(Y^2)) + ((3*X^3*Z*a)/(Y)) + (3*X^3*Z))*v 2
  | 92 => (0)*v 0 + (0)*v 1 + ((((-102)*X)/(5*Y^2)) + (((-51)*X*a)/(5*Y)) + ((102*X)/(5)) + (((-51)*X*a^2)/(5)) + (((-51)*X*Y*a)/(5)))*v 2
  | 93 => (0)*v 0 + (0)*v 1 + ((((-30)*X*Z)/(W^2)))*v 2
  | 94 => (0)*v 0 + (((510)/(Y^2*W^2)))*v 1 + ((((-510)*X^2)/(Y^2*W^2)) + (((-255)*X^3)/(Y^2*W^2)) + (((-255)*X^3*a)/(Y*W^2)) + (((-255)*X^3)/(W^2)))*v 2
  | 95 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 96 => (0)*v 0 + (0)*v 1 + ((((-255))/(Y^2*W^2)) + (((-255)*a)/(Y*W^2)) + (((-255))/(W^2)))*v 2
  | 101 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 102 => (0)*v 0 + ((((-850))/(3*X*W^2)))*v 1 + (((850*X)/(3*W^2)))*v 2
  | 103 => (0)*v 0 + (0)*v 1 + (((1275)/(Y^2*W^2)) + ((1275*a)/(Y*W^2)) + ((1275)/(W^2)))*v 2
  | 106 => (0)*v 0 + (0)*v 1 + (((90*X*Z)/(Y^2*W^2)))*v 2
  | 108 => (0)*v 0 + (0)*v 1 + (((2040)/(Y^2*W^2)) + ((1020*X)/(Y^2*W^2)) + ((1020*X*a)/(Y*W^2)) + ((1020*X)/(W^2)))*v 2
  | 109 => (0)*v 0 + ((((-34))/(15*X)))*v 1 + (((34*X)/(15)))*v 2
  | 110 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 112 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 116 => (0)*v 0 + (0)*v 1 + ((((-51))/(5*Y^2)) + (((-51)*a)/(5*Y)) + (((-51))/(5)))*v 2
  | 117 => (0)*v 0 + (0)*v 1 + (((15*X*Z)/(Y^2*W^2)))*v 2
  | 118 => (0)*v 0 + (0)*v 1 + (((51*X)/(10*Y^2)) + ((51*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)))*v 2
  | 119 => (0)*v 0 + (0)*v 1 + (((17*X)/(5)) + ((17*X^2)/(10)) + ((17*X^2*Y*a)/(10)) + ((17*X^2*Y^2)/(10)))*v 2
  | 120 => (0)*v 0 + (0)*v 1 + (((5*Z)/(3*W^2)) + ((5*Y*Z*a)/(3*W^2)) + ((5*Y^2*Z)/(3*W^2)) + (((-10)*X*Z)/(3*W^2)))*v 2
  | 121 => (0)*v 0 + (0)*v 1 + (((34)/(15)))*v 2
  | 122 => (0)*v 0 + (0)*v 1 + ((((-5)*X*Z)/(6*W^2)) + (((-5)*X*Y*Z*a)/(6*W^2)) + (((-5)*X*Y^2*Z)/(6*W^2)))*v 2
  | 124 => (0)*v 0 + ((((-1020))/(X*Y^2*W^2)))*v 1 + (0)*v 2
  | 125 => (0)*v 0 + (((1020)/(Y^2*W^2)))*v 1 + (0)*v 2
  | 126 => (0)*v 0 + ((((-68))/(15)))*v 1 + (0)*v 2
  | 128 => (0)*v 0 + (0)*v 1 + (((816)/(5*Y^2)) + ((408*X)/(5*Y^2)) + ((408*X*a)/(5*Y)) + ((408*X)/(5)))*v 2
  | 130 => (0)*v 0 + (0)*v 1 + ((((-17)*X)/(6)) + (((-17)*X*Y*a)/(6)) + (((-17)*X*Y^2)/(6)))*v 2
  | 131 => (0)*v 0 + (((51)/(5)))*v 1 + ((((-51)*X)/(10*Y^2)) + (((-51)*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)) + (((-51)*X^2*a)/(10*Y)) + (((-51)*X^2*a^2)/(10)) + (((-51)*X^2*Y*a)/(10)))*v 2
  | 132 => (0)*v 0 + (0)*v 1 + (((102)/(5*Y^2)))*v 2
  | 134 => (0)*v 0 + (0)*v 1 + ((((-85))/(W^2)) + (((-85)*Y*a)/(W^2)) + (((-85)*Y^2)/(W^2)))*v 2
  | 138 => (0)*v 0 + ((17))*v 1 + (((-17)*X^2) + (((-17)*X^3)/(2)) + (((-17)*X^3*Y*a)/(2)) + (((-17)*X^3*Y^2)/(2)))*v 2
  | 140 => (0)*v 0 + (0)*v 1 + ((((-17))/(5)) + (((-17)*Y*a)/(5)) + (((-17)*Y^2)/(5)))*v 2
  | 144 => (0)*v 0 + (0)*v 1 + (((51*X)/(Y^2)))*v 2
  | 148 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 155 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 157 => (0)*v 0 + (((51)/(5)))*v 1 + ((((-51)*X)/(10*Y^2)) + (((-51)*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)) + (((-51)*X^2*a)/(10*Y)) + (((-51)*X^2*a^2)/(10)) + (((-51)*X^2*Y*a)/(10)))*v 2
  | 158 => (0)*v 0 + (0)*v 1 + ((((-17)*X)/(6)) + (((-17)*X*Y*a)/(6)) + (((-17)*X*Y^2)/(6)))*v 2
  | 161 => (0)*v 0 + (((255)/(Y^2*W^2)))*v 1 + ((((-255)*X^2)/(Y^2*W^2)) + (((-255)*X^3)/(2*Y^2*W^2)) + (((-255)*X^3*a)/(2*Y*W^2)) + (((-255)*X^3)/(2*W^2)))*v 2
  | 162 => (0)*v 0 + (0)*v 1 + ((((-30)*X*Z)/(Y^2*W^2)) + (((-15)*X*Z*a)/(Y*W^2)) + ((30*X*Z)/(W^2)) + (((-15)*X*Z*a^2)/(W^2)) + (((-15)*X*Y*Z*a)/(W^2)))*v 2
  | 164 => (0)*v 0 + (((510)/(X*Y^2*W^2)))*v 1 + ((((-510)*X)/(Y^2*W^2)) + (((-255)*X^2)/(Y^2*W^2)) + (((-255)*X^2*a)/(Y*W^2)) + (((-255)*X^2)/(W^2)))*v 2
  | 167 => (0)*v 0 + (((510)/(X*Y^2*W^2)))*v 1 + ((((-510)*X)/(Y^2*W^2)))*v 2
  | 168 => (0)*v 0 + (((68)/(15)))*v 1 + (0)*v 2
  | 183 => (0)*v 0 + (0)*v 1 + ((((-510))/(Y^2*W^2)))*v 2
  | 187 => (0)*v 0 + (0)*v 1 + (((510*X)/(Y^2*W^2)))*v 2
  | 189 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 192 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 196 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 197 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 198 => (0)*v 0 + (0)*v 1 + (((15*Z)/(Y^2*W^2)) + ((15*Z*a)/(Y*W^2)) + (((-15)*Z)/(W^2)) + ((30*X*Z)/(Y^2*W^2)) + ((15*X*Z*a)/(Y*W^2)) + ((15*X*Z*a^2)/(W^2)) + ((15*X*Y*Z*a)/(W^2)))*v 2
  | 199 => (0)*v 0 + (0)*v 1 + (((15*Z)/(Y^2*W^2)) + ((15*Z*a)/(Y*W^2)) + (((-15)*Z)/(W^2)) + ((30*X*Z)/(Y^2*W^2)) + ((15*X*Z*a)/(Y*W^2)) + ((15*X*Z*a^2)/(W^2)) + ((15*X*Y*Z*a)/(W^2)))*v 2
  | 202 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 211 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 217 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 218 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 228 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 238 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 247 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 259 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 260 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 261 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 262 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 265 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 268 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 272 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 276 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 277 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 289 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 295 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 302 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 313 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 315 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 316 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 320 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 333 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 334 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 345 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 354 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 360 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 370 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 372 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 382 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 384 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 399 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 400 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 417 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 424 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 430 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 433 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 443 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 447 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 453 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | 479 => (0)*v 0 + (0)*v 1 + (0)*v 2
  | _ => 0

def requiredSources : List (Fin 546) := [1,2,3,4,6,7,8,9,10,12,14,15,16,18,19,21,22,23,24,25,26,27,29,30,32,33,37,38,39,40,42,43,44,45,47,49,51,52,53,54,55,56,57,58,59,62,63,66,67,70,72,73,74,75,78,79,82,83,85,90,91,92,93,94,95,96,101,102,103,106,108,109,110,112,116,117,118,119,120,121,122,124,125,126,128,130,131,132,134,138,140,144,148,155,157,158,161,162,164,167,168,183,187,189,192,196,197,198,199,202,211,217,218,228,238,247,259,260,261,262,265,268,272,276,277,289,295,302,313,315,316,320,333,334,345,354,360,370,372,382,384,399,400,417,424,430,433,443,447,453,479]

def SourceValues (X Y Z W a b : ℂ) (v : Fin 3→ℂ) (r : Fin 546→ℂ) : Prop :=
  ∀ i, i∈requiredSources → r i=initialValues X Y Z W a b v i

end SmallLevelThirtyFourJetOperatorMMM
end
end

/-! ## SmallLevelThirtyFourJetOperatorMMMBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourJetOperatorMMM
open Complex SmallLevelThirtyFourUnitMMMInhomogeneous

theorem pivot_value_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot0 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 19 (by decide)
  change r 19=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot0,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot1 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 47 (by decide)
  change r 47=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot1,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot2 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 59 (by decide)
  change r 59=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot2,hs]
  rw [pivot_value_0 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot3 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 10 (by decide)
  change r 10=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot3,hs]
  rw [pivot_value_2 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot4 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 4 (by decide)
  change r 4=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot4,hs]
  rw [pivot_value_3 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot5 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 22 (by decide)
  change r 22=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot5,hs]
  rw [pivot_value_3 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot6 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 26 (by decide)
  change r 26=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot6,hs]
  rw [pivot_value_2 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot8 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 40 (by decide)
  change r 40=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot8,hs]
  rw [pivot_value_3 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_8

theorem pivot_value_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot9 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 44 (by decide)
  change r 44=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot9,hs]
  rw [pivot_value_2 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot10 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 27 (by decide)
  change r 27=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot10,hs]
  rw [pivot_value_9 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot11 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 7 (by decide)
  change r 7=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot11,hs]
  rw [pivot_value_10 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot12 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 1 (by decide)
  change r 1=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot12,hs]
  rw [pivot_value_11 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot13 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 25 (by decide)
  change r 25=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot13,hs]
  rw [pivot_value_10 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot14 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 29 (by decide)
  change r 29=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot14,hs]
  rw [pivot_value_13 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot15 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 33 (by decide)
  change r 33=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot15,hs]
  rw [pivot_value_9 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_16 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot16 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 51 (by decide)
  change r 51=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot16,hs]
  rw [pivot_value_5 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_16

theorem pivot_value_18 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot18 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 62 (by decide)
  change r 62=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot18,hs]
  rw [pivot_value_9 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_19 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot19 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 23 (by decide)
  change r 23=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot19,hs]
  rw [pivot_value_18 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot21 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 79 (by decide)
  change r 79=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot21,hs]
  rw [pivot_value_16 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot25 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 101 (by decide)
  change r 101=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot25,hs]
  rw [pivot_value_2 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot26 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 95 (by decide)
  change r 95=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot26,hs]
  rw [pivot_value_25 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot27 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 74 (by decide)
  change r 74=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot27,hs]
  rw [pivot_value_26 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot31 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 110 (by decide)
  change r 110=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot31,hs]
  rw [pivot_value_6 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_33 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot33 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 112 (by decide)
  change r 112=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot33,hs]
  rw [pivot_value_6 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_33

theorem pivot_value_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot40 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 148 (by decide)
  change r 148=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot40,hs]
  rw [pivot_value_6 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot43 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 155 (by decide)
  change r 155=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot43,hs]
  rw [pivot_value_2 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_55 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot55 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-1020))/(W^2)))*v 2 := by
  have hs:=hr 2 (by decide)
  change r 2=(0)*v 0 + (0)*v 1 + ((((-1020))/(W^2)))*v 2 at hs
  rw [rhsPivot55,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_56 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot56 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-1020)*X)/(Y^2*W^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 3 (by decide)
  change r 3=(0)*v 0 + ((((-1020)*X)/(Y^2*W^2)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot56,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_58 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot58 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-595)*X)/(W^2)))*v 2 := by
  have hs:=hr 6 (by decide)
  change r 6=(0)*v 0 + (0)*v 1 + (((238)/(5)))*v 2 at hs
  rw [rhsPivot58,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_59 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot59 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((1785)/(Y^2*W^2)))*v 1 + ((((-1785)*X^2)/(Y^2*W^2)) + (((-1785)*X^3)/(2*Y^2*W^2)) + (((-1785)*X^3*a)/(2*Y*W^2)) + (((-1785)*X^3)/(2*W^2)))*v 2 := by
  have hs:=hr 8 (by decide)
  change r 8=(0)*v 0 + (((1785)/(Y^2*W^2)))*v 1 + ((((-1785)*X^2)/(Y^2*W^2)) + (((-1785)*X^3)/(2*Y^2*W^2)) + (((-1785)*X^3*a)/(2*Y*W^2)) + (((-1785)*X^3)/(2*W^2)))*v 2 at hs
  rw [rhsPivot59,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_60 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot60 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-255)*X)/(Y^2)))*v 2 := by
  have hs:=hr 9 (by decide)
  change r 9=(0)*v 0 + (0)*v 1 + (((1190)/(3*W^2)))*v 2 at hs
  rw [rhsPivot60,hs]
  rw [pivot_value_55 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot62 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((51*X)/(Y^2)))*v 2 := by
  have hs:=hr 12 (by decide)
  change r 12=(0)*v 0 + (0)*v 1 + (((1173*X)/(5*Y^2)))*v 2 at hs
  rw [rhsPivot62,hs]
  rw [pivot_value_55 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_62

theorem pivot_value_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot64 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-255)*X)/(Y^2)))*v 2 := by
  have hs:=hr 14 (by decide)
  change r 14=(0)*v 0 + (0)*v 1 + (((170)/(3)))*v 2 at hs
  rw [rhsPivot64,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_65 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot65 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((170*Y^2)/(X*W^2)))*v 1 + ((((-85))/(W^2)) + (((-85)*Y*a)/(W^2)) + ((85*Y^2)/(W^2)) + (((-170)*X)/(W^2)) + (((-85)*X*Y*a)/(W^2)) + (((-85)*X*Y^2*a^2)/(W^2)) + (((-85)*X*Y^3*a)/(W^2)))*v 2 := by
  have hs:=hr 15 (by decide)
  change r 15=(0)*v 0 + ((((-85)*Y^2)/(W^2)))*v 1 + (((85*X)/(2*W^2)) + ((85*X*Y*a)/(2*W^2)) + (((-85)*X*Y^2)/(2*W^2)) + ((85*X^2)/(W^2)) + ((85*X^2*Y*a)/(2*W^2)) + ((85*X^2*Y^2*a^2)/(2*W^2)) + ((85*X^2*Y^3*a)/(2*W^2)))*v 2 at hs
  rw [rhsPivot65,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot66 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-170))/(X*W^2)))*v 1 + (((170*X)/(W^2)))*v 2 := by
  have hs:=hr 16 (by decide)
  change r 16=(0)*v 0 + ((((-170))/(X*W^2)))*v 1 + (((170*X)/(W^2)))*v 2 at hs
  rw [rhsPivot66,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot68 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-255))/(Y^2*W^2)) + (((-255)*a)/(Y*W^2)) + (((-255))/(W^2)))*v 2 := by
  have hs:=hr 18 (by decide)
  change r 18=(0)*v 0 + (0)*v 1 + ((((-255))/(Y^2*W^2)) + (((-255)*a)/(Y*W^2)) + (((-255))/(W^2)))*v 2 at hs
  rw [rhsPivot68,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_70 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot70 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-595)*X)/(W^2)))*v 2 := by
  have hs:=hr 21 (by decide)
  change r 21=(0)*v 0 + (0)*v 1 + (((170)/(W^2)))*v 2 at hs
  rw [rhsPivot70,hs]
  rw [pivot_value_55 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot71 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((510*Z)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 24 (by decide)
  change r 24=(0)*v 0 + (0)*v 1 + ((((-85)*X*Z)/(3*W^2)))*v 2 at hs
  rw [rhsPivot71,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_72 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot72 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-480)*Z)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 30 (by decide)
  change r 30=(0)*v 0 + (0)*v 1 + ((((-544))/(15)))*v 2 at hs
  rw [rhsPivot72,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot73 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((1530)/(Y^2*W^2)))*v 1 + ((((-1530)*X^2)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 32 (by decide)
  change r 32=(0)*v 0 + (((1530)/(Y^2*W^2)))*v 1 + ((((-1530)*X^2)/(Y^2*W^2)))*v 2 at hs
  rw [rhsPivot73,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_73

theorem pivot_value_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot77 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((-17)*X))*v 2 := by
  have hs:=hr 37 (by decide)
  change r 37=(0)*v 0 + (0)*v 1 + (((17*X)/(5)))*v 2 at hs
  rw [rhsPivot77,hs]
  rw [pivot_value_55 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot78 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((51*X)/(Y^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 38 (by decide)
  change r 38=(0)*v 0 + ((((-34))/(15)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot78,hs]
  rw [pivot_value_56 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot79 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((510)/(Y^2*W^2)) + ((255*X)/(Y^2*W^2)) + ((255*X*a)/(Y*W^2)) + ((255*X)/(W^2)))*v 2 := by
  have hs:=hr 39 (by decide)
  change r 39=(0)*v 0 + (0)*v 1 + ((((-17)*X)/(15)) + (((-17)*X^2)/(30)) + (((-17)*X^2*Y*a)/(30)) + (((-17)*X^2*Y^2)/(30)))*v 2 at hs
  rw [rhsPivot79,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot81 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-255)*X)/(Y^2*W^2)) + (((-255)*X^2)/(2*Y^2*W^2)) + (((-255)*X^2*a)/(2*Y*W^2)) + (((-255)*X^2)/(2*W^2)))*v 2 := by
  have hs:=hr 42 (by decide)
  change r 42=(0)*v 0 + (0)*v 1 + (((102)/(5*Y^2)) + ((51*X)/(5*Y^2)) + ((51*X*a)/(5*Y)) + ((51*X)/(5)))*v 2 at hs
  rw [rhsPivot81,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot82 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-408))/(Y^2)))*v 2 := by
  have hs:=hr 43 (by decide)
  change r 43=(0)*v 0 + (0)*v 1 + ((((-51)*X)/(Y^2)))*v 2 at hs
  rw [rhsPivot82,hs]
  rw [pivot_value_60 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot83 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((-68)))*v 2 := by
  have hs:=hr 45 (by decide)
  change r 45=(0)*v 0 + (0)*v 1 + (((255*X)/(W^2)))*v 2 at hs
  rw [rhsPivot83,hs]
  rw [pivot_value_58 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot86 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-255))/(Y^2*W^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 49 (by decide)
  change r 49=(0)*v 0 + ((((-255))/(Y^2*W^2)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot86,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_87 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot87 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-170))/(3*X*W^2)))*v 1 + (((170*X)/(3*W^2)))*v 2 := by
  have hs:=hr 52 (by decide)
  change r 52=(0)*v 0 + (((51)/(5*Y^2)))*v 1 + ((((-51)*X^2)/(5*Y^2)))*v 2 at hs
  rw [rhsPivot87,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_87

theorem pivot_value_88 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot88 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-51))/(Y^2)))*v 1 + (((51*X^2)/(Y^2)) + ((51*X^3)/(2*Y^2)) + ((51*X^3*a)/(2*Y)) + ((51*X^3)/(2)))*v 2 := by
  have hs:=hr 53 (by decide)
  change r 53=(0)*v 0 + (((34)/(3*X)))*v 1 + ((((-34)*X)/(3)) + (((-17)*X^2)/(3)) + (((-17)*X^2*Y*a)/(3)) + (((-17)*X^2*Y^2)/(3)))*v 2 at hs
  rw [rhsPivot88,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_89 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot89 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-102))/(5*X*Y^2)) + ((102*a)/(5*X*Y)) + (((-102))/(5*X)))*v 1 + ((((-102))/(5*Y^2)) + (((-102)*X*a)/(5*Y)))*v 2 := by
  have hs:=hr 54 (by decide)
  change r 54=(0)*v 0 + ((((-102))/(5*X*Y^2)) + ((102*a)/(5*X*Y)) + (((-102))/(5*X)))*v 1 + ((((-102))/(5*Y^2)) + (((-102)*X*a)/(5*Y)))*v 2 at hs
  rw [rhsPivot89,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_90 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot90 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-102))/(5*X*Y^2)) + ((102*a)/(5*X*Y)) + (((-102))/(5*X)))*v 1 + ((((-102))/(5*Y^2)) + (((-102)*X*a)/(5*Y)))*v 2 := by
  have hs:=hr 55 (by decide)
  change r 55=(0)*v 0 + (((85)/(3*W^2)) + (((-85)*Y*a)/(3*W^2)) + ((85*Y^2)/(3*W^2)))*v 1 + (((85*X)/(3*W^2)) + ((85*X^2*Y*a)/(3*W^2)))*v 2 at hs
  rw [rhsPivot90,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_91 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot91 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((-17)*X))*v 2 := by
  have hs:=hr 56 (by decide)
  change r 56=(0)*v 0 + (0)*v 1 + ((34))*v 2 at hs
  rw [rhsPivot91,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_92 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot92 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-51))/(Y^2)))*v 1 + (((51*X^2)/(Y^2)) + ((51*X^3)/(2*Y^2)) + ((51*X^3*a)/(2*Y)) + ((51*X^3)/(2)))*v 2 := by
  have hs:=hr 57 (by decide)
  change r 57=(0)*v 0 + ((((-51))/(Y^2)))*v 1 + (((51*X^2)/(Y^2)) + ((51*X^3)/(2*Y^2)) + ((51*X^3*a)/(2*Y)) + ((51*X^3)/(2)))*v 2 at hs
  rw [rhsPivot92,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_93 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot93 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-102))/(5*Y^2)))*v 1 + (((102*X^2)/(5*Y^2)))*v 2 := by
  have hs:=hr 58 (by decide)
  change r 58=(0)*v 0 + ((((-170))/(3*X*W^2)))*v 1 + (((170*X)/(3*W^2)))*v 2 at hs
  rw [rhsPivot93,hs]
  rw [pivot_value_66 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_95 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot95 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-51))/(Y^2)) + (((-51)*a)/(Y)) + ((-51)))*v 2 := by
  have hs:=hr 63 (by decide)
  change r 63=(0)*v 0 + (0)*v 1 + ((((-51))/(Y^2)) + (((-51)*a)/(Y)) + ((-51)))*v 2 at hs
  rw [rhsPivot95,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_98 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot98 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((51*X)/(Y^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 66 (by decide)
  change r 66=(0)*v 0 + (((51*X)/(Y^2)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot98,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_98

theorem pivot_value_99 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot99 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((34)/(X)))*v 1 + (0)*v 2 := by
  have hs:=hr 67 (by decide)
  change r 67=(0)*v 0 + (((34)/(X)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot99,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_102 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot102 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((34)/(X)))*v 1 + (0)*v 2 := by
  have hs:=hr 70 (by decide)
  change r 70=(0)*v 0 + (((-17)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot102,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_104 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot104 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-85)*X)/(2*W^2)) + (((-85)*X*Y*a)/(2*W^2)) + (((-85)*X*Y^2)/(2*W^2)))*v 2 := by
  have hs:=hr 72 (by decide)
  change r 72=(0)*v 0 + (0)*v 1 + (((17)/(5)) + ((17*Y*a)/(5)) + ((17*Y^2)/(5)))*v 2 at hs
  rw [rhsPivot104,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_105 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot105 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-51))/(Y^2)) + (((-51)*a)/(Y)) + ((-51)))*v 2 := by
  have hs:=hr 73 (by decide)
  change r 73=(0)*v 0 + (0)*v 1 + (((17*X)/(6)) + ((17*X*Y*a)/(6)) + ((17*X*Y^2)/(6)))*v 2 at hs
  rw [rhsPivot105,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_106 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot106 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-255))/(Y^2*W^2)))*v 1 + (((255*X^2)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 75 (by decide)
  change r 75=(0)*v 0 + (((34)/(15*X)))*v 1 + ((((-34)*X)/(15)))*v 2 at hs
  rw [rhsPivot106,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_108 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot108 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-2040))/(Y^2*W^2)))*v 1 + (((2040*X^2)/(Y^2*W^2)) + ((1020*X^3)/(Y^2*W^2)) + ((1020*X^3*a)/(Y*W^2)) + ((1020*X^3)/(W^2)))*v 2 := by
  have hs:=hr 78 (by decide)
  change r 78=(0)*v 0 + (((136)/(15)))*v 1 + ((((-136)*X^2)/(15)) + (((-68)*X^3)/(15)) + (((-68)*X^3*Y*a)/(15)) + (((-68)*X^3*Y^2)/(15)))*v 2 at hs
  rw [rhsPivot108,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_110 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot110 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((170)/(X*W^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 82 (by decide)
  change r 82=(0)*v 0 + ((((-680))/(X*W^2)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot110,hs]
  rw [pivot_value_102 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_111 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot111 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((102)/(Y^2)) + ((51*X)/(Y^2)) + ((51*X*a)/(Y)) + (51*X))*v 2 := by
  have hs:=hr 83 (by decide)
  change r 83=(0)*v 0 + (0)*v 1 + (((408)/(5*Y^2)) + ((204*X)/(5*Y^2)) + ((204*X*a)/(5*Y)) + ((204*X)/(5)))*v 2 at hs
  rw [rhsPivot111,hs]
  rw [pivot_value_79 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_111

theorem pivot_value_113 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot113 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-5)*X*Z)/(W^2)))*v 2 := by
  have hs:=hr 85 (by decide)
  change r 85=(0)*v 0 + (0)*v 1 + ((((-115)*X*Z)/(3*W^2)))*v 2 at hs
  rw [rhsPivot113,hs]
  rw [pivot_value_82 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_117 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot117 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-3)*Z)/(Y^2)))*v 1 + (((3*X^2*Z)/(Y^2)) + ((3*X^3*Z)/(2*Y^2)) + ((3*X^3*Z*a)/(2*Y)) + ((3*X^3*Z)/(2)))*v 2 := by
  have hs:=hr 90 (by decide)
  change r 90=(0)*v 0 + (((6*Z)/(5*Y^2)))*v 1 + ((((-6)*X^2*Z)/(5*Y^2)) + (((-3)*X^3*Z)/(5*Y^2)) + (((-3)*X^3*Z*a)/(5*Y)) + (((-3)*X^3*Z)/(5)))*v 2 at hs
  rw [rhsPivot117,hs]
  rw [pivot_value_59 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_118 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot118 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-3)*Z)/(Y^2)))*v 1 + (((3*X^2*Z)/(Y^2)) + ((3*X^3*Z)/(2*Y^2)) + ((3*X^3*Z*a)/(2*Y)) + ((3*X^3*Z)/(2)))*v 2 := by
  have hs:=hr 91 (by decide)
  change r 91=(0)*v 0 + ((((-6)*Z)/(Y^2)))*v 1 + (((6*X^2*Z)/(Y^2)) + ((3*X^3*Z)/(Y^2)) + ((3*X^3*Z*a)/(Y)) + (3*X^3*Z))*v 2 at hs
  rw [rhsPivot118,hs]
  rw [pivot_value_88 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_119 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot119 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-30)*X*Z)/(Y^2*W^2)) + (((-15)*X*Z*a)/(Y*W^2)) + ((30*X*Z)/(W^2)) + (((-15)*X*Z*a^2)/(W^2)) + (((-15)*X*Y*Z*a)/(W^2)))*v 2 := by
  have hs:=hr 92 (by decide)
  change r 92=(0)*v 0 + (0)*v 1 + ((((-102)*X)/(5*Y^2)) + (((-51)*X*a)/(5*Y)) + ((102*X)/(5)) + (((-51)*X*a^2)/(5)) + (((-51)*X*Y*a)/(5)))*v 2 at hs
  rw [rhsPivot119,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_120 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot120 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-5)*X*Z)/(W^2)))*v 2 := by
  have hs:=hr 93 (by decide)
  change r 93=(0)*v 0 + (0)*v 1 + ((((-30)*X*Z)/(W^2)))*v 2 at hs
  rw [rhsPivot120,hs]
  rw [pivot_value_91 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_121 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot121 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((17))*v 1 + (((-17)*X^2) + (((-17)*X^3)/(2)) + (((-17)*X^3*Y*a)/(2)) + (((-17)*X^3*Y^2)/(2)))*v 2 := by
  have hs:=hr 94 (by decide)
  change r 94=(0)*v 0 + (((510)/(Y^2*W^2)))*v 1 + ((((-510)*X^2)/(Y^2*W^2)) + (((-255)*X^3)/(Y^2*W^2)) + (((-255)*X^3*a)/(Y*W^2)) + (((-255)*X^3)/(W^2)))*v 2 at hs
  rw [rhsPivot121,hs]
  rw [pivot_value_108 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_118 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_122 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot122 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-255))/(Y^2*W^2)) + (((-255)*a)/(Y*W^2)) + (((-255))/(W^2)))*v 2 := by
  have hs:=hr 96 (by decide)
  change r 96=(0)*v 0 + (0)*v 1 + ((((-255))/(Y^2*W^2)) + (((-255)*a)/(Y*W^2)) + (((-255))/(W^2)))*v 2 at hs
  rw [rhsPivot122,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_126 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot126 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-85))/(W^2)))*v 1 + (((85*X^2)/(W^2)))*v 2 := by
  have hs:=hr 102 (by decide)
  change r 102=(0)*v 0 + ((((-850))/(3*X*W^2)))*v 1 + (((850*X)/(3*W^2)))*v 2 at hs
  rw [rhsPivot126,hs]
  rw [pivot_value_66 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_106 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_126

theorem pivot_value_127 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot127 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((85*X)/(2*W^2)) + ((85*X*Y*a)/(2*W^2)) + ((85*X*Y^2)/(2*W^2)))*v 2 := by
  have hs:=hr 103 (by decide)
  change r 103=(0)*v 0 + (0)*v 1 + (((1275)/(Y^2*W^2)) + ((1275*a)/(Y*W^2)) + ((1275)/(W^2)))*v 2 at hs
  rw [rhsPivot127,hs]
  rw [pivot_value_68 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_104 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_128 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot128 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((465*X*Z)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 106 (by decide)
  change r 106=(0)*v 0 + (0)*v 1 + (((90*X*Z)/(Y^2*W^2)))*v 2 at hs
  rw [rhsPivot128,hs]
  rw [pivot_value_60 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_130 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot130 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((10*Z)/(W^2)) + ((5*X*Z)/(W^2)) + ((5*X*Y*Z*a)/(W^2)) + ((5*X*Y^2*Z)/(W^2)))*v 2 := by
  have hs:=hr 108 (by decide)
  change r 108=(0)*v 0 + (0)*v 1 + (((2040)/(Y^2*W^2)) + ((1020*X)/(Y^2*W^2)) + ((1020*X*a)/(Y*W^2)) + ((1020*X)/(W^2)))*v 2 at hs
  rw [rhsPivot130,hs]
  rw [pivot_value_79 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_131 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot131 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((34)/(3*X)))*v 1 + ((((-34)*X)/(3)))*v 2 := by
  have hs:=hr 109 (by decide)
  change r 109=(0)*v 0 + ((((-34))/(15*X)))*v 1 + (((34*X)/(15)))*v 2 at hs
  rw [rhsPivot131,hs]
  rw [pivot_value_73 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_132 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot132 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-51))/(5*Y^2)) + (((-51)*a)/(5*Y)) + (((-51))/(5)))*v 2 := by
  have hs:=hr 116 (by decide)
  change r 116=(0)*v 0 + (0)*v 1 + ((((-51))/(5*Y^2)) + (((-51)*a)/(5*Y)) + (((-51))/(5)))*v 2 at hs
  rw [rhsPivot132,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_133 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot133 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((465*X*Z)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 117 (by decide)
  change r 117=(0)*v 0 + (0)*v 1 + (((15*X*Z)/(Y^2*W^2)))*v 2 at hs
  rw [rhsPivot133,hs]
  rw [pivot_value_83 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_134 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot134 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((51*X)/(10*Y^2)) + ((51*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)))*v 2 := by
  have hs:=hr 118 (by decide)
  change r 118=(0)*v 0 + (0)*v 1 + (((51*X)/(10*Y^2)) + ((51*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)))*v 2 at hs
  rw [rhsPivot134,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_135 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot135 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((10*Z)/(W^2)) + ((5*X*Z)/(W^2)) + ((5*X*Y*Z*a)/(W^2)) + ((5*X*Y^2*Z)/(W^2)))*v 2 := by
  have hs:=hr 119 (by decide)
  change r 119=(0)*v 0 + (0)*v 1 + (((17*X)/(5)) + ((17*X^2)/(10)) + ((17*X^2*Y*a)/(10)) + ((17*X^2*Y^2)/(10)))*v 2 at hs
  rw [rhsPivot135,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_135

theorem pivot_value_136 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot136 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((51*X)/(10*Y^2)) + ((51*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)))*v 2 := by
  have hs:=hr 120 (by decide)
  change r 120=(0)*v 0 + (0)*v 1 + (((5*Z)/(3*W^2)) + ((5*Y*Z*a)/(3*W^2)) + ((5*Y^2*Z)/(3*W^2)) + (((-10)*X*Z)/(3*W^2)))*v 2 at hs
  rw [rhsPivot136,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_137 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot137 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((-68)))*v 2 := by
  have hs:=hr 121 (by decide)
  change r 121=(0)*v 0 + (0)*v 1 + (((34)/(15)))*v 2 at hs
  rw [rhsPivot137,hs]
  rw [pivot_value_128 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_138 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot138 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-51))/(5*Y^2)) + (((-51)*a)/(5*Y)) + (((-51))/(5)))*v 2 := by
  have hs:=hr 122 (by decide)
  change r 122=(0)*v 0 + (0)*v 1 + ((((-5)*X*Z)/(6*W^2)) + (((-5)*X*Y*Z*a)/(6*W^2)) + (((-5)*X*Y^2*Z)/(6*W^2)))*v 2 at hs
  rw [rhsPivot138,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_139 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot139 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((6630)/(X*Y^2*W^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 124 (by decide)
  change r 124=(0)*v 0 + ((((-1020))/(X*Y^2*W^2)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot139,hs]
  rw [pivot_value_99 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_140 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot140 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((1020)/(Y^2*W^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 125 (by decide)
  change r 125=(0)*v 0 + (((1020)/(Y^2*W^2)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot140,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_141 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot141 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((102)/(X*Y^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 126 (by decide)
  change r 126=(0)*v 0 + ((((-68))/(15)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot141,hs]
  rw [pivot_value_86 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_142 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot142 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((102)/(Y^2)) + ((51*X)/(Y^2)) + ((51*X*a)/(Y)) + (51*X))*v 2 := by
  have hs:=hr 128 (by decide)
  change r 128=(0)*v 0 + (0)*v 1 + (((816)/(5*Y^2)) + ((408*X)/(5*Y^2)) + ((408*X*a)/(5*Y)) + ((408*X)/(5)))*v 2 at hs
  rw [rhsPivot142,hs]
  rw [pivot_value_135 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_143 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot143 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-5)*X*Z)/(W^2)) + (((-5)*X*Y*Z*a)/(W^2)) + (((-5)*X*Y^2*Z)/(W^2)))*v 2 := by
  have hs:=hr 130 (by decide)
  change r 130=(0)*v 0 + (0)*v 1 + ((((-17)*X)/(6)) + (((-17)*X*Y*a)/(6)) + (((-17)*X*Y^2)/(6)))*v 2 at hs
  rw [rhsPivot143,hs]
  rw [pivot_value_138 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_143

theorem pivot_value_144 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot144 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((51)/(5)))*v 1 + ((((-51)*X)/(10*Y^2)) + (((-51)*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)) + (((-51)*X^2*a)/(10*Y)) + (((-51)*X^2*a^2)/(10)) + (((-51)*X^2*Y*a)/(10)))*v 2 := by
  have hs:=hr 131 (by decide)
  change r 131=(0)*v 0 + (((51)/(5)))*v 1 + ((((-51)*X)/(10*Y^2)) + (((-51)*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)) + (((-51)*X^2*a)/(10*Y)) + (((-51)*X^2*a^2)/(10)) + (((-51)*X^2*Y*a)/(10)))*v 2 at hs
  rw [rhsPivot144,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_145 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot145 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-408))/(Y^2)))*v 2 := by
  have hs:=hr 132 (by decide)
  change r 132=(0)*v 0 + (0)*v 1 + (((102)/(5*Y^2)))*v 2 at hs
  rw [rhsPivot145,hs]
  rw [pivot_value_58 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_146 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot146 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-85))/(W^2)) + (((-85)*Y*a)/(W^2)) + (((-85)*Y^2)/(W^2)))*v 2 := by
  have hs:=hr 134 (by decide)
  change r 134=(0)*v 0 + (0)*v 1 + ((((-85))/(W^2)) + (((-85)*Y*a)/(W^2)) + (((-85)*Y^2)/(W^2)))*v 2 at hs
  rw [rhsPivot146,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_150 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot150 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((17))*v 1 + (((-17)*X^2) + (((-17)*X^3)/(2)) + (((-17)*X^3*Y*a)/(2)) + (((-17)*X^3*Y^2)/(2)))*v 2 := by
  have hs:=hr 138 (by decide)
  change r 138=(0)*v 0 + ((17))*v 1 + (((-17)*X^2) + (((-17)*X^3)/(2)) + (((-17)*X^3*Y*a)/(2)) + (((-17)*X^3*Y^2)/(2)))*v 2 at hs
  rw [rhsPivot150,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_152 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot152 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((85*X)/(2*W^2)) + ((85*X*Y*a)/(2*W^2)) + ((85*X*Y^2)/(2*W^2)))*v 2 := by
  have hs:=hr 140 (by decide)
  change r 140=(0)*v 0 + (0)*v 1 + ((((-17))/(5)) + (((-17)*Y*a)/(5)) + (((-17)*Y^2)/(5)))*v 2 at hs
  rw [rhsPivot152,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_156 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot156 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((51*X)/(Y^2)))*v 2 := by
  have hs:=hr 144 (by decide)
  change r 144=(0)*v 0 + (0)*v 1 + (((51*X)/(Y^2)))*v 2 at hs
  rw [rhsPivot156,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_164 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot164 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((204)/(5)))*v 1 + ((((-102)*X)/(5*Y^2)) + (((-102)*X*a)/(5*Y)) + ((102*X)/(5)) + (((-204)*X^2)/(5*Y^2)) + (((-102)*X^2*a)/(5*Y)) + (((-102)*X^2*a^2)/(5)) + (((-102)*X^2*Y*a)/(5)))*v 2 := by
  have hs:=hr 157 (by decide)
  change r 157=(0)*v 0 + (((51)/(5)))*v 1 + ((((-51)*X)/(10*Y^2)) + (((-51)*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)) + (((-51)*X^2*a)/(10*Y)) + (((-51)*X^2*a^2)/(10)) + (((-51)*X^2*Y*a)/(10)))*v 2 at hs
  rw [rhsPivot164,hs]
  rw [pivot_value_65 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_165 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot165 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-5)*X*Z)/(W^2)) + (((-5)*X*Y*Z*a)/(W^2)) + (((-5)*X*Y^2*Z)/(W^2)))*v 2 := by
  have hs:=hr 158 (by decide)
  change r 158=(0)*v 0 + (0)*v 1 + ((((-17)*X)/(6)) + (((-17)*X*Y*a)/(6)) + (((-17)*X*Y^2)/(6)))*v 2 at hs
  rw [rhsPivot165,hs]
  rw [pivot_value_132 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_165

theorem pivot_value_168 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot168 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-510))/(X*Y^2*W^2)))*v 1 + (((510*X)/(Y^2*W^2)) + ((255*X^2)/(Y^2*W^2)) + ((255*X^2*a)/(Y*W^2)) + ((255*X^2)/(W^2)))*v 2 := by
  have hs:=hr 161 (by decide)
  change r 161=(0)*v 0 + (((255)/(Y^2*W^2)))*v 1 + ((((-255)*X^2)/(Y^2*W^2)) + (((-255)*X^3)/(2*Y^2*W^2)) + (((-255)*X^3*a)/(2*Y*W^2)) + (((-255)*X^3)/(2*W^2)))*v 2 at hs
  rw [rhsPivot168,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_169 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot169 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-30)*X*Z)/(Y^2*W^2)) + (((-15)*X*Z*a)/(Y*W^2)) + ((30*X*Z)/(W^2)) + (((-15)*X*Z*a^2)/(W^2)) + (((-15)*X*Y*Z*a)/(W^2)))*v 2 := by
  have hs:=hr 162 (by decide)
  change r 162=(0)*v 0 + (0)*v 1 + ((((-30)*X*Z)/(Y^2*W^2)) + (((-15)*X*Z*a)/(Y*W^2)) + ((30*X*Z)/(W^2)) + (((-15)*X*Z*a^2)/(W^2)) + (((-15)*X*Y*Z*a)/(W^2)))*v 2 at hs
  rw [rhsPivot169,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_171 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot171 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((4335)/(Y^2*W^2)))*v 1 + ((((-4335)*X^2)/(Y^2*W^2)) + (((-4335)*X^3)/(2*Y^2*W^2)) + (((-4335)*X^3*a)/(2*Y*W^2)) + (((-4335)*X^3)/(2*W^2)))*v 2 := by
  have hs:=hr 164 (by decide)
  change r 164=(0)*v 0 + (((510)/(X*Y^2*W^2)))*v 1 + ((((-510)*X)/(Y^2*W^2)) + (((-255)*X^2)/(Y^2*W^2)) + (((-255)*X^2*a)/(Y*W^2)) + (((-255)*X^2)/(W^2)))*v 2 at hs
  rw [rhsPivot171,hs]
  rw [pivot_value_121 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_168 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_174 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot174 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((510)/(X*Y^2*W^2)))*v 1 + ((((-510)*X)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 167 (by decide)
  change r 167=(0)*v 0 + (((510)/(X*Y^2*W^2)))*v 1 + ((((-510)*X)/(Y^2*W^2)))*v 2 at hs
  rw [rhsPivot174,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_175 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot175 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-1020))/(Y^2*W^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 168 (by decide)
  change r 168=(0)*v 0 + (((68)/(15)))*v 1 + (0)*v 2 at hs
  rw [rhsPivot175,hs]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_185 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot185 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-11220))/(Y^2*W^2)))*v 2 := by
  have hs:=hr 183 (by decide)
  change r 183=(0)*v 0 + (0)*v 1 + ((((-510))/(Y^2*W^2)))*v 2 at hs
  rw [rhsPivot185,hs]
  rw [pivot_value_70 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_187 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot187 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-5865)*X)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 187 (by decide)
  change r 187=(0)*v 0 + (0)*v 1 + (((510*X)/(Y^2*W^2)))*v 2 at hs
  rw [rhsPivot187,hs]
  rw [pivot_value_64 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_189 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot189 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-68))/(3*X)))*v 1 + (((68*X)/(3)) + ((34*X^2)/(3)) + ((34*X^2*Y*a)/(3)) + ((34*X^2*Y^2)/(3)))*v 2 := by
  have hs:=hr 189 (by decide)
  change r 189=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot189,hs]
  rw [pivot_value_117 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_118 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_189

theorem pivot_value_190 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot190 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 192 (by decide)
  change r 192=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot190,hs]
  rw [pivot_value_6 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_12 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_192 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot192 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 196 (by decide)
  change r 196=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot192,hs]
  rw [pivot_value_6 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_11 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_193 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot193 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 197 (by decide)
  change r 197=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot193,hs]
  rw [pivot_value_6 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_12 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_194 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot194 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((102))*v 2 := by
  have hs:=hr 259 (by decide)
  change r 259=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot194,hs]
  rw [pivot_value_33 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_185 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_187 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_195 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot195 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-323)*X)/(5)) + (((-34)*X*Y*a)/(5)) + (((-34)*X*Y^2)/(5)))*v 2 := by
  have hs:=hr 202 (by decide)
  change r 202=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot195,hs]
  rw [pivot_value_113 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_120 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_143 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_165 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_196 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot196 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 262 (by decide)
  change r 262=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot196,hs]
  rw [pivot_value_19 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_140 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_175 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_198 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot198 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 268 (by decide)
  change r 268=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot198,hs]
  rw [pivot_value_8 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_127 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_146 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_202 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot202 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((646)/(5)) + ((68*Y*a)/(5)) + ((68*Y^2)/(5)))*v 2 := by
  have hs:=hr 316 (by decide)
  change r 316=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot202,hs]
  rw [pivot_value_3 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_202

theorem pivot_value_205 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot205 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((51*X)/(2*Y^2)) + ((51*X*a)/(2*Y)) + ((51*X)/(2)) + (((-323)*X^2)/(10)) + (((-17)*X^2*Y*a)/(5)) + (((-17)*X^2*Y^2)/(5)))*v 2 := by
  have hs:=hr 320 (by decide)
  change r 320=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot205,hs]
  rw [pivot_value_95 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_192 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_207 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot207 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 333 (by decide)
  change r 333=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot207,hs]
  rw [pivot_value_40 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_208 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot208 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 334 (by decide)
  change r 334=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot208,hs]
  rw [pivot_value_27 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_217 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot217 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 345 (by decide)
  change r 345=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot217,hs]
  rw [pivot_value_14 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_219 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot219 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((6069*X)/(10*Y^2)) + ((867*X*a)/(10*Y)) + ((867*X)/(10)))*v 2 := by
  have hs:=hr 360 (by decide)
  change r 360=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot219,hs]
  rw [pivot_value_105 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_193 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_227 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot227 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 430 (by decide)
  change r 430=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot227,hs]
  rw [pivot_value_3 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_9 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_15 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_230 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot230 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-391)*X)/(20)) + ((17*X*Y*a)/(20)) + (((-119)*X*Y^2)/(60)))*v 2 := by
  have hs:=hr 453 (by decide)
  change r 453=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot230,hs]
  rw [pivot_value_105 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_137 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_145 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_198 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_231 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot231 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-95)*Z)/(2*W^2)) + ((25*Y*Z*a)/(2*W^2)) + ((25*Y^2*Z)/(6*W^2)) + ((5*X*Z)/(W^2)))*v 2 := by
  have hs:=hr 272 (by decide)
  change r 272=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot231,hs]
  rw [pivot_value_62 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_132 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_134 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_165 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_230 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_231

theorem pivot_value_232 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot232 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((901*X^2)/(40)) + ((153*X^2*Y*a)/(40)) + ((289*X^2*Y^2)/(120)))*v 2 := by
  have hs:=hr 289 (by decide)
  change r 289=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot232,hs]
  rw [pivot_value_113 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_130 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_143 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_230 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_233 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot233 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((-51)*X) + ((391*X^2)/(40)) + (((-17)*X^2*Y*a)/(40)) + ((119*X^2*Y^2)/(120)))*v 2 := by
  have hs:=hr 302 (by decide)
  change r 302=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot233,hs]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_230 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_234 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot234 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-245)*Z)/(2*W^2)) + (((-25)*Y*Z*a)/(2*W^2)) + (((-25)*Y^2*Z)/(6*W^2)) + ((80*X*Z)/(W^2)))*v 2 := by
  have hs:=hr 211 (by decide)
  change r 211=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot234,hs]
  rw [pivot_value_130 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_135 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_231 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_232 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_233 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_235 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot235 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-68))/(3)))*v 1 + (((493*X)/(5)) + ((34*X*Y*a)/(5)) + ((34*X*Y^2)/(5)) + (((-289)*X^2)/(30)) + (((-17)*X^2*Y*a)/(5)) + (((-17)*X^2*Y^2)/(5)) + ((34*X^3)/(3)) + ((34*X^3*Y*a)/(3)) + ((34*X^3*Y^2)/(3)))*v 2 := by
  have hs:=hr 218 (by decide)
  change r 218=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot235,hs]
  rw [pivot_value_3 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_4 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_9 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_13 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_15 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_27 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_77 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_91 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_121 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_150 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_189 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_232 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_233 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_236 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot236 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-34))/(3*X)) + (((-68))/(3)))*v 1 + ((((-1972))/(5)) + (((-136)*Y*a)/(5)) + (((-136)*Y^2)/(5)) + ((1598*X)/(15)) + ((68*X*Y*a)/(5)) + ((68*X*Y^2)/(5)) + (((-1309)*X^2)/(30)) + (((-187)*X^2*Y*a)/(5)) + (((-187)*X^2*Y^2)/(5)) + ((34*X^3)/(3)) + ((34*X^3*Y*a)/(3)) + ((34*X^3*Y^2)/(3)))*v 2 := by
  have hs:=hr 228 (by decide)
  change r 228=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot236,hs]
  rw [pivot_value_2 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_3 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_4 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_6 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_9 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_10 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_15 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_27 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_77 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_83 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_91 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_99 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_102 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_121 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_131 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_137 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_150 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_189 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_196 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_198 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_202 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_208 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_232 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_233 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_237 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot237 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((1365*Z)/(2*Y^2*W^2)) + ((285*Z*a)/(2*Y*W^2)) + ((85*Z)/(W^2)) + (((-25)*Y*Z*a)/(2*W^2)) + (((-25)*Y^2*Z)/(6*W^2)) + (((-720)*X*Z)/(Y^2*W^2)) + (((-735)*X*Z*a)/(4*Y*W^2)) + (((-5)*X*Z)/(W^2)) + (((-75)*X*Z*a^2)/(4*W^2)) + (((-25)*X*Y*Z*a)/(4*W^2)))*v 2 := by
  have hs:=hr 424 (by decide)
  change r 424=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot237,hs]
  rw [pivot_value_71 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_113 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_130 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_231 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_232 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_234 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_238 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot238 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-1365)*X*Z)/(4*Y^2*W^2)) + (((-285)*X*Z*a)/(4*Y*W^2)) + (((-85)*X*Z)/(2*W^2)) + ((25*X*Y*Z*a)/(4*W^2)) + ((25*X*Y^2*Z)/(12*W^2)))*v 2 := by
  have hs:=hr 433 (by decide)
  change r 433=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot238,hs]
  rw [pivot_value_113 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_133 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_143 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_165 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_230 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_239 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot239 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-510)*X)/(Y^2)) + (((-2703)*X*a)/(20*Y)) + (17*X) + (((-459)*X*a^2)/(20)) + (((-289)*X*Y*a)/(20)))*v 2 := by
  have hs:=hr 382 (by decide)
  change r 382=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot239,hs]
  rw [pivot_value_119 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_237 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_238 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_239

theorem pivot_value_240 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot240 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-1440)*Z)/(Y^2*W^2)) + (((-735)*Z*a)/(2*Y*W^2)) + (((-10)*Z)/(W^2)) + (((-75)*Z*a^2)/(2*W^2)) + (((-25)*Y*Z*a)/(2*W^2)) + (((-465)*X*Z)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 400 (by decide)
  change r 400=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot240,hs]
  rw [pivot_value_119 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_128 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_239 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_241 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot241 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-2715)*X*Z)/(4*Y^2*W^2)) + (((-735)*X*Z*a)/(4*Y*W^2)) + (((-85)*X*Z)/(2*W^2)) + (((-25)*X*Y*Z*a)/(4*W^2)) + (((-25)*X*Y^2*Z)/(12*W^2)))*v 2 := by
  have hs:=hr 443 (by decide)
  change r 443=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot241,hs]
  rw [pivot_value_130 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_135 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_217 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_232 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_233 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_234 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_240 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_242 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot242 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-51)*X)/(Y^2)) + (((-1173)*X*a)/(20*Y)) + ((-34)*X) + ((51*X*a^2)/(20)) + (((-119)*X*Y*a)/(20)))*v 2 := by
  have hs:=hr 217 (by decide)
  change r 217=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot242,hs]
  rw [pivot_value_14 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_40 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_119 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_128 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_133 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_169 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_238 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_239 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_241 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_243 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot243 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-90)*Z)/(Y^2*W^2)) + (((-285)*Z*a)/(2*Y*W^2)) + (((-160)*Z)/(W^2)) + ((75*Z*a^2)/(2*W^2)) + ((25*Y*Z*a)/(2*W^2)) + ((210*X*Z)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 276 (by decide)
  change r 276=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot243,hs]
  rw [pivot_value_133 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_169 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_242 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_244 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot244 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((2715*Z)/(2*Y^2*W^2)) + ((735*Z*a)/(2*Y*W^2)) + ((85*Z)/(W^2)) + ((25*Y*Z*a)/(2*W^2)) + ((25*Y^2*Z)/(6*W^2)) + (((-45)*X*Z)/(Y^2*W^2)) + (((-285)*X*Z*a)/(4*Y*W^2)) + (((-80)*X*Z)/(W^2)) + ((75*X*Z*a^2)/(4*W^2)) + ((25*X*Y*Z*a)/(4*W^2)))*v 2 := by
  have hs:=hr 238 (by decide)
  change r 238=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot244,hs]
  rw [pivot_value_71 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_72 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_83 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_113 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_207 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_217 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_237 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_238 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_240 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_241 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_243 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_246 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot246 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (0)*v 2 := by
  have hs:=hr 479 (by decide)
  change r 479=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot246,hs]
  rw [pivot_value_4 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_13 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_27 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_252 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot252 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-1360)*Y^2)/(27*W^2)))*v 1 + ((((-2295)*X)/(4*W^2)) + (((-255)*X*Y*a)/(4*W^2)) + (((-13685)*X*Y^2)/(36*W^2)) + (((-170)*X*Y^3*a)/(9*W^2)) + (((-170)*X*Y^4)/(9*W^2)) + ((2465*X^2)/(3*W^2)) + ((1955*X^2*Y*a)/(8*W^2)) + ((1445*X^2*Y^2)/(54*W^2)) + ((2125*X^2*Y^2*a^2)/(24*W^2)) + ((6205*X^2*Y^3*a)/(72*W^2)) + ((85*X^2*Y^4)/(9*W^2)) + (((-850)*X^3*Y^2)/(27*W^2)) + (((-850)*X^3*Y^3*a)/(27*W^2)) + (((-850)*X^3*Y^4)/(27*W^2)))*v 2 := by
  have hs:=hr 198 (by decide)
  change r 198=(0)*v 0 + (0)*v 1 + (((15*Z)/(Y^2*W^2)) + ((15*Z*a)/(Y*W^2)) + (((-15)*Z)/(W^2)) + ((30*X*Z)/(Y^2*W^2)) + ((15*X*Z*a)/(Y*W^2)) + ((15*X*Z*a^2)/(W^2)) + ((15*X*Y*Z*a)/(W^2)))*v 2 at hs
  rw [rhsPivot252,hs]
  rw [pivot_value_164 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_231 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_237 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_253 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot253 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-170)*Y^2)/(3*X*W^2)))*v 1 + ((((-5015))/(2*W^2)) + (((-1275)*Y*a)/(2*W^2)) + ((85*Y^2)/(6*W^2)) + ((595*X)/(3*W^2)) + ((765*X*Y*a)/(4*W^2)) + ((85*X*Y^2*a^2)/(4*W^2)) + ((1615*X*Y^3*a)/(36*W^2)))*v 2 := by
  have hs:=hr 199 (by decide)
  change r 199=(0)*v 0 + (0)*v 1 + (((15*Z)/(Y^2*W^2)) + ((15*Z*a)/(Y*W^2)) + (((-15)*Z)/(W^2)) + ((30*X*Z)/(Y^2*W^2)) + ((15*X*Z*a)/(Y*W^2)) + ((15*X*Z*a^2)/(W^2)) + ((15*X*Y*Z*a)/(W^2)))*v 2 at hs
  rw [rhsPivot253,hs]
  rw [pivot_value_144 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_234 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_244 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_253

theorem pivot_value_256 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot256 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-51))/(Y^2)))*v 1 + ((((-102)*X^2)/(Y^2)))*v 2 := by
  have hs:=hr 260 (by decide)
  change r 260=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot256,hs]
  rw [pivot_value_140 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_174 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_187 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_257 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot257 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-68))/(X)))*v 1 + ((34*X) + (((-221)*X^2)/(40)) + ((527*X^2*Y*a)/(40)) + ((1751*X^2*Y^2)/(120)))*v 2 := by
  have hs:=hr 261 (by decide)
  change r 261=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot257,hs]
  rw [pivot_value_81 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_111 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_139 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_171 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_232 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_264 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot264 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-34)*X)/(3)))*v 1 + (((408*X)/(Y^2)) + ((119*X^2)/(5)) + ((17*X^2*Y*a)/(5)) + ((17*X^2*Y^2)/(5)) + (((-255)*X^3)/(2*Y^2)) + (((-2703)*X^3*a)/(80*Y)) + (((-289)*X^3)/(60)) + (((-459)*X^3*a^2)/(80)) + (((-85)*X^3*Y*a)/(16)) + (((-17)*X^3*Y^2)/(10)) + ((17*X^4)/(3)) + ((17*X^4*Y*a)/(3)) + ((17*X^4*Y^2)/(3)))*v 2 := by
  have hs:=hr 277 (by decide)
  change r 277=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot264,hs]
  rw [pivot_value_142 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_164 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_233 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_252 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_277 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot277 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((51)/(5*Y^2)) + (((-51)*a)/(5*Y)) + ((51)/(5)))*v 1 + (((51*X)/(5*Y^2)) + (((-8619)*X^2)/(40*Y^2)) + (((-1479)*X^2*a)/(40*Y)) + (((-1377)*X^2)/(40)) + ((391*X^3)/(80)) + (((-17)*X^3*Y*a)/(80)) + ((119*X^3*Y^2)/(240)))*v 2 := by
  have hs:=hr 295 (by decide)
  change r 295=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot277,hs]
  rw [pivot_value_89 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_219 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_230 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_288 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot288 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + (((510*X)/(W^2)))*v 2 := by
  have hs:=hr 313 (by decide)
  change r 313=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot288,hs]
  rw [pivot_value_55 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_290 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot290 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-510))/(Y^2*W^2)) + (((-41565)*X)/(4*Y^2*W^2)) + (((-7905)*X*a)/(4*Y*W^2)) + (((-5355)*X)/(4*W^2)))*v 2 := by
  have hs:=hr 315 (by decide)
  change r 315=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot290,hs]
  rw [pivot_value_79 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_232 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_311 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot311 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-255)*X)/(Y^2*W^2)))*v 2 := by
  have hs:=hr 370 (by decide)
  change r 370=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot311,hs]
  rw [pivot_value_122 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_152 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_190 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_202 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_230 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_290 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_313 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot313 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-680))/(X^2*W^2)))*v 1 + (0)*v 2 := by
  have hs:=hr 372 (by decide)
  change r 372=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot313,hs]
  rw [pivot_value_87 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_256 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_288 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_313

theorem pivot_value_319 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot319 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (((51)/(5*Y^2)) + (((-51)*a)/(5*Y)) + ((51)/(5)))*v 1 + (((51*X)/(5*Y^2)) + (((-4029)*X^2)/(40*Y^2)) + ((51*X^2*a)/(40*Y)) + (((-867)*X^2)/(40)) + ((901*X^3)/(80)) + ((153*X^3*Y*a)/(80)) + ((289*X^3*Y^2)/(240)))*v 2 := by
  have hs:=hr 384 (by decide)
  change r 384=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot319,hs]
  rw [pivot_value_90 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_205 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_230 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_330 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot330 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + (0)*v 1 + ((((-51)*X)/(Y^2)) + ((-51)*X^2) + (((-51)*X^3)/(4*Y^2)) + (((-1173)*X^3*a)/(80*Y)) + ((51*X^3*a^2)/(80)) + (((-119)*X^3*Y*a)/(80)))*v 2 := by
  have hs:=hr 399 (by decide)
  change r 399=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot330,hs]
  rw [pivot_value_111 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_144 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_232 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_253 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_331 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot331 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-2380))/(3*W^2)) + (((-170)*Y*a)/(3*W^2)) + ((3230*Y^2)/(27*W^2)) + ((850*X)/(3*W^2)) + (((-850)*X*Y^2)/(27*W^2)))*v 1 + ((((-8075)*X)/(3*W^2)) + (((-2975)*X*Y*a)/(3*W^2)) + (((-170)*X*Y^2)/(W^2)) + (((-170)*X*Y^2*a^2)/(3*W^2)) + (((-170)*X*Y^3*a)/(3*W^2)) + (((-425)*X^2)/(6*W^2)) + ((255*X^2*Y*a)/(W^2)) + (((-11305)*X^2*Y^2)/(54*W^2)) + ((85*X^2*Y^2*a^2)/(3*W^2)) + ((340*X^2*Y^3*a)/(9*W^2)) + ((85*X^2*Y^4)/(9*W^2)) + (((-2125)*X^3)/(4*W^2)) + (((-1105)*X^3*Y*a)/(4*W^2)) + (((-425)*X^3*Y^2)/(3*W^2)) + (((-85)*X^3*Y^2*a^2)/(6*W^2)) + (((-2465)*X^3*Y^3*a)/(54*W^2)) + (((-850)*X^3*Y^4)/(27*W^2)) + ((425*X^4*Y^2)/(27*W^2)) + ((425*X^4*Y^3*a)/(27*W^2)) + ((425*X^4*Y^4)/(27*W^2)))*v 2 := by
  have hs:=hr 247 (by decide)
  change r 247=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot331,hs]
  rw [pivot_value_1 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_21 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_31 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_43 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_60 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_62 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_64 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_78 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_88 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_92 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_93 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_98 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_126 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_134 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_136 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_144 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_156 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_164 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_189 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_192 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_193 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_195 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_196 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_205 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_208 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_219 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_227 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_231 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_234 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_236 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_239 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_242 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_246 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_252 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_253 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_264 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_277 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_319 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_330 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem pivot_value_335 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsPivot335 (X/2) (Y/3) (Z/17) (W/5) a b r=(0)*v 0 + ((((-340))/(3*W^2)) + (((-85)*Y*a)/(3*W^2)) + (((-170)*Y^2)/(9*W^2)) + (((-850)*X*Y*a)/(9*W^2)))*v 1 + (((85*X)/(3*W^2)) + (((-4930)*X*Y*a)/(3*W^2)) + (((-340)*X*Y^2*a^2)/(3*W^2)) + (((-340)*X*Y^3*a)/(3*W^2)) + ((1700*X^2*Y*a)/(3*W^2)) + ((170*X^2*Y^2*a^2)/(3*W^2)) + ((170*X^2*Y^3*a)/(3*W^2)) + (((-6545)*X^3*Y*a)/(36*W^2)) + (((-935)*X^3*Y^2*a^2)/(6*W^2)) + (((-935)*X^3*Y^3*a)/(6*W^2)) + ((425*X^4*Y*a)/(9*W^2)) + ((425*X^4*Y^2*a^2)/(9*W^2)) + ((425*X^4*Y^3*a)/(9*W^2)))*v 2 := by
  have hs:=hr 417 (by decide)
  change r 417=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsPivot335,hs]
  rw [pivot_value_126 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_140 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_236 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_256 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_311 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_313 X Y Z W a b hX hY hZ hW v r hr]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms pivot_value_335

end SmallLevelThirtyFourJetOperatorMMM
end
end
