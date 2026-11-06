module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic
public meta import QuantitativeArithmeticCompactCommandsV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveContinuationNegativeTheoryV4 -/
section
/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveContinuationNegativeDataV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative

def sourceRows0 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 144

def sourceRows1 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 144 + (((-1) * (y^2))) * w 148

def sourceRows2 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 144 + (((-1) * (x^2))) * w 147

def sourceRows3 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((-1)) * w 6 + (1) * w 144

def sourceRows4 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 2

def sourceRows5 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 1 + (((-1) / (x^2))) * w 2

def sourceRows6 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 3 + (((-1) / (x^2))) * w 144

def sourceRows7 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 72 + (((-1) * (y^2))) * w 148

def sourceRows8 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 76 + (((-1) / (y^2))) * w 144

def sourceRows9 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 78 + (((-1) * (x^2))) * w 147

def sourceRows10 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 74 + ((-1)) * w 148

def sourceRows11 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 138

def sourceRows12 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 138 + (((-1) * (y^2))) * w 146

def sourceRows13 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((-1)) * w 12 + (1) * w 138

def sourceRows14 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 4 + (1) * w 138

def sourceRows15 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 0

def sourceRows16 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / (x^2))) * w 0 + (1) * w 75

def sourceRows17 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (y^2) * (z^2)))) * w 0 + (1) * w 149

def sourceRows18 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 120 + (((-1) * (x^2) * (y^2))) * w 145

def sourceRows19 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2) * (y^2))) * w 7 + (1) * w 108

def sourceRows20 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 8 + (1) * w 126

def sourceRows21 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2))) * w 9 + (1) * w 132

def sourceRows22 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135

def sourceRows23 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140

def sourceRows24 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / (x^2))) * w 18 + (1) * w 141

def sourceRows25 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / (y^2))) * w 24 + (1) * w 142

def sourceRows26 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / ((x^2) * (y^2)))) * w 42 + (1) * w 143

def sourceRows27 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 5 + (((-1) / ((x^2) * (y^2)))) * w 30

def sourceRows28 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 77 + (((-1) / (x^2))) * w 142

def sourceRows29 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 80 + (((-1) * (x^2))) * w 145

def sourceRows30 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 42 + (((-1) * (x^2) * (y^2))) * w 139

def sourceRows31 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 60 + (((-1) * (y^2))) * w 140

def sourceRows32 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 66 + (((-1) * (x^2))) * w 141

def sourceRows33 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 69 + ((((-1) * (y^2)) / (x^2))) * w 142

def sourceRows34 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 79 + (((-1) / ((x^2) * (y^2)))) * w 102

def sourceRows35 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 81 + (((-1) / (x^2))) * w 126

def sourceRows36 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 82 + ((((-1) * (x^2)) / (y^2))) * w 129

def sourceRows37 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 84 + ((-1)) * w 132

def sourceRows38 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 87 + ((((-1) * (y^2)) / (x^2))) * w 134

def sourceRows39 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 90 + (((-1) * (x^2))) * w 135

def sourceRows40 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 96 + (((-1) * (y^2))) * w 136

def sourceRows41 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 114 + (((-1) * (x^2) * (y^2))) * w 137

def sourceRows42 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2) * (y^2))) * w 13 + (1) * w 36

def sourceRows43 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 14 + (1) * w 54

def sourceRows44 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (y^2)) / (x^2))) * w 16 + (1) * w 63

def sourceRows45 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (x^2)) / (y^2))) * w 21 + (1) * w 68

def sourceRows46 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / (y^2))) * w 30 + (1) * w 70

def sourceRows47 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / ((x^2) * (y^2)))) * w 48 + (1) * w 71

def sourceRows48 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 73 + (((-1) / ((x^2) * (y^2)))) * w 126

def sourceRows49 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108

def sourceRows50 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 5 + ((1 / ((x^2) * (y^2)))) * w 120

def sourceRows51 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 9 + (((y^2) / ((x^2) * (z^2)))) * w 50

def sourceRows52 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((y^2) / ((x^2) * (z^2)))) * w 100 + (1) * w 141

def sourceRows53 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 10 + ((1 / (y^2))) * w 60

def sourceRows54 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 20 + (((x^2) / (y^2))) * w 105

def sourceRows55 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((x^2) / (y^2))) * w 45 + (1) * w 130

def sourceRows56 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114

def sourceRows57 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125

def sourceRows58 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 50 + (1) * w 100

def sourceRows59 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 40 + (1) * w 60 + (1) * w 90 + (1) * w 110

def sourceRows60 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 20 + ((((-1) * a) / x)) * w 40 + ((1 / (x^2))) * w 80 + (1) * w 95

def sourceRows61 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 9 + ((((-1) * a) / x)) * w 18 + ((1 / (x^2))) * w 36 + (1) * w 84

def sourceRows62 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 25 + (1) * w 125

def sourceRows63 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 18 + ((((-1) * a) / x)) * w 36 + ((1 / (x^2))) * w 72 + (1) * w 93

def sourceRows64 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 36 + ((((-1) * a) / x)) * w 72 + (1) * w 111 + ((1 / (x^2))) * w 144

def sourceRows65 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 6 + (1) * w 39 + ((((-1) * a) / x)) * w 78 + (1) * w 114

def sourceRows66 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 57 + ((1 / (x^2))) * w 78 + ((((-1) * a) / x)) * w 114 + (1) * w 132

def sourceRows67 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (z^2)))) * w 0 + (1) * w 51 + ((1 / ((x^2) * (z^2)))) * w 100 + (1) * w 101

def sourceRows68 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (z^2)))) * w 0 + (1) * w 49 + ((1 / ((x^2) * (z^2)))) * w 50 + (1) * w 99

def sourceRows69 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (z^2))) * w 0 + ((1 / (z^2))) * w 50 + (1) * w 52 + (1) * w 102

def sourceRows70 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (z^2))) * w 0 + (1) * w 48 + (1) * w 98 + ((1 / (z^2))) * w 100

def sourceRows71 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((x^2) / (z^2))) * w 25 + (1) * w 54 + (((x^2) / (z^2))) * w 75 + (1) * w 104

def sourceRows72 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 46 + (((x^2) / (z^2))) * w 75 + (1) * w 96 + (((x^2) / (z^2))) * w 125

def sourceRows73 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 10 + ((((-1) * b) / y)) * w 30 + (1) * w 60 + ((1 / (y^2))) * w 90 + (1) * w 110

def sourceRows74 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 15 + ((((-1) * a) / x)) * w 30 + ((1 / (x^2))) * w 60 + (1) * w 90

def sourceRows75 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 5 + ((((-1) * a) / x)) * w 10 + ((1 / (x^2))) * w 20 + (1) * w 80

def sourceRows76 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 30 + (1) * w 55 + ((1 / (x^2))) * w 80 + (1) * w 105

def sourceRows77 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (y^2))) * w 0 + (1) * w 20 + ((1 / (y^2))) * w 30 + (1) * w 50 + ((1 / (y^2))) * w 60 + (1) * w 80 + (1) * w 110 + ((1 / (y^2))) * w 120

def sourceRows78 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (y^2))) * w 0 + ((1 / (y^2))) * w 30 + (1) * w 40 + (1) * w 70 + ((1 / (y^2))) * w 90 + (1) * w 100 + ((1 / (y^2))) * w 120 + (1) * w 130

def sourceRows79 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 45 + ((1 / (x^2))) * w 70 + (1) * w 95 + ((1 / (x^2))) * w 120

def sourceRows80 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 10 + ((((-1) * a) / x)) * w 20 + ((1 / (x^2))) * w 40 + (1) * w 85

def sourceRows81 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (y^2)))) * w 0 + (1) * w 25 + (1) * w 55 + ((1 / ((x^2) * (y^2)))) * w 60 + (1) * w 85 + ((1 / ((x^2) * (y^2)))) * w 90 + (1) * w 115 + ((1 / ((x^2) * (y^2)))) * w 120

def sourceRows82 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 35 + ((((-1) * a) / x)) * w 70 + (1) * w 110 + ((1 / (x^2))) * w 140

def sourceRows83 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (y^2)))) * w 0 + ((1 / ((x^2) * (y^2)))) * w 30 + (1) * w 35 + ((1 / ((x^2) * (y^2)))) * w 60 + (1) * w 65 + ((1 / ((x^2) * (y^2)))) * w 90 + (1) * w 95 + (1) * w 125

def sourceRows84 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (z^2))) * w 30 + (1) * w 36 + ((1 / (z^2))) * w 60 + (1) * w 66 + ((1 / (z^2))) * w 90 + (1) * w 96 + ((1 / (z^2))) * w 120 + (1) * w 126

def sourceRows85 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 24 + ((1 / (z^2))) * w 30 + (1) * w 54 + ((1 / (z^2))) * w 60 + (1) * w 84 + ((1 / (z^2))) * w 90 + (1) * w 114 + ((1 / (z^2))) * w 120

def sourceRows86 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((x^2) / (z^2))) * w 15 + (1) * w 42 + (((x^2) / (z^2))) * w 45 + (1) * w 72 + (1) * w 102 + (((x^2) / (z^2))) * w 105 + (1) * w 132 + (((x^2) / (z^2))) * w 135

def sourceRows87 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((x^2) / (z^2))) * w 15 + (1) * w 18 + (((x^2) / (z^2))) * w 45 + (1) * w 48 + (1) * w 78 + (((x^2) / (z^2))) * w 105 + (1) * w 108 + (((x^2) / (z^2))) * w 135

def sourceRows88 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (z^2))) * w 0 + (1) * w 26 + ((1 / (z^2))) * w 100 + (1) * w 126

def sourceRows89 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (z^2))) * w 0 + (1) * w 24 + ((1 / (z^2))) * w 50 + (1) * w 124

def sourceRows90 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 2 + ((((-1) * a) / x)) * w 4 + ((1 / (x^2))) * w 8 + (1) * w 77

def sourceRows91 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 33 + ((((-1) * a) / x)) * w 66 + (1) * w 108 + ((1 / (x^2))) * w 132

def sourceRows92 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 37 + ((((-1) * a) / x)) * w 74 + (1) * w 112 + ((1 / (x^2))) * w 148

def sourceRows93 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 2 + (1) * w 38 + ((((-1) * a) / x)) * w 76 + (1) * w 113

def sourceRows94 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 18 + (1) * w 42 + ((((-1) * a) / x)) * w 84 + (1) * w 117

def sourceRows95 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (z^2)))) * w 30 + (1) * w 33 + ((1 / ((x^2) * (z^2)))) * w 60 + (1) * w 63 + ((1 / ((x^2) * (z^2)))) * w 90 + (1) * w 93 + ((1 / ((x^2) * (z^2)))) * w 120 + (1) * w 123

def sourceRows96 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 27 + ((1 / ((x^2) * (z^2)))) * w 30 + (1) * w 57 + ((1 / ((x^2) * (z^2)))) * w 60 + (1) * w 87 + ((1 / ((x^2) * (z^2)))) * w 90 + (1) * w 117 + ((1 / ((x^2) * (z^2)))) * w 120

def sourceRows97 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((y^2) / ((x^2) * (z^2)))) * w 20 + (1) * w 39 + (1) * w 69 + (((y^2) / ((x^2) * (z^2)))) * w 80 + (1) * w 99 + (((y^2) / ((x^2) * (z^2)))) * w 110 + (1) * w 129 + (((y^2) / ((x^2) * (z^2)))) * w 140

def sourceRows98 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((y^2) / ((x^2) * (z^2)))) * w 10 + (1) * w 21 + (((y^2) / ((x^2) * (z^2)))) * w 40 + (1) * w 51 + (((y^2) / ((x^2) * (z^2)))) * w 70 + (1) * w 81 + (1) * w 111 + (((y^2) / ((x^2) * (z^2)))) * w 130

def sourceRows99 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 16 + ((1 / ((y^2) * (z^2)))) * w 30 + (1) * w 46 + ((1 / ((y^2) * (z^2)))) * w 60 + ((1 / ((y^2) * (z^2)))) * w 90 + (1) * w 106 + ((1 / ((y^2) * (z^2)))) * w 120 + (1) * w 136

def sourceRows100 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 14 + ((1 / ((y^2) * (z^2)))) * w 30 + (1) * w 44 + ((1 / ((y^2) * (z^2)))) * w 60 + ((1 / ((y^2) * (z^2)))) * w 90 + (1) * w 104 + ((1 / ((y^2) * (z^2)))) * w 120 + (1) * w 134

def sourceRows101 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 4 + ((((-1) * a) / x)) * w 8 + ((1 / (x^2))) * w 16 + (1) * w 79

def sourceRows102 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 12 + ((((-1) * a) / x)) * w 24 + ((1 / (x^2))) * w 48 + (1) * w 87

def sourceRows103 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 11 + ((((-1) * a) / x)) * w 22 + ((1 / (x^2))) * w 44 + (1) * w 86

def sourceRows104 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 13 + ((((-1) * a) / x)) * w 26 + ((1 / (x^2))) * w 52 + (1) * w 88

def sourceRows105 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 19 + ((((-1) * a) / x)) * w 38 + ((1 / (x^2))) * w 76 + (1) * w 94

def sourceRows106 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 21 + ((((-1) * a) / x)) * w 42 + ((1 / (x^2))) * w 84 + (1) * w 96

def sourceRows107 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 24 + ((((-1) * a) / x)) * w 48 + ((1 / (x^2))) * w 96 + (1) * w 99

def sourceRows108 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 7 + ((((-1) * a) / x)) * w 14 + ((1 / (x^2))) * w 28 + (1) * w 82

def sourceRows109 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 56 + ((1 / (x^2))) * w 74 + ((((-1) * a) / x)) * w 112 + (1) * w 131

def sourceRows110 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 62 + ((1 / (x^2))) * w 98 + ((((-1) * a) / x)) * w 124 + (1) * w 137

def sourceRows111 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 64 + ((1 / (x^2))) * w 106 + ((((-1) * a) / x)) * w 128 + (1) * w 139

def sourceRows112 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 68 + ((1 / (x^2))) * w 122 + ((((-1) * a) / x)) * w 136 + (1) * w 143

def sourceRows113 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 6 + ((((-1) * b) / y)) * w 18 + ((1 / (y^2))) * w 54 + (1) * w 56 + (1) * w 106

def sourceRows114 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 8 + ((((-1) * b) / y)) * w 24 + (1) * w 58 + ((1 / (y^2))) * w 72 + (1) * w 108

def sourceRows115 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 11 + ((((-1) * b) / y)) * w 33 + (1) * w 61 + ((1 / (y^2))) * w 99 + (1) * w 111

def sourceRows116 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 12 + ((((-1) * b) / y)) * w 36 + (1) * w 62 + ((1 / (y^2))) * w 108 + (1) * w 112

def sourceRows117 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 13 + ((((-1) * b) / y)) * w 39 + (1) * w 63 + (1) * w 113 + ((1 / (y^2))) * w 117

def sourceRows118 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 14 + ((((-1) * b) / y)) * w 42 + (1) * w 64 + (1) * w 114 + ((1 / (y^2))) * w 126

def sourceRows119 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 8 + ((1 / (z^2))) * w 10 + (1) * w 18 + ((1 / (z^2))) * w 30 + (1) * w 38 + ((1 / (z^2))) * w 40 + ((1 / (z^2))) * w 60 + (1) * w 68 + ((1 / (z^2))) * w 70 + (1) * w 78 + ((1 / (z^2))) * w 90 + (1) * w 108 + ((1 / (z^2))) * w 120 + (1) * w 128 + ((1 / (z^2))) * w 130 + (1) * w 138

def sourceRows120 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 28 + (1) * w 78 + ((((-1) * b) / y)) * w 84 + ((1 / (y^2))) * w 102 + (1) * w 128

def sourceRows121 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 28 + ((1 / ((y^2) * (z^2)))) * w 30 + (1) * w 58 + ((1 / ((y^2) * (z^2)))) * w 60 + (1) * w 88 + ((1 / ((y^2) * (z^2)))) * w 90 + (1) * w 118 + ((1 / ((y^2) * (z^2)))) * w 120

def sourceRows122 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (z^2)))) * w 10 + (1) * w 11 + (1) * w 21 + ((1 / ((x^2) * (z^2)))) * w 30 + ((1 / ((x^2) * (z^2)))) * w 40 + (1) * w 41 + ((1 / ((x^2) * (z^2)))) * w 60 + ((1 / ((x^2) * (z^2)))) * w 70 + (1) * w 71 + (1) * w 81 + ((1 / ((x^2) * (z^2)))) * w 90 + (1) * w 111 + ((1 / ((x^2) * (z^2)))) * w 120 + ((1 / ((x^2) * (z^2)))) * w 130 + (1) * w 131 + (1) * w 141

def sourceRows123 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 12 + ((1 / (z^2))) * w 20 + (1) * w 22 + ((1 / (z^2))) * w 30 + (1) * w 42 + ((1 / (z^2))) * w 60 + (1) * w 72 + ((1 / (z^2))) * w 80 + (1) * w 82 + ((1 / (z^2))) * w 90 + ((1 / (z^2))) * w 110 + (1) * w 112 + ((1 / (z^2))) * w 120 + (1) * w 132 + ((1 / (z^2))) * w 140 + (1) * w 142

def sourceRows124 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 22 + ((1 / (y^2))) * w 48 + ((((-1) * b) / y)) * w 66 + (1) * w 72 + (1) * w 122

def sourceRows125 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((x^2) / ((y^2) * (z^2)))) * w 15 + (1) * w 26 + (((x^2) / ((y^2) * (z^2)))) * w 45 + (1) * w 56 + (1) * w 86 + (((x^2) / ((y^2) * (z^2)))) * w 105 + (1) * w 116 + (((x^2) / ((y^2) * (z^2)))) * w 135

def sourceRows126 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 14 + ((((-1) * a) / x)) * w 28 + ((1 / (x^2))) * w 56 + (1) * w 89

def sourceRows127 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 22 + ((((-1) * a) / x)) * w 44 + ((1 / (x^2))) * w 88 + (1) * w 97

def sourceRows128 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 28 + ((((-1) * a) / x)) * w 56 + (1) * w 103 + ((1 / (x^2))) * w 112

def sourceRows129 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 29 + ((((-1) * a) / x)) * w 58 + (1) * w 104 + ((1 / (x^2))) * w 116

def sourceRows130 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 31 + ((((-1) * a) / x)) * w 62 + (1) * w 106 + ((1 / (x^2))) * w 124

def sourceRows131 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 22 + (1) * w 43 + ((((-1) * a) / x)) * w 86 + (1) * w 118

def sourceRows132 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 26 + (1) * w 44 + ((((-1) * a) / x)) * w 88 + (1) * w 119

def sourceRows133 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 29 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 30 + (1) * w 59 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 60 + (1) * w 89 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 90 + (1) * w 119 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 120

def sourceRows134 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 52 + ((1 / (x^2))) * w 58 + ((((-1) * a) / x)) * w 104 + (1) * w 127

def sourceRows135 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 53 + ((1 / (x^2))) * w 62 + ((((-1) * a) / x)) * w 106 + (1) * w 128

def sourceRows136 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 58 + ((1 / (x^2))) * w 82 + ((((-1) * a) / x)) * w 116 + (1) * w 133

def sourceRows137 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 61 + ((1 / (x^2))) * w 94 + ((((-1) * a) / x)) * w 122 + (1) * w 136

def sourceRows138 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((x^2) / ((y^2) * (z^2)))) * w 15 + (1) * w 34 + (((x^2) / ((y^2) * (z^2)))) * w 45 + (1) * w 64 + (1) * w 94 + (((x^2) / ((y^2) * (z^2)))) * w 105 + (1) * w 124 + (((x^2) / ((y^2) * (z^2)))) * w 135

def sourceRows139 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 9 + (1) * w 19 + ((1 / ((x^2) * (z^2)))) * w 20 + ((1 / ((x^2) * (z^2)))) * w 30 + (1) * w 39 + ((1 / ((x^2) * (z^2)))) * w 60 + (1) * w 69 + (1) * w 79 + ((1 / ((x^2) * (z^2)))) * w 80 + ((1 / ((x^2) * (z^2)))) * w 90 + (1) * w 109 + ((1 / ((x^2) * (z^2)))) * w 110 + ((1 / ((x^2) * (z^2)))) * w 120 + (1) * w 129 + (1) * w 139 + ((1 / ((x^2) * (z^2)))) * w 140

def sourceRows140 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (y^2)))) * w 0 + ((1 / ((x^2) * (y^2)))) * w 6 + (1) * w 7 + ((1 / ((x^2) * (y^2)))) * w 12 + (1) * w 13 + ((1 / ((x^2) * (y^2)))) * w 18 + (1) * w 19 + (1) * w 25 + ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 36 + (1) * w 37 + ((1 / ((x^2) * (y^2)))) * w 42 + (1) * w 43 + ((1 / ((x^2) * (y^2)))) * w 48 + (1) * w 49 + (1) * w 55 + ((1 / ((x^2) * (y^2)))) * w 60 + ((1 / ((x^2) * (y^2)))) * w 66 + (1) * w 67 + ((1 / ((x^2) * (y^2)))) * w 72 + (1) * w 73 + ((1 / ((x^2) * (y^2)))) * w 78 + (1) * w 79 + (1) * w 85 + ((1 / ((x^2) * (y^2)))) * w 90 + ((1 / ((x^2) * (y^2)))) * w 96 + (1) * w 97 + ((1 / ((x^2) * (y^2)))) * w 102 + (1) * w 103 + ((1 / ((x^2) * (y^2)))) * w 108 + (1) * w 109 + (1) * w 115 + ((1 / ((x^2) * (y^2)))) * w 120 + ((1 / ((x^2) * (y^2)))) * w 126 + (1) * w 127 + ((1 / ((x^2) * (y^2)))) * w 132 + (1) * w 133 + ((1 / ((x^2) * (y^2)))) * w 138 + (1) * w 139 + (1) * w 145

def sourceRows141 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 38 + (1) * w 47 + ((((-1) * a) / x)) * w 94 + (1) * w 122

def sourceRows142 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 7 + ((((-1) * b) / y)) * w 21 + (1) * w 57 + ((1 / (y^2))) * w 63 + (1) * w 107

def sourceRows143 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 32 + ((((-1) * a) / x)) * w 64 + (1) * w 107 + ((1 / (x^2))) * w 128

def sourceRows144 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((y^2) * (z^2)))) * w 30 + (1) * w 32 + ((1 / ((y^2) * (z^2)))) * w 60 + (1) * w 62 + ((1 / ((y^2) * (z^2)))) * w 90 + (1) * w 92 + ((1 / ((y^2) * (z^2)))) * w 120 + (1) * w 122

def sourceRows145 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 8 + ((((-1) * a) / x)) * w 16 + ((1 / (x^2))) * w 32 + (1) * w 83

def sourceRows146 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 16 + ((((-1) * a) / x)) * w 32 + ((1 / (x^2))) * w 64 + (1) * w 91

def sourceRows147 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (y^2) * (z^2)))) * w 30 + (1) * w 31 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 60 + (1) * w 61 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 90 + (1) * w 91 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 120 + (1) * w 121

def sourceRows148 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 17 + ((((-1) * a) / x)) * w 34 + ((1 / (x^2))) * w 68 + (1) * w 92

def sourceRows149 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (y^2)))) * w 0 + (1) * w 5 + (1) * w 11 + ((1 / ((x^2) * (y^2)))) * w 12 + (1) * w 17 + ((1 / ((x^2) * (y^2)))) * w 18 + (1) * w 23 + ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 30 + (1) * w 35 + (1) * w 41 + ((1 / ((x^2) * (y^2)))) * w 42 + (1) * w 47 + ((1 / ((x^2) * (y^2)))) * w 48 + (1) * w 53 + ((1 / ((x^2) * (y^2)))) * w 54 + ((1 / ((x^2) * (y^2)))) * w 60 + (1) * w 65 + (1) * w 71 + ((1 / ((x^2) * (y^2)))) * w 72 + (1) * w 77 + ((1 / ((x^2) * (y^2)))) * w 78 + (1) * w 83 + ((1 / ((x^2) * (y^2)))) * w 84 + ((1 / ((x^2) * (y^2)))) * w 90 + (1) * w 95 + (1) * w 101 + ((1 / ((x^2) * (y^2)))) * w 102 + (1) * w 107 + ((1 / ((x^2) * (y^2)))) * w 108 + (1) * w 113 + ((1 / ((x^2) * (y^2)))) * w 114 + ((1 / ((x^2) * (y^2)))) * w 120 + (1) * w 125 + (1) * w 131 + ((1 / ((x^2) * (y^2)))) * w 132 + (1) * w 137 + ((1 / ((x^2) * (y^2)))) * w 138 + (1) * w 143 + ((1 / ((x^2) * (y^2)))) * w 144

def sourceRows (x y z a b : ℂ) (w : Fin 150→ℂ) (i : Fin 150) : ℂ :=
  ([sourceRows0 x y z a b w,
    sourceRows1 x y z a b w,
    sourceRows2 x y z a b w,
    sourceRows3 x y z a b w,
    sourceRows4 x y z a b w,
    sourceRows5 x y z a b w,
    sourceRows6 x y z a b w,
    sourceRows7 x y z a b w,
    sourceRows8 x y z a b w,
    sourceRows9 x y z a b w,
    sourceRows10 x y z a b w,
    sourceRows11 x y z a b w,
    sourceRows12 x y z a b w,
    sourceRows13 x y z a b w,
    sourceRows14 x y z a b w,
    sourceRows15 x y z a b w,
    sourceRows16 x y z a b w,
    sourceRows17 x y z a b w,
    sourceRows18 x y z a b w,
    sourceRows19 x y z a b w,
    sourceRows20 x y z a b w,
    sourceRows21 x y z a b w,
    sourceRows22 x y z a b w,
    sourceRows23 x y z a b w,
    sourceRows24 x y z a b w,
    sourceRows25 x y z a b w,
    sourceRows26 x y z a b w,
    sourceRows27 x y z a b w,
    sourceRows28 x y z a b w,
    sourceRows29 x y z a b w,
    sourceRows30 x y z a b w,
    sourceRows31 x y z a b w,
    sourceRows32 x y z a b w,
    sourceRows33 x y z a b w,
    sourceRows34 x y z a b w,
    sourceRows35 x y z a b w,
    sourceRows36 x y z a b w,
    sourceRows37 x y z a b w,
    sourceRows38 x y z a b w,
    sourceRows39 x y z a b w,
    sourceRows40 x y z a b w,
    sourceRows41 x y z a b w,
    sourceRows42 x y z a b w,
    sourceRows43 x y z a b w,
    sourceRows44 x y z a b w,
    sourceRows45 x y z a b w,
    sourceRows46 x y z a b w,
    sourceRows47 x y z a b w,
    sourceRows48 x y z a b w,
    sourceRows49 x y z a b w,
    sourceRows50 x y z a b w,
    sourceRows51 x y z a b w,
    sourceRows52 x y z a b w,
    sourceRows53 x y z a b w,
    sourceRows54 x y z a b w,
    sourceRows55 x y z a b w,
    sourceRows56 x y z a b w,
    sourceRows57 x y z a b w,
    sourceRows58 x y z a b w,
    sourceRows59 x y z a b w,
    sourceRows60 x y z a b w,
    sourceRows61 x y z a b w,
    sourceRows62 x y z a b w,
    sourceRows63 x y z a b w,
    sourceRows64 x y z a b w,
    sourceRows65 x y z a b w,
    sourceRows66 x y z a b w,
    sourceRows67 x y z a b w,
    sourceRows68 x y z a b w,
    sourceRows69 x y z a b w,
    sourceRows70 x y z a b w,
    sourceRows71 x y z a b w,
    sourceRows72 x y z a b w,
    sourceRows73 x y z a b w,
    sourceRows74 x y z a b w,
    sourceRows75 x y z a b w,
    sourceRows76 x y z a b w,
    sourceRows77 x y z a b w,
    sourceRows78 x y z a b w,
    sourceRows79 x y z a b w,
    sourceRows80 x y z a b w,
    sourceRows81 x y z a b w,
    sourceRows82 x y z a b w,
    sourceRows83 x y z a b w,
    sourceRows84 x y z a b w,
    sourceRows85 x y z a b w,
    sourceRows86 x y z a b w,
    sourceRows87 x y z a b w,
    sourceRows88 x y z a b w,
    sourceRows89 x y z a b w,
    sourceRows90 x y z a b w,
    sourceRows91 x y z a b w,
    sourceRows92 x y z a b w,
    sourceRows93 x y z a b w,
    sourceRows94 x y z a b w,
    sourceRows95 x y z a b w,
    sourceRows96 x y z a b w,
    sourceRows97 x y z a b w,
    sourceRows98 x y z a b w,
    sourceRows99 x y z a b w,
    sourceRows100 x y z a b w,
    sourceRows101 x y z a b w,
    sourceRows102 x y z a b w,
    sourceRows103 x y z a b w,
    sourceRows104 x y z a b w,
    sourceRows105 x y z a b w,
    sourceRows106 x y z a b w,
    sourceRows107 x y z a b w,
    sourceRows108 x y z a b w,
    sourceRows109 x y z a b w,
    sourceRows110 x y z a b w,
    sourceRows111 x y z a b w,
    sourceRows112 x y z a b w,
    sourceRows113 x y z a b w,
    sourceRows114 x y z a b w,
    sourceRows115 x y z a b w,
    sourceRows116 x y z a b w,
    sourceRows117 x y z a b w,
    sourceRows118 x y z a b w,
    sourceRows119 x y z a b w,
    sourceRows120 x y z a b w,
    sourceRows121 x y z a b w,
    sourceRows122 x y z a b w,
    sourceRows123 x y z a b w,
    sourceRows124 x y z a b w,
    sourceRows125 x y z a b w,
    sourceRows126 x y z a b w,
    sourceRows127 x y z a b w,
    sourceRows128 x y z a b w,
    sourceRows129 x y z a b w,
    sourceRows130 x y z a b w,
    sourceRows131 x y z a b w,
    sourceRows132 x y z a b w,
    sourceRows133 x y z a b w,
    sourceRows134 x y z a b w,
    sourceRows135 x y z a b w,
    sourceRows136 x y z a b w,
    sourceRows137 x y z a b w,
    sourceRows138 x y z a b w,
    sourceRows139 x y z a b w,
    sourceRows140 x y z a b w,
    sourceRows141 x y z a b w,
    sourceRows142 x y z a b w,
    sourceRows143 x y z a b w,
    sourceRows144 x y z a b w,
    sourceRows145 x y z a b w,
    sourceRows146 x y z a b w,
    sourceRows147 x y z a b w,
    sourceRows148 x y z a b w,
    sourceRows149 x y z a b w] : List ℂ).getD i.val 0

def reducedRows0 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 144

def reducedRows1 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 148

def reducedRows2 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2))) * w 147

def reducedRows3 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((-1)) * w 6

def reducedRows4 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 2

def reducedRows5 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 1

def reducedRows6 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 3

def reducedRows7 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 72

def reducedRows8 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 76

def reducedRows9 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 78

def reducedRows10 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 74

def reducedRows11 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 138

def reducedRows12 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 146

def reducedRows13 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((-1)) * w 12

def reducedRows14 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 4

def reducedRows15 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 0

def reducedRows16 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 75

def reducedRows17 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 149

def reducedRows18 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 120 + (((-1) * (x^2) * (y^2))) * w 145

def reducedRows19 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2) * (y^2))) * w 7 + (1) * w 108

def reducedRows20 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 8 + (1) * w 126

def reducedRows21 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2))) * w 9 + (1) * w 132

def reducedRows22 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135

def reducedRows23 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140

def reducedRows24 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / (x^2))) * w 18 + (1) * w 141

def reducedRows25 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / (y^2))) * w 24 + (1) * w 142

def reducedRows26 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / ((x^2) * (y^2)))) * w 42 + (1) * w 143

def reducedRows27 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 5 + (((-1) / ((x^2) * (y^2)))) * w 30

def reducedRows28 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / ((x^2) * (y^2)))) * w 24 + (1) * w 77

def reducedRows29 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 80 + (((-1) / (y^2))) * w 120

def reducedRows30 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 42 + (((-1) * (x^2) * (y^2))) * w 139

def reducedRows31 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2))) * w 15 + (1) * w 60

def reducedRows32 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((-1)) * w 18 + (1) * w 66

def reducedRows33 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / (x^2))) * w 24 + (1) * w 69

def reducedRows34 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 79 + (((-1) / ((x^2) * (y^2)))) * w 102

def reducedRows35 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 81 + (((-1) / (x^2))) * w 126

def reducedRows36 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 82 + ((((-1) * (x^2)) / (y^2))) * w 129

def reducedRows37 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 84 + ((-1)) * w 132

def reducedRows38 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 87 + ((((-1) * (y^2)) / (x^2))) * w 134

def reducedRows39 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 10 + (1) * w 90

def reducedRows40 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 96 + (((-1) * (y^2))) * w 136

def reducedRows41 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 114 + (((-1) * (x^2) * (y^2))) * w 137

def reducedRows42 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2) * (y^2))) * w 13 + (1) * w 36

def reducedRows43 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (y^2))) * w 14 + (1) * w 54

def reducedRows44 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (y^2)) / (x^2))) * w 16 + (1) * w 63

def reducedRows45 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (x^2)) / (y^2))) * w 21 + (1) * w 68

def reducedRows46 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / (y^2))) * w 30 + (1) * w 70

def reducedRows47 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) / ((x^2) * (y^2)))) * w 48 + (1) * w 71

def reducedRows48 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 73 + (((-1) / ((x^2) * (y^2)))) * w 126

def reducedRows49 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108

def reducedRows50 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120

def reducedRows51 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((y^2) / ((x^2) * (z^2)))) * w 50 + ((1 / (x^2))) * w 132

def reducedRows52 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 18 + (((y^2) / ((x^2) * (z^2)))) * w 100

def reducedRows53 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90

def reducedRows54 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 20 + (((x^2) / (y^2))) * w 105

def reducedRows55 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((x^2) / (y^2))) * w 45 + (1) * w 130

def reducedRows56 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114

def reducedRows57 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125

def reducedRows58 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132

def reducedRows59 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 40 + (1) * w 110

def reducedRows60 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36

def reducedRows61 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114

def reducedRows62 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((x + ((-1) * a) + ((-1) * a * (x^2)) + ((-1) * x * (a^2))) / x)) * w 18 + (1) * w 93

def reducedRows63 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 + (x^2) + (a * x))) * w 18 + (1) * w 111

def reducedRows64 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((-1) + ((-1) * (x^2)) + ((-1) * a * x))) * w 18 + (1) * w 39

def reducedRows65 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((a + ((-1) * x) + (a * (x^2)) + (x * (a^2))) / x)) * w 18 + (1) * w 57

def reducedRows66 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90

def reducedRows67 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110

def reducedRows68 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30

def reducedRows69 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((2 + (x^2) + (x^6) + ((-3) * (x^4)) + ((a^2) * (x^4)) + ((-2) * (a^2) * (x^2)) + ((a^2) * (x^2) * (y^2)) + (a * b * y * (x^3)) + ((-2) * a * b * x * y)) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 95

def reducedRows70 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((2 + ((-1) * (x^2)) + ((-4) * (y^2)) + ((-1) * (x^4) * (y^2)) + (4 * (x^2) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 55

def reducedRows71 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30

def reducedRows72 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45

def reducedRows73 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18

def reducedRows74 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 85

def reducedRows75 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 115

def reducedRows76 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 35

def reducedRows77 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 65

def reducedRows78 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 51 + (1) * w 101

def reducedRows79 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 49 + (1) * w 99

def reducedRows80 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 52 + (1) * w 102

def reducedRows81 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 48 + (1) * w 98

def reducedRows82 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((y^2)) * w 14 + (1) * w 104

def reducedRows83 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 46 + (1) * w 96

def reducedRows84 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 96 + (1) * w 126

def reducedRows85 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((y^2)) * w 14 + (1) * w 24

def reducedRows86 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 42 + (1) * w 102

def reducedRows87 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 48 + (1) * w 108

def reducedRows88 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 26 + (1) * w 126

def reducedRows89 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 24 + (1) * w 124

def reducedRows90 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126

def reducedRows91 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 33 + (1) * w 108

def reducedRows92 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 37 + (1) * w 112

def reducedRows93 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 38 + (1) * w 113

def reducedRows94 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 42 + (1) * w 117

def reducedRows95 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((y^2) / (x^2))) * w 16 + ((-1)) * w 108 + (1) * w 123

def reducedRows96 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 27 + ((-1)) * w 42 + (1) * w 87

def reducedRows97 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 24 + (((y^2) / (x^2))) * w 82 + (1) * w 99

def reducedRows98 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 21 + (((-1) / (x^2))) * w 24 + ((-1)) * w 101

def reducedRows99 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 16 + (((1 + ((-1) * (y^2))) / (y^2))) * w 24 + (1) * w 106

def reducedRows100 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) + (y^2)) / (y^2))) * w 24 + (1) * w 44 + (((x^2) / (y^2))) * w 87

def reducedRows101 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42

def reducedRows102 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / (x^2))) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 44 + (((-1) / (x^2))) * w 108

def reducedRows103 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * a) / x)) * w 22 + (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 86

def reducedRows104 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * a) / x)) * w 24 + ((1 / (x^2))) * w 42 + (1) * w 88

def reducedRows105 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 19 + ((((-1) * a) / x)) * w 38 + (1) * w 94

def reducedRows106 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42

def reducedRows107 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108

def reducedRows108 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((a + (x^3)) / (x * (y^2)))) * w 24 + ((1 / (x^2))) * w 28 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 108

def reducedRows109 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 56 + ((((-1) * a) / x)) * w 112 + (1) * w 131

def reducedRows110 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((a / x)) * w 24 + (1) * w 62 + ((1 / (x^2))) * w 108

def reducedRows111 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) + (y^2) + (a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 64 + ((((-1) * a) / x)) * w 128

def reducedRows112 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((((-1) * a) + ((-1) * (x^3))) / (x * (y^2)))) * w 24 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 42 + ((1 / (x^2))) * w 122

def reducedRows113 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-2) + (y^2) + (a * x)) / (y^2))) * w 24 + (((-1) / (y^2))) * w 42 + (1) * w 56

def reducedRows114 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) + ((-1) * b * y)) / (y^2))) * w 24 + (1) * w 58 + (1) * w 108

def reducedRows115 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 24 + (1) * w 61 + (((1 + ((-1) * a * x) + (b * y * (x^2))) / ((x^2) * (y^2)))) * w 108

def reducedRows116 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * a) / x)) * w 24 + ((((x^2) + ((-1) * (y^2))) / ((x^2) * (y^2)))) * w 108 + (1) * w 112

def reducedRows117 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((-1) * a) / x)) * w 24 + ((-1)) * w 38 + ((((y^2) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 42

def reducedRows118 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128

def reducedRows119 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128

def reducedRows120 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128

def reducedRows121 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((a * (x^2)) + ((a^2) * (x^5)) + ((-1) * a * (x^4)) + ((-1) * (a^2) * (x^7)) + (a * b * (y^3)) + ((a^2) * (x^7) * (y^2)) + ((a^3) * (x^2) * (y^2)) + ((a^3) * (x^4) * (y^2)) + ((a^4) * (x^5) * (y^2)) + ((b^2) * (x^3) * (y^2)) + ((b^2) * (x^3) * (y^4)) + ((-1) * a * (x^2) * (y^2)) + ((-1) * a * (x^2) * (y^4)) + ((-1) * a * (x^4) * (y^2)) + ((-1) * b * y * (x^5)) + ((-1) * b * (x^5) * (y^3)) + ((-1) * (a^2) * (x^3) * (y^2)) + ((-2) * (a^2) * (x^5) * (y^2)) + (a * (b^2) * (x^6) * (y^2)) + (b * y * (a^2) * (x^3)) + (b * y * (a^3) * (x^6)) + (b * (a^2) * (x^3) * (y^3)) + ((-1) * a * b * y * (x^2)) + ((-1) * a * b * y * (x^8)) + ((-1) * a * b * (x^2) * (y^3)) + ((-1) * b * y * (a^2) * (x^5))) / (x * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42 + (1) * w 118

def reducedRows122 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 41 + (((((-1) * (x^5)) + (2 * (x^7)) + (a * (y^6)) + ((a^2) * (x^9)) + ((a^3) * (x^8)) + ((a^4) * (x^7)) + ((a^4) * (x^11)) + ((x^5) * (y^4)) + ((-1) * a * (y^4)) + ((-1) * (a^2) * (x^11)) + ((-4) * (a^2) * (x^7)) + ((-2) * a * (x^8)) + ((-2) * (a^3) * (x^6)) + ((-2) * (a^3) * (x^10)) + (2 * a * (x^6)) + (2 * a * (x^10)) + (2 * (a^2) * (x^5)) + (2 * (x^7) * (y^2)) + (a * (x^2) * (y^2)) + (a * (x^4) * (y^4)) + (a * (x^6) * (y^2)) + (a * (x^8) * (y^2)) + (x * (a^2) * (y^4)) + ((a^2) * (x^3) * (y^4)) + ((a^2) * (x^7) * (y^2)) + ((a^2) * (x^9) * (y^4)) + ((a^3) * (x^6) * (y^4)) + ((a^3) * (x^10) * (y^2)) + ((a^4) * (x^5) * (y^4)) + ((a^4) * (x^7) * (y^4)) + ((a^5) * (x^8) * (y^2)) + ((-1) * a * (x^4) * (y^6)) + ((-1) * a * (x^10) * (y^2)) + ((-1) * b * (x^5) * (y^3)) + ((-1) * b * (x^5) * (y^5)) + ((-1) * (a^2) * (x^5) * (y^2)) + ((-1) * (a^2) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^2) * (y^4)) + ((-1) * (a^4) * (x^7) * (y^2)) + ((-3) * (a^2) * (x^3) * (y^2)) + ((-3) * (a^2) * (x^5) * (y^4)) + ((-2) * a * (x^4) * (y^2)) + ((-2) * a * (x^6) * (y^4)) + ((-2) * b * y * (x^7)) + ((-2) * b * (x^7) * (y^3)) + ((-2) * (a^2) * (x^9) * (y^2)) + ((-2) * (a^3) * (x^8) * (y^2)) + (3 * (a^3) * (x^4) * (y^2)) + (a * b * (x^4) * (y^3)) + (a * b * (x^6) * (y^3)) + (b * y * (a^2) * (x^7)) + (b * y * (a^2) * (x^11)) + (b * (a^2) * (x^3) * (y^5)) + (b * (a^2) * (x^5) * (y^5)) + (b * (a^3) * (x^8) * (y^3)) + ((-1) * a * b * y * (x^6)) + ((-1) * a * b * y * (x^10)) + ((-1) * a * b * (x^8) * (y^3)) + ((-1) * b * (a^2) * (x^5) * (y^3))) / ((x^5) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42

def reducedRows123 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 22 + ((((y^6) + ((-1) * (y^4)) + (a * (x^5)) + ((a^2) * (x^8)) + ((a^2) * (x^10)) + ((a^3) * (x^9)) + ((x^2) * (y^2)) + ((x^2) * (y^4)) + ((-1) * a * (x^9)) + ((-1) * (a^4) * (x^8)) + ((-1) * (x^4) * (y^2)) + ((-1) * (x^4) * (y^6)) + ((-3) * (a^2) * (x^6)) + ((-2) * a * (x^7)) + ((-2) * (x^6) * (y^2)) + ((-2) * (x^6) * (y^4)) + (3 * (a^3) * (x^7)) + (a * x * (y^4)) + (a * (x^9) * (y^4)) + (b * y * (x^10)) + (b * (x^4) * (y^3)) + ((a^2) * (x^6) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((a^3) * (x^5) * (y^4)) + ((a^3) * (x^7) * (y^4)) + ((a^4) * (x^8) * (y^2)) + ((-1) * a * (x^7) * (y^4)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^2) * (x^8) * (y^2)) + ((-1) * (a^3) * (x^7) * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * a * (x^5) * (y^4)) + ((-2) * a * (x^9) * (y^2)) + ((-2) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^3) * (y^4)) + (2 * a * (x^5) * (y^2)) + (2 * b * (x^6) * (y^3)) + (2 * (a^2) * (x^6) * (y^2)) + (3 * a * (x^7) * (y^2)) + (4 * (a^2) * (x^4) * (y^2)) + (a * b * (x^3) * (y^5)) + (a * b * (x^5) * (y^5)) + (b * (a^2) * (x^6) * (y^3)) + (b * (a^2) * (x^8) * (y^3)) + ((-1) * a * b * (x^5) * (y^3)) + ((-1) * b * y * (a^2) * (x^8)) + (2 * a * b * y * (x^7)) + (2 * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42

def reducedRows124 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42

def reducedRows125 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 116

def reducedRows126 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 89

def reducedRows127 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 97

def reducedRows128 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 103

def reducedRows129 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 29

def reducedRows130 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 31

def reducedRows131 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 43

def reducedRows132 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 119

def reducedRows133 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 59

def reducedRows134 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 127

def reducedRows135 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 53

def reducedRows136 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 133

def reducedRows137 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := ((1 / (x^2))) * w 94

def reducedRows138 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 34

def reducedRows139 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 109

def reducedRows140 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 67

def reducedRows141 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 47

def reducedRows142 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 107

def reducedRows143 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 32

def reducedRows144 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 92

def reducedRows145 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 83

def reducedRows146 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 91

def reducedRows147 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 121

def reducedRows148 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 17

def reducedRows149 (x y z a b : ℂ) (w : Fin 150→ℂ) : ℂ := (1) * w 23

def reducedRows (x y z a b : ℂ) (w : Fin 150→ℂ) (i : Fin 150) : ℂ :=
  ([reducedRows0 x y z a b w,
    reducedRows1 x y z a b w,
    reducedRows2 x y z a b w,
    reducedRows3 x y z a b w,
    reducedRows4 x y z a b w,
    reducedRows5 x y z a b w,
    reducedRows6 x y z a b w,
    reducedRows7 x y z a b w,
    reducedRows8 x y z a b w,
    reducedRows9 x y z a b w,
    reducedRows10 x y z a b w,
    reducedRows11 x y z a b w,
    reducedRows12 x y z a b w,
    reducedRows13 x y z a b w,
    reducedRows14 x y z a b w,
    reducedRows15 x y z a b w,
    reducedRows16 x y z a b w,
    reducedRows17 x y z a b w,
    reducedRows18 x y z a b w,
    reducedRows19 x y z a b w,
    reducedRows20 x y z a b w,
    reducedRows21 x y z a b w,
    reducedRows22 x y z a b w,
    reducedRows23 x y z a b w,
    reducedRows24 x y z a b w,
    reducedRows25 x y z a b w,
    reducedRows26 x y z a b w,
    reducedRows27 x y z a b w,
    reducedRows28 x y z a b w,
    reducedRows29 x y z a b w,
    reducedRows30 x y z a b w,
    reducedRows31 x y z a b w,
    reducedRows32 x y z a b w,
    reducedRows33 x y z a b w,
    reducedRows34 x y z a b w,
    reducedRows35 x y z a b w,
    reducedRows36 x y z a b w,
    reducedRows37 x y z a b w,
    reducedRows38 x y z a b w,
    reducedRows39 x y z a b w,
    reducedRows40 x y z a b w,
    reducedRows41 x y z a b w,
    reducedRows42 x y z a b w,
    reducedRows43 x y z a b w,
    reducedRows44 x y z a b w,
    reducedRows45 x y z a b w,
    reducedRows46 x y z a b w,
    reducedRows47 x y z a b w,
    reducedRows48 x y z a b w,
    reducedRows49 x y z a b w,
    reducedRows50 x y z a b w,
    reducedRows51 x y z a b w,
    reducedRows52 x y z a b w,
    reducedRows53 x y z a b w,
    reducedRows54 x y z a b w,
    reducedRows55 x y z a b w,
    reducedRows56 x y z a b w,
    reducedRows57 x y z a b w,
    reducedRows58 x y z a b w,
    reducedRows59 x y z a b w,
    reducedRows60 x y z a b w,
    reducedRows61 x y z a b w,
    reducedRows62 x y z a b w,
    reducedRows63 x y z a b w,
    reducedRows64 x y z a b w,
    reducedRows65 x y z a b w,
    reducedRows66 x y z a b w,
    reducedRows67 x y z a b w,
    reducedRows68 x y z a b w,
    reducedRows69 x y z a b w,
    reducedRows70 x y z a b w,
    reducedRows71 x y z a b w,
    reducedRows72 x y z a b w,
    reducedRows73 x y z a b w,
    reducedRows74 x y z a b w,
    reducedRows75 x y z a b w,
    reducedRows76 x y z a b w,
    reducedRows77 x y z a b w,
    reducedRows78 x y z a b w,
    reducedRows79 x y z a b w,
    reducedRows80 x y z a b w,
    reducedRows81 x y z a b w,
    reducedRows82 x y z a b w,
    reducedRows83 x y z a b w,
    reducedRows84 x y z a b w,
    reducedRows85 x y z a b w,
    reducedRows86 x y z a b w,
    reducedRows87 x y z a b w,
    reducedRows88 x y z a b w,
    reducedRows89 x y z a b w,
    reducedRows90 x y z a b w,
    reducedRows91 x y z a b w,
    reducedRows92 x y z a b w,
    reducedRows93 x y z a b w,
    reducedRows94 x y z a b w,
    reducedRows95 x y z a b w,
    reducedRows96 x y z a b w,
    reducedRows97 x y z a b w,
    reducedRows98 x y z a b w,
    reducedRows99 x y z a b w,
    reducedRows100 x y z a b w,
    reducedRows101 x y z a b w,
    reducedRows102 x y z a b w,
    reducedRows103 x y z a b w,
    reducedRows104 x y z a b w,
    reducedRows105 x y z a b w,
    reducedRows106 x y z a b w,
    reducedRows107 x y z a b w,
    reducedRows108 x y z a b w,
    reducedRows109 x y z a b w,
    reducedRows110 x y z a b w,
    reducedRows111 x y z a b w,
    reducedRows112 x y z a b w,
    reducedRows113 x y z a b w,
    reducedRows114 x y z a b w,
    reducedRows115 x y z a b w,
    reducedRows116 x y z a b w,
    reducedRows117 x y z a b w,
    reducedRows118 x y z a b w,
    reducedRows119 x y z a b w,
    reducedRows120 x y z a b w,
    reducedRows121 x y z a b w,
    reducedRows122 x y z a b w,
    reducedRows123 x y z a b w,
    reducedRows124 x y z a b w,
    reducedRows125 x y z a b w,
    reducedRows126 x y z a b w,
    reducedRows127 x y z a b w,
    reducedRows128 x y z a b w,
    reducedRows129 x y z a b w,
    reducedRows130 x y z a b w,
    reducedRows131 x y z a b w,
    reducedRows132 x y z a b w,
    reducedRows133 x y z a b w,
    reducedRows134 x y z a b w,
    reducedRows135 x y z a b w,
    reducedRows136 x y z a b w,
    reducedRows137 x y z a b w,
    reducedRows138 x y z a b w,
    reducedRows139 x y z a b w,
    reducedRows140 x y z a b w,
    reducedRows141 x y z a b w,
    reducedRows142 x y z a b w,
    reducedRows143 x y z a b w,
    reducedRows144 x y z a b w,
    reducedRows145 x y z a b w,
    reducedRows146 x y z a b w,
    reducedRows147 x y z a b w,
    reducedRows148 x y z a b w,
    reducedRows149 x y z a b w] : List ℂ).getD i.val 0

end QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveContinuationNegativeBackSubstitutionV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative

theorem reduced_rows_kernel (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ) (h : ∀ i, reducedRows x y z a b w i=0) : w=0 := by
  have hw23 : w 23=0 := by
    have hi := h (149:Fin 150)
    change (1) * w 23=0 at hi
    simpa only [one_mul] using hi
  have hw17 : w 17=0 := by
    have hi := h (148:Fin 150)
    change (1) * w 17=0 at hi
    simpa only [one_mul] using hi
  have hw121 : w 121=0 := by
    have hi := h (147:Fin 150)
    change (1) * w 121=0 at hi
    simpa only [one_mul] using hi
  have hw91 : w 91=0 := by
    have hi := h (146:Fin 150)
    change (1) * w 91=0 at hi
    simpa only [one_mul] using hi
  have hw83 : w 83=0 := by
    have hi := h (145:Fin 150)
    change (1) * w 83=0 at hi
    simpa only [one_mul] using hi
  have hw92 : w 92=0 := by
    have hi := h (144:Fin 150)
    change (1) * w 92=0 at hi
    simpa only [one_mul] using hi
  have hw32 : w 32=0 := by
    have hi := h (143:Fin 150)
    change (1) * w 32=0 at hi
    simpa only [one_mul] using hi
  have hw107 : w 107=0 := by
    have hi := h (142:Fin 150)
    change (1) * w 107=0 at hi
    simpa only [one_mul] using hi
  have hw47 : w 47=0 := by
    have hi := h (141:Fin 150)
    change (1) * w 47=0 at hi
    simpa only [one_mul] using hi
  have hw67 : w 67=0 := by
    have hi := h (140:Fin 150)
    change (1) * w 67=0 at hi
    simpa only [one_mul] using hi
  have hw109 : w 109=0 := by
    have hi := h (139:Fin 150)
    change (1) * w 109=0 at hi
    simpa only [one_mul] using hi
  have hw34 : w 34=0 := by
    have hi := h (138:Fin 150)
    change (1) * w 34=0 at hi
    simpa only [one_mul] using hi
  have hw94 : w 94=0 := by
    have hi := h (137:Fin 150)
    change ((1 / (x^2))) * w 94=0 at hi
    have hn : ((1 / (x^2)):ℂ)≠0 := by
      have he : ((1 / (x^2)):ℂ)=1/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw133 : w 133=0 := by
    have hi := h (136:Fin 150)
    change (1) * w 133=0 at hi
    simpa only [one_mul] using hi
  have hw53 : w 53=0 := by
    have hi := h (135:Fin 150)
    change (1) * w 53=0 at hi
    simpa only [one_mul] using hi
  have hw127 : w 127=0 := by
    have hi := h (134:Fin 150)
    change (1) * w 127=0 at hi
    simpa only [one_mul] using hi
  have hw59 : w 59=0 := by
    have hi := h (133:Fin 150)
    change (1) * w 59=0 at hi
    simpa only [one_mul] using hi
  have hw119 : w 119=0 := by
    have hi := h (132:Fin 150)
    change (1) * w 119=0 at hi
    simpa only [one_mul] using hi
  have hw43 : w 43=0 := by
    have hi := h (131:Fin 150)
    change (1) * w 43=0 at hi
    simpa only [one_mul] using hi
  have hw31 : w 31=0 := by
    have hi := h (130:Fin 150)
    change (1) * w 31=0 at hi
    simpa only [one_mul] using hi
  have hw29 : w 29=0 := by
    have hi := h (129:Fin 150)
    change (1) * w 29=0 at hi
    simpa only [one_mul] using hi
  have hw103 : w 103=0 := by
    have hi := h (128:Fin 150)
    change (1) * w 103=0 at hi
    simpa only [one_mul] using hi
  have hw97 : w 97=0 := by
    have hi := h (127:Fin 150)
    change (1) * w 97=0 at hi
    simpa only [one_mul] using hi
  have hw89 : w 89=0 := by
    have hi := h (126:Fin 150)
    change (1) * w 89=0 at hi
    simpa only [one_mul] using hi
  have hw116 : w 116=0 := by
    have hi := h (125:Fin 150)
    change (1) * w 116=0 at hi
    simpa only [one_mul] using hi
  have hw42 : w 42=0 := by
    have hi := h (124:Fin 150)
    change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at hi
    have hn : ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2))))):ℂ)≠0 := by
      have he : ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2))))):ℂ)=((1 * ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))) * ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3))))/(((1 * (y^2)) * (x^4)) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hP5) hP0) (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (pow_ne_zero 4 hx)) hP3)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw22 : w 22=0 := by
    have hi := h (123:Fin 150)
    change (1) * w 22 + ((((y^6) + ((-1) * (y^4)) + (a * (x^5)) + ((a^2) * (x^8)) + ((a^2) * (x^10)) + ((a^3) * (x^9)) + ((x^2) * (y^2)) + ((x^2) * (y^4)) + ((-1) * a * (x^9)) + ((-1) * (a^4) * (x^8)) + ((-1) * (x^4) * (y^2)) + ((-1) * (x^4) * (y^6)) + ((-3) * (a^2) * (x^6)) + ((-2) * a * (x^7)) + ((-2) * (x^6) * (y^2)) + ((-2) * (x^6) * (y^4)) + (3 * (a^3) * (x^7)) + (a * x * (y^4)) + (a * (x^9) * (y^4)) + (b * y * (x^10)) + (b * (x^4) * (y^3)) + ((a^2) * (x^6) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((a^3) * (x^5) * (y^4)) + ((a^3) * (x^7) * (y^4)) + ((a^4) * (x^8) * (y^2)) + ((-1) * a * (x^7) * (y^4)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^2) * (x^8) * (y^2)) + ((-1) * (a^3) * (x^7) * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * a * (x^5) * (y^4)) + ((-2) * a * (x^9) * (y^2)) + ((-2) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^3) * (y^4)) + (2 * a * (x^5) * (y^2)) + (2 * b * (x^6) * (y^3)) + (2 * (a^2) * (x^6) * (y^2)) + (3 * a * (x^7) * (y^2)) + (4 * (a^2) * (x^4) * (y^2)) + (a * b * (x^3) * (y^5)) + (a * b * (x^5) * (y^5)) + (b * (a^2) * (x^6) * (y^3)) + (b * (a^2) * (x^8) * (y^3)) + ((-1) * a * b * (x^5) * (y^3)) + ((-1) * b * y * (a^2) * (x^8)) + (2 * a * b * y * (x^7)) + (2 * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw41 : w 41=0 := by
    have hi := h (122:Fin 150)
    change (1) * w 41 + (((((-1) * (x^5)) + (2 * (x^7)) + (a * (y^6)) + ((a^2) * (x^9)) + ((a^3) * (x^8)) + ((a^4) * (x^7)) + ((a^4) * (x^11)) + ((x^5) * (y^4)) + ((-1) * a * (y^4)) + ((-1) * (a^2) * (x^11)) + ((-4) * (a^2) * (x^7)) + ((-2) * a * (x^8)) + ((-2) * (a^3) * (x^6)) + ((-2) * (a^3) * (x^10)) + (2 * a * (x^6)) + (2 * a * (x^10)) + (2 * (a^2) * (x^5)) + (2 * (x^7) * (y^2)) + (a * (x^2) * (y^2)) + (a * (x^4) * (y^4)) + (a * (x^6) * (y^2)) + (a * (x^8) * (y^2)) + (x * (a^2) * (y^4)) + ((a^2) * (x^3) * (y^4)) + ((a^2) * (x^7) * (y^2)) + ((a^2) * (x^9) * (y^4)) + ((a^3) * (x^6) * (y^4)) + ((a^3) * (x^10) * (y^2)) + ((a^4) * (x^5) * (y^4)) + ((a^4) * (x^7) * (y^4)) + ((a^5) * (x^8) * (y^2)) + ((-1) * a * (x^4) * (y^6)) + ((-1) * a * (x^10) * (y^2)) + ((-1) * b * (x^5) * (y^3)) + ((-1) * b * (x^5) * (y^5)) + ((-1) * (a^2) * (x^5) * (y^2)) + ((-1) * (a^2) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^2) * (y^4)) + ((-1) * (a^4) * (x^7) * (y^2)) + ((-3) * (a^2) * (x^3) * (y^2)) + ((-3) * (a^2) * (x^5) * (y^4)) + ((-2) * a * (x^4) * (y^2)) + ((-2) * a * (x^6) * (y^4)) + ((-2) * b * y * (x^7)) + ((-2) * b * (x^7) * (y^3)) + ((-2) * (a^2) * (x^9) * (y^2)) + ((-2) * (a^3) * (x^8) * (y^2)) + (3 * (a^3) * (x^4) * (y^2)) + (a * b * (x^4) * (y^3)) + (a * b * (x^6) * (y^3)) + (b * y * (a^2) * (x^7)) + (b * y * (a^2) * (x^11)) + (b * (a^2) * (x^3) * (y^5)) + (b * (a^2) * (x^5) * (y^5)) + (b * (a^3) * (x^8) * (y^3)) + ((-1) * a * b * y * (x^6)) + ((-1) * a * b * y * (x^10)) + ((-1) * a * b * (x^8) * (y^3)) + ((-1) * b * (a^2) * (x^5) * (y^3))) / ((x^5) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw118 : w 118=0 := by
    have hi := h (121:Fin 150)
    change ((((a * (x^2)) + ((a^2) * (x^5)) + ((-1) * a * (x^4)) + ((-1) * (a^2) * (x^7)) + (a * b * (y^3)) + ((a^2) * (x^7) * (y^2)) + ((a^3) * (x^2) * (y^2)) + ((a^3) * (x^4) * (y^2)) + ((a^4) * (x^5) * (y^2)) + ((b^2) * (x^3) * (y^2)) + ((b^2) * (x^3) * (y^4)) + ((-1) * a * (x^2) * (y^2)) + ((-1) * a * (x^2) * (y^4)) + ((-1) * a * (x^4) * (y^2)) + ((-1) * b * y * (x^5)) + ((-1) * b * (x^5) * (y^3)) + ((-1) * (a^2) * (x^3) * (y^2)) + ((-2) * (a^2) * (x^5) * (y^2)) + (a * (b^2) * (x^6) * (y^2)) + (b * y * (a^2) * (x^3)) + (b * y * (a^3) * (x^6)) + (b * (a^2) * (x^3) * (y^3)) + ((-1) * a * b * y * (x^2)) + ((-1) * a * b * y * (x^8)) + ((-1) * a * b * (x^2) * (y^3)) + ((-1) * b * y * (a^2) * (x^5))) / (x * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42 + (1) * w 118=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw128 : w 128=0 := by
    have hi := h (120:Fin 150)
    change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))):ℂ)≠0 := by
      have he : ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))):ℂ)=((-1) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2))))/((1 * (y^2)) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) hP3) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) hP4)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw108 : w 108=0 := by
    have hi := h (119:Fin 150)
    change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at hi
    simp only [hw128, hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw24 : w 24=0 := by
    have hi := h (118:Fin 150)
    change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at hi
    simp only [hw42, hw128,mul_zero,add_zero,zero_add] at hi
    have hn : (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2))):ℂ)≠0 := by
      have he : (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2))):ℂ)=((-1) * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))/((1 * (x^2)) * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) hP4) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw38 : w 38=0 := by
    have hi := h (117:Fin 150)
    change ((((-1) * a) / x)) * w 24 + ((-1)) * w 38 + ((((y^2) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 42=0 at hi
    simp only [hw42, hw24,mul_zero,add_zero,zero_add] at hi
    have hn : ((-1):ℂ)≠0 := by
      have he : ((-1):ℂ)=(-1)/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw112 : w 112=0 := by
    have hi := h (116:Fin 150)
    change ((((-1) * a) / x)) * w 24 + ((((x^2) + ((-1) * (y^2))) / ((x^2) * (y^2)))) * w 108 + (1) * w 112=0 at hi
    simp only [hw108, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw61 : w 61=0 := by
    have hi := h (115:Fin 150)
    change ((((-1) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 24 + (1) * w 61 + (((1 + ((-1) * a * x) + (b * y * (x^2))) / ((x^2) * (y^2)))) * w 108=0 at hi
    simp only [hw108, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw58 : w 58=0 := by
    have hi := h (114:Fin 150)
    change ((((-1) + ((-1) * b * y)) / (y^2))) * w 24 + (1) * w 58 + (1) * w 108=0 at hi
    simp only [hw108, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw56 : w 56=0 := by
    have hi := h (113:Fin 150)
    change ((((-2) + (y^2) + (a * x)) / (y^2))) * w 24 + (((-1) / (y^2))) * w 42 + (1) * w 56=0 at hi
    simp only [hw24, hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw122 : w 122=0 := by
    have hi := h (112:Fin 150)
    change (((((-1) * a) + ((-1) * (x^3))) / (x * (y^2)))) * w 24 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 42 + ((1 / (x^2))) * w 122=0 at hi
    simp only [hw42, hw24,mul_zero,add_zero,zero_add] at hi
    have hn : ((1 / (x^2)):ℂ)≠0 := by
      have he : ((1 / (x^2)):ℂ)=1/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw64 : w 64=0 := by
    have hi := h (111:Fin 150)
    change ((((-1) + (y^2) + (a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 64 + ((((-1) * a) / x)) * w 128=0 at hi
    simp only [hw128, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw62 : w 62=0 := by
    have hi := h (110:Fin 150)
    change ((a / x)) * w 24 + (1) * w 62 + ((1 / (x^2))) * w 108=0 at hi
    simp only [hw108, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw131 : w 131=0 := by
    have hi := h (109:Fin 150)
    change (1) * w 56 + ((((-1) * a) / x)) * w 112 + (1) * w 131=0 at hi
    simp only [hw56, hw112,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw28 : w 28=0 := by
    have hi := h (108:Fin 150)
    change (((a + (x^3)) / (x * (y^2)))) * w 24 + ((1 / (x^2))) * w 28 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 108=0 at hi
    simp only [hw108, hw24,mul_zero,add_zero,zero_add] at hi
    have hn : ((1 / (x^2)):ℂ)≠0 := by
      have he : ((1 / (x^2)):ℂ)=1/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw82 : w 82=0 := by
    have hi := h (107:Fin 150)
    change (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108=0 at hi
    simp only [hw24, hw108,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) * (y^2)) / (x^2)):ℂ)≠0 := by
      have he : ((((-1) * (y^2)) / (x^2)):ℂ)=((-1) * (y^2))/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw21 : w 21=0 := by
    have hi := h (106:Fin 150)
    change (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42=0 at hi
    simp only [hw42, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw19 : w 19=0 := by
    have hi := h (105:Fin 150)
    change (1) * w 19 + ((((-1) * a) / x)) * w 38 + (1) * w 94=0 at hi
    simp only [hw94, hw38,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw88 : w 88=0 := by
    have hi := h (104:Fin 150)
    change ((((-1) * a) / x)) * w 24 + ((1 / (x^2))) * w 42 + (1) * w 88=0 at hi
    simp only [hw42, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw86 : w 86=0 := by
    have hi := h (103:Fin 150)
    change ((((-1) * a) / x)) * w 22 + (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 86=0 at hi
    simp only [hw22, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw44 : w 44=0 := by
    have hi := h (102:Fin 150)
    change (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / (x^2))) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 44 + (((-1) / (x^2))) * w 108=0 at hi
    simp only [hw24, hw108,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) * (y^2)) / (x^2)):ℂ)≠0 := by
      have he : ((((-1) * (y^2)) / (x^2)):ℂ)=((-1) * (y^2))/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw16 : w 16=0 := by
    have hi := h (101:Fin 150)
    change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at hi
    simp only [hw42, hw24,mul_zero,add_zero,zero_add] at hi
    have hn : ((1 / (x^2)):ℂ)≠0 := by
      have he : ((1 / (x^2)):ℂ)=1/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw87 : w 87=0 := by
    have hi := h (100:Fin 150)
    change ((((-1) + (y^2)) / (y^2))) * w 24 + (1) * w 44 + (((x^2) / (y^2))) * w 87=0 at hi
    simp only [hw44, hw24,mul_zero,add_zero,zero_add] at hi
    have hn : (((x^2) / (y^2)):ℂ)≠0 := by
      have he : (((x^2) / (y^2)):ℂ)=(1 * (x^2))/(1 * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw106 : w 106=0 := by
    have hi := h (99:Fin 150)
    change (1) * w 16 + (((1 + ((-1) * (y^2))) / (y^2))) * w 24 + (1) * w 106=0 at hi
    simp only [hw16, hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw101 : w 101=0 := by
    have hi := h (98:Fin 150)
    change (1) * w 21 + (((-1) / (x^2))) * w 24 + ((-1)) * w 101=0 at hi
    simp only [hw21, hw24,mul_zero,add_zero,zero_add] at hi
    have hn : ((-1):ℂ)≠0 := by
      have he : ((-1):ℂ)=(-1)/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw99 : w 99=0 := by
    have hi := h (97:Fin 150)
    change ((1 / (x^2))) * w 24 + (((y^2) / (x^2))) * w 82 + (1) * w 99=0 at hi
    simp only [hw24, hw82,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw27 : w 27=0 := by
    have hi := h (96:Fin 150)
    change (1) * w 27 + ((-1)) * w 42 + (1) * w 87=0 at hi
    simp only [hw87, hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw123 : w 123=0 := by
    have hi := h (95:Fin 150)
    change (((y^2) / (x^2))) * w 16 + ((-1)) * w 108 + (1) * w 123=0 at hi
    simp only [hw16, hw108,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw117 : w 117=0 := by
    have hi := h (94:Fin 150)
    change (1) * w 42 + (1) * w 117=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw113 : w 113=0 := by
    have hi := h (93:Fin 150)
    change (1) * w 38 + (1) * w 113=0 at hi
    simp only [hw38,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw37 : w 37=0 := by
    have hi := h (92:Fin 150)
    change (1) * w 37 + (1) * w 112=0 at hi
    simp only [hw112,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw33 : w 33=0 := by
    have hi := h (91:Fin 150)
    change (1) * w 33 + (1) * w 108=0 at hi
    simp only [hw108,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw126 : w 126=0 := by
    have hi := h (90:Fin 150)
    change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at hi
    simp only [hw24,mul_zero,add_zero,zero_add] at hi
    have hn : ((1 / ((x^2) * (y^2))):ℂ)≠0 := by
      have he : ((1 / ((x^2) * (y^2))):ℂ)=1/((1 * (x^2)) * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw124 : w 124=0 := by
    have hi := h (89:Fin 150)
    change (1) * w 24 + (1) * w 124=0 at hi
    simp only [hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw26 : w 26=0 := by
    have hi := h (88:Fin 150)
    change (1) * w 26 + (1) * w 126=0 at hi
    simp only [hw126,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw48 : w 48=0 := by
    have hi := h (87:Fin 150)
    change (1) * w 48 + (1) * w 108=0 at hi
    simp only [hw108,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw102 : w 102=0 := by
    have hi := h (86:Fin 150)
    change (1) * w 42 + (1) * w 102=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw14 : w 14=0 := by
    have hi := h (85:Fin 150)
    change ((y^2)) * w 14 + (1) * w 24=0 at hi
    simp only [hw24,mul_zero,add_zero,zero_add] at hi
    have hn : ((y^2):ℂ)≠0 := by
      have he : ((y^2):ℂ)=(1 * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw96 : w 96=0 := by
    have hi := h (84:Fin 150)
    change (1) * w 96 + (1) * w 126=0 at hi
    simp only [hw126,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw46 : w 46=0 := by
    have hi := h (83:Fin 150)
    change (1) * w 46 + (1) * w 96=0 at hi
    simp only [hw96,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw104 : w 104=0 := by
    have hi := h (82:Fin 150)
    change ((y^2)) * w 14 + (1) * w 104=0 at hi
    simp only [hw14,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw98 : w 98=0 := by
    have hi := h (81:Fin 150)
    change (1) * w 48 + (1) * w 98=0 at hi
    simp only [hw48,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw52 : w 52=0 := by
    have hi := h (80:Fin 150)
    change (1) * w 52 + (1) * w 102=0 at hi
    simp only [hw102,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw49 : w 49=0 := by
    have hi := h (79:Fin 150)
    change (1) * w 49 + (1) * w 99=0 at hi
    simp only [hw99,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw51 : w 51=0 := by
    have hi := h (78:Fin 150)
    change (1) * w 51 + (1) * w 101=0 at hi
    simp only [hw101,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw65 : w 65=0 := by
    have hi := h (77:Fin 150)
    change (1) * w 65=0 at hi
    simpa only [one_mul] using hi
  have hw35 : w 35=0 := by
    have hi := h (76:Fin 150)
    change (1) * w 35=0 at hi
    simpa only [one_mul] using hi
  have hw115 : w 115=0 := by
    have hi := h (75:Fin 150)
    change (1) * w 115=0 at hi
    simpa only [one_mul] using hi
  have hw85 : w 85=0 := by
    have hi := h (74:Fin 150)
    change (1) * w 85=0 at hi
    simpa only [one_mul] using hi
  have hw18 : w 18=0 := by
    have hi := h (73:Fin 150)
    change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at hi
    have hn : ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))):ℂ)≠0 := by
      have he : ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))):ℂ)=(((1 * (z^2)) * ((-2) + (x^2))) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))/(((1 * (x^2)) * (y^2)) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)) hP6) hP1) (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy)) hP2)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw45 : w 45=0 := by
    have hi := h (72:Fin 150)
    change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) * (x^2)) / (y^2)):ℂ)≠0 := by
      have he : ((((-1) * (x^2)) / (y^2)):ℂ)=((-1) * (x^2))/(1 * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw30 : w 30=0 := by
    have hi := h (71:Fin 150)
    change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    have hn : (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2)))):ℂ)≠0 := by
      have he : (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2)))):ℂ)=(1 * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))/((1 * (y^2)) * ((-2) + (x^2))) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) hP2) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) hP6)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw55 : w 55=0 := by
    have hi := h (70:Fin 150)
    change (((2 + ((-1) * (x^2)) + ((-4) * (y^2)) + ((-1) * (x^4) * (y^2)) + (4 * (x^2) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 55=0 at hi
    simp only [hw30,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw95 : w 95=0 := by
    have hi := h (69:Fin 150)
    change (((2 + (x^2) + (x^6) + ((-3) * (x^4)) + ((a^2) * (x^4)) + ((-2) * (a^2) * (x^2)) + ((a^2) * (x^2) * (y^2)) + (a * b * y * (x^3)) + ((-2) * a * b * x * y)) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 95=0 at hi
    simp only [hw30,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw20 : w 20=0 := by
    have hi := h (68:Fin 150)
    change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at hi
    simp only [hw30,mul_zero,add_zero,zero_add] at hi
    have hn : ((1 / (x^2)):ℂ)≠0 := by
      have he : ((1 / (x^2)):ℂ)=1/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw110 : w 110=0 := by
    have hi := h (67:Fin 150)
    change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at hi
    simp only [hw30,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw90 : w 90=0 := by
    have hi := h (66:Fin 150)
    change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at hi
    simp only [hw30,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-2) + (x^2)) / (x^2)):ℂ)≠0 := by
      have he : ((((-2) + (x^2)) / (x^2)):ℂ)=(1 * ((-2) + (x^2)))/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) hP6) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw57 : w 57=0 := by
    have hi := h (65:Fin 150)
    change (((a + ((-1) * x) + (a * (x^2)) + (x * (a^2))) / x)) * w 18 + (1) * w 57=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw39 : w 39=0 := by
    have hi := h (64:Fin 150)
    change (((-1) + ((-1) * (x^2)) + ((-1) * a * x))) * w 18 + (1) * w 39=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw111 : w 111=0 := by
    have hi := h (63:Fin 150)
    change ((1 + (x^2) + (a * x))) * w 18 + (1) * w 111=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw93 : w 93=0 := by
    have hi := h (62:Fin 150)
    change (((x + ((-1) * a) + ((-1) * a * (x^2)) + ((-1) * x * (a^2))) / x)) * w 18 + (1) * w 93=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw114 : w 114=0 := by
    have hi := h (61:Fin 150)
    change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) * (z^2)) / ((x^2) * (y^2))):ℂ)≠0 := by
      have he : ((((-1) * (z^2)) / ((x^2) * (y^2))):ℂ)=((-1) * (z^2))/((1 * (x^2)) * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw36 : w 36=0 := by
    have hi := h (60:Fin 150)
    change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    have hn : ((1 / (x^2)):ℂ)≠0 := by
      have he : ((1 / (x^2)):ℂ)=1/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw40 : w 40=0 := by
    have hi := h (59:Fin 150)
    change (1) * w 40 + (1) * w 110=0 at hi
    simp only [hw110,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw132 : w 132=0 := by
    have hi := h (58:Fin 150)
    change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) * (z^2)) / (y^2)):ℂ)≠0 := by
      have he : ((((-1) * (z^2)) / (y^2)):ℂ)=((-1) * (z^2))/(1 * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw125 : w 125=0 := by
    have hi := h (57:Fin 150)
    change (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125=0 at hi
    simp only [hw36,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw25 : w 25=0 := by
    have hi := h (56:Fin 150)
    change (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114=0 at hi
    simp only [hw114,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw130 : w 130=0 := by
    have hi := h (55:Fin 150)
    change (((x^2) / (y^2))) * w 45 + (1) * w 130=0 at hi
    simp only [hw45,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw105 : w 105=0 := by
    have hi := h (54:Fin 150)
    change (1) * w 20 + (((x^2) / (y^2))) * w 105=0 at hi
    simp only [hw20,mul_zero,add_zero,zero_add] at hi
    have hn : (((x^2) / (y^2)):ℂ)≠0 := by
      have he : (((x^2) / (y^2)):ℂ)=(1 * (x^2))/(1 * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw60 : w 60=0 := by
    have hi := h (53:Fin 150)
    change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at hi
    simp only [hw90,mul_zero,add_zero,zero_add] at hi
    have hn : ((1 / (y^2)):ℂ)≠0 := by
      have he : ((1 / (y^2)):ℂ)=1/(1 * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw100 : w 100=0 := by
    have hi := h (52:Fin 150)
    change ((1 / (x^2))) * w 18 + (((y^2) / ((x^2) * (z^2)))) * w 100=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    have hn : (((y^2) / ((x^2) * (z^2))):ℂ)≠0 := by
      have he : (((y^2) / ((x^2) * (z^2))):ℂ)=(1 * (y^2))/((1 * (x^2)) * (z^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hz))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw50 : w 50=0 := by
    have hi := h (51:Fin 150)
    change (((y^2) / ((x^2) * (z^2)))) * w 50 + ((1 / (x^2))) * w 132=0 at hi
    simp only [hw132,mul_zero,add_zero,zero_add] at hi
    have hn : (((y^2) / ((x^2) * (z^2))):ℂ)≠0 := by
      have he : (((y^2) / ((x^2) * (z^2))):ℂ)=(1 * (y^2))/((1 * (x^2)) * (z^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hz))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw120 : w 120=0 := by
    have hi := h (50:Fin 150)
    change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at hi
    simp only [hw30,mul_zero,add_zero,zero_add] at hi
    have hn : ((1 / ((x^2) * (y^2))):ℂ)≠0 := by
      have he : ((1 / ((x^2) * (y^2))):ℂ)=1/((1 * (x^2)) * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw11 : w 11=0 := by
    have hi := h (49:Fin 150)
    change (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108=0 at hi
    simp only [hw108,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (x^2) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2) * (y^2)):ℂ)=(((-1) * (x^2)) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw73 : w 73=0 := by
    have hi := h (48:Fin 150)
    change (1) * w 73 + (((-1) / ((x^2) * (y^2)))) * w 126=0 at hi
    simp only [hw126,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw71 : w 71=0 := by
    have hi := h (47:Fin 150)
    change (((-1) / ((x^2) * (y^2)))) * w 48 + (1) * w 71=0 at hi
    simp only [hw48,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw70 : w 70=0 := by
    have hi := h (46:Fin 150)
    change (((-1) / (y^2))) * w 30 + (1) * w 70=0 at hi
    simp only [hw30,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw68 : w 68=0 := by
    have hi := h (45:Fin 150)
    change ((((-1) * (x^2)) / (y^2))) * w 21 + (1) * w 68=0 at hi
    simp only [hw21,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw63 : w 63=0 := by
    have hi := h (44:Fin 150)
    change ((((-1) * (y^2)) / (x^2))) * w 16 + (1) * w 63=0 at hi
    simp only [hw16,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw54 : w 54=0 := by
    have hi := h (43:Fin 150)
    change (((-1) * (y^2))) * w 14 + (1) * w 54=0 at hi
    simp only [hw14,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw13 : w 13=0 := by
    have hi := h (42:Fin 150)
    change (((-1) * (x^2) * (y^2))) * w 13 + (1) * w 36=0 at hi
    simp only [hw36,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (x^2) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2) * (y^2)):ℂ)=(((-1) * (x^2)) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw137 : w 137=0 := by
    have hi := h (41:Fin 150)
    change (1) * w 114 + (((-1) * (x^2) * (y^2))) * w 137=0 at hi
    simp only [hw114,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (x^2) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2) * (y^2)):ℂ)=(((-1) * (x^2)) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw136 : w 136=0 := by
    have hi := h (40:Fin 150)
    change (1) * w 96 + (((-1) * (y^2))) * w 136=0 at hi
    simp only [hw96,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (y^2)):ℂ)=((-1) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw10 : w 10=0 := by
    have hi := h (39:Fin 150)
    change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at hi
    simp only [hw90,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (y^2)):ℂ)=((-1) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw134 : w 134=0 := by
    have hi := h (38:Fin 150)
    change (1) * w 87 + ((((-1) * (y^2)) / (x^2))) * w 134=0 at hi
    simp only [hw87,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) * (y^2)) / (x^2)):ℂ)≠0 := by
      have he : ((((-1) * (y^2)) / (x^2)):ℂ)=((-1) * (y^2))/(1 * (x^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw84 : w 84=0 := by
    have hi := h (37:Fin 150)
    change (1) * w 84 + ((-1)) * w 132=0 at hi
    simp only [hw132,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw129 : w 129=0 := by
    have hi := h (36:Fin 150)
    change (1) * w 82 + ((((-1) * (x^2)) / (y^2))) * w 129=0 at hi
    simp only [hw82,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) * (x^2)) / (y^2)):ℂ)≠0 := by
      have he : ((((-1) * (x^2)) / (y^2)):ℂ)=((-1) * (x^2))/(1 * (y^2)) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw81 : w 81=0 := by
    have hi := h (35:Fin 150)
    change (1) * w 81 + (((-1) / (x^2))) * w 126=0 at hi
    simp only [hw126,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw79 : w 79=0 := by
    have hi := h (34:Fin 150)
    change (1) * w 79 + (((-1) / ((x^2) * (y^2)))) * w 102=0 at hi
    simp only [hw102,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw69 : w 69=0 := by
    have hi := h (33:Fin 150)
    change (((-1) / (x^2))) * w 24 + (1) * w 69=0 at hi
    simp only [hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw66 : w 66=0 := by
    have hi := h (32:Fin 150)
    change ((-1)) * w 18 + (1) * w 66=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw15 : w 15=0 := by
    have hi := h (31:Fin 150)
    change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at hi
    simp only [hw60,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (x^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2)):ℂ)=((-1) * (x^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw139 : w 139=0 := by
    have hi := h (30:Fin 150)
    change (1) * w 42 + (((-1) * (x^2) * (y^2))) * w 139=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (x^2) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2) * (y^2)):ℂ)=(((-1) * (x^2)) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw80 : w 80=0 := by
    have hi := h (29:Fin 150)
    change (1) * w 80 + (((-1) / (y^2))) * w 120=0 at hi
    simp only [hw120,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw77 : w 77=0 := by
    have hi := h (28:Fin 150)
    change (((-1) / ((x^2) * (y^2)))) * w 24 + (1) * w 77=0 at hi
    simp only [hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw5 : w 5=0 := by
    have hi := h (27:Fin 150)
    change (1) * w 5 + (((-1) / ((x^2) * (y^2)))) * w 30=0 at hi
    simp only [hw30,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw143 : w 143=0 := by
    have hi := h (26:Fin 150)
    change (((-1) / ((x^2) * (y^2)))) * w 42 + (1) * w 143=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw142 : w 142=0 := by
    have hi := h (25:Fin 150)
    change (((-1) / (y^2))) * w 24 + (1) * w 142=0 at hi
    simp only [hw24,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw141 : w 141=0 := by
    have hi := h (24:Fin 150)
    change (((-1) / (x^2))) * w 18 + (1) * w 141=0 at hi
    simp only [hw18,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw140 : w 140=0 := by
    have hi := h (23:Fin 150)
    change ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140=0 at hi
    simp only [hw15,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw135 : w 135=0 := by
    have hi := h (22:Fin 150)
    change ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135=0 at hi
    simp only [hw10,mul_zero,add_zero,zero_add] at hi
    simpa only [one_mul] using hi
  have hw9 : w 9=0 := by
    have hi := h (21:Fin 150)
    change (((-1) * (x^2))) * w 9 + (1) * w 132=0 at hi
    simp only [hw132,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (x^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2)):ℂ)=((-1) * (x^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw8 : w 8=0 := by
    have hi := h (20:Fin 150)
    change (((-1) * (y^2))) * w 8 + (1) * w 126=0 at hi
    simp only [hw126,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (y^2)):ℂ)=((-1) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw7 : w 7=0 := by
    have hi := h (19:Fin 150)
    change (((-1) * (x^2) * (y^2))) * w 7 + (1) * w 108=0 at hi
    simp only [hw108,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (x^2) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2) * (y^2)):ℂ)=(((-1) * (x^2)) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw145 : w 145=0 := by
    have hi := h (18:Fin 150)
    change (1) * w 120 + (((-1) * (x^2) * (y^2))) * w 145=0 at hi
    simp only [hw120,mul_zero,add_zero,zero_add] at hi
    have hn : (((-1) * (x^2) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2) * (y^2)):ℂ)=(((-1) * (x^2)) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw149 : w 149=0 := by
    have hi := h (17:Fin 150)
    change (1) * w 149=0 at hi
    simpa only [one_mul] using hi
  have hw75 : w 75=0 := by
    have hi := h (16:Fin 150)
    change (1) * w 75=0 at hi
    simpa only [one_mul] using hi
  have hw0 : w 0=0 := by
    have hi := h (15:Fin 150)
    change (1) * w 0=0 at hi
    simpa only [one_mul] using hi
  have hw4 : w 4=0 := by
    have hi := h (14:Fin 150)
    change (((-1) * (y^2))) * w 4=0 at hi
    have hn : (((-1) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (y^2)):ℂ)=((-1) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw12 : w 12=0 := by
    have hi := h (13:Fin 150)
    change ((-1)) * w 12=0 at hi
    have hn : ((-1):ℂ)≠0 := by
      have he : ((-1):ℂ)=(-1)/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw146 : w 146=0 := by
    have hi := h (12:Fin 150)
    change (((-1) * (y^2))) * w 146=0 at hi
    have hn : (((-1) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (y^2)):ℂ)=((-1) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw138 : w 138=0 := by
    have hi := h (11:Fin 150)
    change (1) * w 138=0 at hi
    simpa only [one_mul] using hi
  have hw74 : w 74=0 := by
    have hi := h (10:Fin 150)
    change (1) * w 74=0 at hi
    simpa only [one_mul] using hi
  have hw78 : w 78=0 := by
    have hi := h (9:Fin 150)
    change (1) * w 78=0 at hi
    simpa only [one_mul] using hi
  have hw76 : w 76=0 := by
    have hi := h (8:Fin 150)
    change (1) * w 76=0 at hi
    simpa only [one_mul] using hi
  have hw72 : w 72=0 := by
    have hi := h (7:Fin 150)
    change (1) * w 72=0 at hi
    simpa only [one_mul] using hi
  have hw3 : w 3=0 := by
    have hi := h (6:Fin 150)
    change (1) * w 3=0 at hi
    simpa only [one_mul] using hi
  have hw1 : w 1=0 := by
    have hi := h (5:Fin 150)
    change (1) * w 1=0 at hi
    simpa only [one_mul] using hi
  have hw2 : w 2=0 := by
    have hi := h (4:Fin 150)
    change (1) * w 2=0 at hi
    simpa only [one_mul] using hi
  have hw6 : w 6=0 := by
    have hi := h (3:Fin 150)
    change ((-1)) * w 6=0 at hi
    have hn : ((-1):ℂ)≠0 := by
      have he : ((-1):ℂ)=(-1)/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (by norm_num) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw147 : w 147=0 := by
    have hi := h (2:Fin 150)
    change (((-1) * (x^2))) * w 147=0 at hi
    have hn : (((-1) * (x^2)):ℂ)≠0 := by
      have he : (((-1) * (x^2)):ℂ)=((-1) * (x^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw148 : w 148=0 := by
    have hi := h (1:Fin 150)
    change (((-1) * (y^2))) * w 148=0 at hi
    have hn : (((-1) * (y^2)):ℂ)≠0 := by
      have he : (((-1) * (y^2)):ℂ)=((-1) * (y^2))/1 := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (by norm_num)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw144 : w 144=0 := by
    have hi := h (0:Fin 150)
    change (1) * w 144=0 at hi
    simpa only [one_mul] using hi
  funext i
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2
  · exact hw3
  · exact hw4
  · exact hw5
  · exact hw6
  · exact hw7
  · exact hw8
  · exact hw9
  · exact hw10
  · exact hw11
  · exact hw12
  · exact hw13
  · exact hw14
  · exact hw15
  · exact hw16
  · exact hw17
  · exact hw18
  · exact hw19
  · exact hw20
  · exact hw21
  · exact hw22
  · exact hw23
  · exact hw24
  · exact hw25
  · exact hw26
  · exact hw27
  · exact hw28
  · exact hw29
  · exact hw30
  · exact hw31
  · exact hw32
  · exact hw33
  · exact hw34
  · exact hw35
  · exact hw36
  · exact hw37
  · exact hw38
  · exact hw39
  · exact hw40
  · exact hw41
  · exact hw42
  · exact hw43
  · exact hw44
  · exact hw45
  · exact hw46
  · exact hw47
  · exact hw48
  · exact hw49
  · exact hw50
  · exact hw51
  · exact hw52
  · exact hw53
  · exact hw54
  · exact hw55
  · exact hw56
  · exact hw57
  · exact hw58
  · exact hw59
  · exact hw60
  · exact hw61
  · exact hw62
  · exact hw63
  · exact hw64
  · exact hw65
  · exact hw66
  · exact hw67
  · exact hw68
  · exact hw69
  · exact hw70
  · exact hw71
  · exact hw72
  · exact hw73
  · exact hw74
  · exact hw75
  · exact hw76
  · exact hw77
  · exact hw78
  · exact hw79
  · exact hw80
  · exact hw81
  · exact hw82
  · exact hw83
  · exact hw84
  · exact hw85
  · exact hw86
  · exact hw87
  · exact hw88
  · exact hw89
  · exact hw90
  · exact hw91
  · exact hw92
  · exact hw93
  · exact hw94
  · exact hw95
  · exact hw96
  · exact hw97
  · exact hw98
  · exact hw99
  · exact hw100
  · exact hw101
  · exact hw102
  · exact hw103
  · exact hw104
  · exact hw105
  · exact hw106
  · exact hw107
  · exact hw108
  · exact hw109
  · exact hw110
  · exact hw111
  · exact hw112
  · exact hw113
  · exact hw114
  · exact hw115
  · exact hw116
  · exact hw117
  · exact hw118
  · exact hw119
  · exact hw120
  · exact hw121
  · exact hw122
  · exact hw123
  · exact hw124
  · exact hw125
  · exact hw126
  · exact hw127
  · exact hw128
  · exact hw129
  · exact hw130
  · exact hw131
  · exact hw132
  · exact hw133
  · exact hw134
  · exact hw135
  · exact hw136
  · exact hw137
  · exact hw138
  · exact hw139
  · exact hw140
  · exact hw141
  · exact hw142
  · exact hw143
  · exact hw144
  · exact hw145
  · exact hw146
  · exact hw147
  · exact hw148
  · exact hw149

#print axioms reduced_rows_kernel

end QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveContinuationNegativeLastPivotsV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative

theorem last_pivots_zero (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ) (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0) : w 42=0 ∧ w 128=0 := by
  have hw42 : w 42=0 := by
    have hi := h124
    change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at hi
    have hn : ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2))))):ℂ)≠0 := by
      have he : ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2))))):ℂ)=((1 * ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))) * ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3))))/(((1 * (y^2)) * (x^4)) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hP5) hP0) (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) (pow_ne_zero 4 hx)) hP3)
    exact (mul_eq_zero.mp hi).resolve_left hn
  have hw128 : w 128=0 := by
    have hi := h120
    change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at hi
    simp only [hw42,mul_zero,add_zero,zero_add] at hi
    have hn : ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))):ℂ)≠0 := by
      have he : ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))):ℂ)=((-1) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2))))/((1 * (y^2)) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))) := by
        first | (solve | ring) | (congr 1 <;> ring)
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) hP3) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) hP4)
    exact (mul_eq_zero.mp hi).resolve_left hn
  exact ⟨hw42,hw128⟩
#print axioms last_pivots_zero
end QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative
end
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveContinuationNegativePivotBundleV4 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 16384
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative

theorem pivot71_zero (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ) (hw18 : w 18=0)
    (h71 : reducedRows x y z a b w 71=0) : w 30=0 := by
  have hi := h71
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at hi
  simp only [hw18,mul_zero,add_zero,zero_add] at hi
  have hn : (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2)))):ℂ)≠0 := by
    have he : (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2)))):ℂ)=(1 * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))/((1 * (y^2)) * ((-2) + (x^2))) := by
      first | (solve | ring) | (congr 1 <;> ring)
    rw [he]
    exact div_ne_zero (mul_ne_zero (by norm_num) hP2) (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) hP6)
  exact (mul_eq_zero.mp hi).resolve_left hn
#print axioms pivot71_zero

theorem pivot73_zero (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ) (h73 : reducedRows x y z a b w 73=0) : w 18=0 := by
  have hi := h73
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at hi
  have hn : ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))):ℂ)≠0 := by
    have he : ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))):ℂ)=(((1 * (z^2)) * ((-2) + (x^2))) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))/(((1 * (x^2)) * (y^2)) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))) := by
      first | (solve | ring) | (congr 1 <;> ring)
    rw [he]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)) hP6) hP1) (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 hy)) hP2)
  exact (mul_eq_zero.mp hi).resolve_left hn

#print axioms pivot73_zero

end QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveNegativeContinuationProofV4 -/
section
/-! Complete mathematical proof chains; intermediate development files merged. -/
@[expose] public noncomputable section

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 16384

namespace QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative

compact_certificate theorem reduced_step0 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 0=0)
    : reducedRows x y z a b w 0=0 := by
  change (1) * w 144=0 at hs
  have hs0 := hs
  change (1) * w 144=0
  exact hs0
#print axioms reduced_step0

compact_certificate theorem reduced_step1 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 1=0)
    (h0 : reducedRows x y z a b w 0=0)
    : reducedRows x y z a b w 1=0 := by
  change (1) * w 144 + (((-1) * (y^2))) * w 148=0 at hs
  have hs0 := hs
  change (((-1) * (y^2))) * w 148=0
  change (1) * w 144=0 at h0
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h0
#print axioms reduced_step1

compact_certificate theorem reduced_step2 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 2=0)
    (h0 : reducedRows x y z a b w 0=0)
    : reducedRows x y z a b w 2=0 := by
  change (1) * w 144 + (((-1) * (x^2))) * w 147=0 at hs
  have hs0 := hs
  change (((-1) * (x^2))) * w 147=0
  change (1) * w 144=0 at h0
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h0
#print axioms reduced_step2

compact_certificate theorem reduced_step3 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 3=0)
    (h0 : reducedRows x y z a b w 0=0)
    : reducedRows x y z a b w 3=0 := by
  change ((-1)) * w 6 + (1) * w 144=0 at hs
  have hs0 := hs
  change ((-1)) * w 6=0
  change (1) * w 144=0 at h0
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h0
#print axioms reduced_step3

compact_certificate theorem reduced_step4 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 4=0)
    : reducedRows x y z a b w 4=0 := by
  change (1) * w 2=0 at hs
  have hs0 := hs
  change (1) * w 2=0
  exact hs0
#print axioms reduced_step4

compact_certificate theorem reduced_step5 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 5=0)
    (h4 : reducedRows x y z a b w 4=0)
    : reducedRows x y z a b w 5=0 := by
  change (1) * w 1 + (((-1) / (x^2))) * w 2=0 at hs
  have hs0 := hs
  change (1) * w 1=0
  change (1) * w 2=0 at h4
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h4
#print axioms reduced_step5

compact_certificate theorem reduced_step6 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 6=0)
    (h0 : reducedRows x y z a b w 0=0)
    : reducedRows x y z a b w 6=0 := by
  change (1) * w 3 + (((-1) / (x^2))) * w 144=0 at hs
  have hs0 := hs
  change (1) * w 3=0
  change (1) * w 144=0 at h0
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h0
#print axioms reduced_step6

compact_certificate theorem reduced_step7 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 7=0)
    (h1 : reducedRows x y z a b w 1=0)
    : reducedRows x y z a b w 7=0 := by
  change (1) * w 72 + (((-1) * (y^2))) * w 148=0 at hs
  have hs0 := hs
  change (1) * w 72=0
  change (((-1) * (y^2))) * w 148=0 at h1
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h1
#print axioms reduced_step7

compact_certificate theorem reduced_step8 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 8=0)
    (h0 : reducedRows x y z a b w 0=0)
    : reducedRows x y z a b w 8=0 := by
  change (1) * w 76 + (((-1) / (y^2))) * w 144=0 at hs
  have hs0 := hs
  change (1) * w 76=0
  change (1) * w 144=0 at h0
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h0
#print axioms reduced_step8

compact_certificate theorem reduced_step9 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 9=0)
    (h2 : reducedRows x y z a b w 2=0)
    : reducedRows x y z a b w 9=0 := by
  change (1) * w 78 + (((-1) * (x^2))) * w 147=0 at hs
  have hs0 := hs
  change (1) * w 78=0
  change (((-1) * (x^2))) * w 147=0 at h2
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h2
#print axioms reduced_step9



compact_certificate theorem reduced_step10 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 10=0)
    (h1 : reducedRows x y z a b w 1=0)
    : reducedRows x y z a b w 10=0 := by
  change (1) * w 74 + ((-1)) * w 148=0 at hs
  have hs0 := hs
  change (1) * w 74=0
  change (((-1) * (y^2))) * w 148=0 at h1
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (y^2)))*h1
#print axioms reduced_step10

compact_certificate theorem reduced_step11 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 11=0)
    : reducedRows x y z a b w 11=0 := by
  change (1) * w 138=0 at hs
  have hs0 := hs
  change (1) * w 138=0
  exact hs0
#print axioms reduced_step11

compact_certificate theorem reduced_step12 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 12=0)
    (h11 : reducedRows x y z a b w 11=0)
    : reducedRows x y z a b w 12=0 := by
  change (1) * w 138 + (((-1) * (y^2))) * w 146=0 at hs
  have hs0 := hs
  change (((-1) * (y^2))) * w 146=0
  change (1) * w 138=0 at h11
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h11
#print axioms reduced_step12

compact_certificate theorem reduced_step13 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 13=0)
    (h11 : reducedRows x y z a b w 11=0)
    : reducedRows x y z a b w 13=0 := by
  change ((-1)) * w 12 + (1) * w 138=0 at hs
  have hs0 := hs
  change ((-1)) * w 12=0
  change (1) * w 138=0 at h11
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h11
#print axioms reduced_step13

compact_certificate theorem reduced_step14 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 14=0)
    (h11 : reducedRows x y z a b w 11=0)
    : reducedRows x y z a b w 14=0 := by
  change (((-1) * (y^2))) * w 4 + (1) * w 138=0 at hs
  have hs0 := hs
  change (((-1) * (y^2))) * w 4=0
  change (1) * w 138=0 at h11
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h11
#print axioms reduced_step14

compact_certificate theorem reduced_step15 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 15=0)
    : reducedRows x y z a b w 15=0 := by
  change (1) * w 0=0 at hs
  have hs0 := hs
  change (1) * w 0=0
  exact hs0
#print axioms reduced_step15

compact_certificate theorem reduced_step16 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 16=0)
    (h15 : reducedRows x y z a b w 15=0)
    : reducedRows x y z a b w 16=0 := by
  change (((-1) / (x^2))) * w 0 + (1) * w 75=0 at hs
  have hs0 := hs
  change (1) * w 75=0
  change (1) * w 0=0 at h15
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h15
#print axioms reduced_step16

compact_certificate theorem reduced_step17 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 17=0)
    (h15 : reducedRows x y z a b w 15=0)
    : reducedRows x y z a b w 17=0 := by
  change ((1 / ((x^2) * (y^2) * (z^2)))) * w 0 + (1) * w 149=0 at hs
  have hs0 := hs
  change (1) * w 149=0
  change (1) * w 0=0 at h15
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / ((x^2) * (y^2) * (z^2))))*h15
#print axioms reduced_step17

compact_certificate theorem reduced_step18 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 18=0)
    : reducedRows x y z a b w 18=0 := by
  change (1) * w 120 + (((-1) * (x^2) * (y^2))) * w 145=0 at hs
  have hs0 := hs
  change (1) * w 120 + (((-1) * (x^2) * (y^2))) * w 145=0
  exact hs0
#print axioms reduced_step18

compact_certificate theorem reduced_step19 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 19=0)
    : reducedRows x y z a b w 19=0 := by
  change (((-1) * (x^2) * (y^2))) * w 7 + (1) * w 108=0 at hs
  have hs0 := hs
  change (((-1) * (x^2) * (y^2))) * w 7 + (1) * w 108=0
  exact hs0
#print axioms reduced_step19



compact_certificate theorem reduced_step20 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 20=0)
    : reducedRows x y z a b w 20=0 := by
  change (((-1) * (y^2))) * w 8 + (1) * w 126=0 at hs
  have hs0 := hs
  change (((-1) * (y^2))) * w 8 + (1) * w 126=0
  exact hs0
#print axioms reduced_step20

compact_certificate theorem reduced_step21 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 21=0)
    : reducedRows x y z a b w 21=0 := by
  change (((-1) * (x^2))) * w 9 + (1) * w 132=0 at hs
  have hs0 := hs
  change (((-1) * (x^2))) * w 9 + (1) * w 132=0
  exact hs0
#print axioms reduced_step21

compact_certificate theorem reduced_step22 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 22=0)
    : reducedRows x y z a b w 22=0 := by
  change ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135=0 at hs
  have hs0 := hs
  change ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135=0
  exact hs0
#print axioms reduced_step22

compact_certificate theorem reduced_step23 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 23=0)
    : reducedRows x y z a b w 23=0 := by
  change ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140=0 at hs
  have hs0 := hs
  change ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140=0
  exact hs0
#print axioms reduced_step23

compact_certificate theorem reduced_step24 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 24=0)
    : reducedRows x y z a b w 24=0 := by
  change (((-1) / (x^2))) * w 18 + (1) * w 141=0 at hs
  have hs0 := hs
  change (((-1) / (x^2))) * w 18 + (1) * w 141=0
  exact hs0
#print axioms reduced_step24

compact_certificate theorem reduced_step25 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 25=0)
    : reducedRows x y z a b w 25=0 := by
  change (((-1) / (y^2))) * w 24 + (1) * w 142=0 at hs
  have hs0 := hs
  change (((-1) / (y^2))) * w 24 + (1) * w 142=0
  exact hs0
#print axioms reduced_step25

compact_certificate theorem reduced_step26 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 26=0)
    : reducedRows x y z a b w 26=0 := by
  change (((-1) / ((x^2) * (y^2)))) * w 42 + (1) * w 143=0 at hs
  have hs0 := hs
  change (((-1) / ((x^2) * (y^2)))) * w 42 + (1) * w 143=0
  exact hs0
#print axioms reduced_step26

compact_certificate theorem reduced_step27 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 27=0)
    : reducedRows x y z a b w 27=0 := by
  change (1) * w 5 + (((-1) / ((x^2) * (y^2)))) * w 30=0 at hs
  have hs0 := hs
  change (1) * w 5 + (((-1) / ((x^2) * (y^2)))) * w 30=0
  exact hs0
#print axioms reduced_step27

compact_certificate theorem reduced_step28 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 28=0)
    (h25 : reducedRows x y z a b w 25=0)
    : reducedRows x y z a b w 28=0 := by
  change (1) * w 77 + (((-1) / (x^2))) * w 142=0 at hs
  have hs0 := hs
  change (((-1) / ((x^2) * (y^2)))) * w 24 + (1) * w 77=0
  change (((-1) / (y^2))) * w 24 + (1) * w 142=0 at h25
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h25
#print axioms reduced_step28

compact_certificate theorem reduced_step29 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 29=0)
    (h18 : reducedRows x y z a b w 18=0)
    : reducedRows x y z a b w 29=0 := by
  change (1) * w 80 + (((-1) * (x^2))) * w 145=0 at hs
  have hs0 := hs
  change (1) * w 80 + (((-1) / (y^2))) * w 120=0
  change (1) * w 120 + (((-1) * (x^2) * (y^2))) * w 145=0 at h18
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (y^2)))*h18
#print axioms reduced_step29



compact_certificate theorem reduced_step30 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 30=0)
    : reducedRows x y z a b w 30=0 := by
  change (1) * w 42 + (((-1) * (x^2) * (y^2))) * w 139=0 at hs
  have hs0 := hs
  change (1) * w 42 + (((-1) * (x^2) * (y^2))) * w 139=0
  exact hs0
#print axioms reduced_step30

compact_certificate theorem reduced_step31 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 31=0)
    (h23 : reducedRows x y z a b w 23=0)
    : reducedRows x y z a b w 31=0 := by
  change (1) * w 60 + (((-1) * (y^2))) * w 140=0 at hs
  have hs0 := hs
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0
  change ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140=0 at h23
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) * (y^2)))*h23
#print axioms reduced_step31

compact_certificate theorem reduced_step32 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 32=0)
    (h24 : reducedRows x y z a b w 24=0)
    : reducedRows x y z a b w 32=0 := by
  change (1) * w 66 + (((-1) * (x^2))) * w 141=0 at hs
  have hs0 := hs
  change ((-1)) * w 18 + (1) * w 66=0
  change (((-1) / (x^2))) * w 18 + (1) * w 141=0 at h24
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) * (x^2)))*h24
#print axioms reduced_step32

compact_certificate theorem reduced_step33 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 33=0)
    (h25 : reducedRows x y z a b w 25=0)
    : reducedRows x y z a b w 33=0 := by
  change (1) * w 69 + ((((-1) * (y^2)) / (x^2))) * w 142=0 at hs
  have hs0 := hs
  change (((-1) / (x^2))) * w 24 + (1) * w 69=0
  change (((-1) / (y^2))) * w 24 + (1) * w 142=0 at h25
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((-1) * (y^2)) / (x^2)))*h25
#print axioms reduced_step33

compact_certificate theorem reduced_step34 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 34=0)
    : reducedRows x y z a b w 34=0 := by
  change (1) * w 79 + (((-1) / ((x^2) * (y^2)))) * w 102=0 at hs
  have hs0 := hs
  change (1) * w 79 + (((-1) / ((x^2) * (y^2)))) * w 102=0
  exact hs0
#print axioms reduced_step34

compact_certificate theorem reduced_step35 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 35=0)
    : reducedRows x y z a b w 35=0 := by
  change (1) * w 81 + (((-1) / (x^2))) * w 126=0 at hs
  have hs0 := hs
  change (1) * w 81 + (((-1) / (x^2))) * w 126=0
  exact hs0
#print axioms reduced_step35

compact_certificate theorem reduced_step36 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 36=0)
    : reducedRows x y z a b w 36=0 := by
  change (1) * w 82 + ((((-1) * (x^2)) / (y^2))) * w 129=0 at hs
  have hs0 := hs
  change (1) * w 82 + ((((-1) * (x^2)) / (y^2))) * w 129=0
  exact hs0
#print axioms reduced_step36

compact_certificate theorem reduced_step37 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 37=0)
    : reducedRows x y z a b w 37=0 := by
  change (1) * w 84 + ((-1)) * w 132=0 at hs
  have hs0 := hs
  change (1) * w 84 + ((-1)) * w 132=0
  exact hs0
#print axioms reduced_step37

compact_certificate theorem reduced_step38 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 38=0)
    : reducedRows x y z a b w 38=0 := by
  change (1) * w 87 + ((((-1) * (y^2)) / (x^2))) * w 134=0 at hs
  have hs0 := hs
  change (1) * w 87 + ((((-1) * (y^2)) / (x^2))) * w 134=0
  exact hs0
#print axioms reduced_step38

compact_certificate theorem reduced_step39 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 39=0)
    (h22 : reducedRows x y z a b w 22=0)
    : reducedRows x y z a b w 39=0 := by
  change (1) * w 90 + (((-1) * (x^2))) * w 135=0 at hs
  have hs0 := hs
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0
  change ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135=0 at h22
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) * (x^2)))*h22
#print axioms reduced_step39



compact_certificate theorem reduced_step40 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 40=0)
    : reducedRows x y z a b w 40=0 := by
  change (1) * w 96 + (((-1) * (y^2))) * w 136=0 at hs
  have hs0 := hs
  change (1) * w 96 + (((-1) * (y^2))) * w 136=0
  exact hs0
#print axioms reduced_step40

compact_certificate theorem reduced_step41 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 41=0)
    : reducedRows x y z a b w 41=0 := by
  change (1) * w 114 + (((-1) * (x^2) * (y^2))) * w 137=0 at hs
  have hs0 := hs
  change (1) * w 114 + (((-1) * (x^2) * (y^2))) * w 137=0
  exact hs0
#print axioms reduced_step41

compact_certificate theorem reduced_step42 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 42=0)
    : reducedRows x y z a b w 42=0 := by
  change (((-1) * (x^2) * (y^2))) * w 13 + (1) * w 36=0 at hs
  have hs0 := hs
  change (((-1) * (x^2) * (y^2))) * w 13 + (1) * w 36=0
  exact hs0
#print axioms reduced_step42

compact_certificate theorem reduced_step43 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 43=0)
    : reducedRows x y z a b w 43=0 := by
  change (((-1) * (y^2))) * w 14 + (1) * w 54=0 at hs
  have hs0 := hs
  change (((-1) * (y^2))) * w 14 + (1) * w 54=0
  exact hs0
#print axioms reduced_step43

compact_certificate theorem reduced_step44 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 44=0)
    : reducedRows x y z a b w 44=0 := by
  change ((((-1) * (y^2)) / (x^2))) * w 16 + (1) * w 63=0 at hs
  have hs0 := hs
  change ((((-1) * (y^2)) / (x^2))) * w 16 + (1) * w 63=0
  exact hs0
#print axioms reduced_step44

compact_certificate theorem reduced_step45 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 45=0)
    : reducedRows x y z a b w 45=0 := by
  change ((((-1) * (x^2)) / (y^2))) * w 21 + (1) * w 68=0 at hs
  have hs0 := hs
  change ((((-1) * (x^2)) / (y^2))) * w 21 + (1) * w 68=0
  exact hs0
#print axioms reduced_step45

compact_certificate theorem reduced_step46 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 46=0)
    : reducedRows x y z a b w 46=0 := by
  change (((-1) / (y^2))) * w 30 + (1) * w 70=0 at hs
  have hs0 := hs
  change (((-1) / (y^2))) * w 30 + (1) * w 70=0
  exact hs0
#print axioms reduced_step46

compact_certificate theorem reduced_step47 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 47=0)
    : reducedRows x y z a b w 47=0 := by
  change (((-1) / ((x^2) * (y^2)))) * w 48 + (1) * w 71=0 at hs
  have hs0 := hs
  change (((-1) / ((x^2) * (y^2)))) * w 48 + (1) * w 71=0
  exact hs0
#print axioms reduced_step47

compact_certificate theorem reduced_step48 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 48=0)
    : reducedRows x y z a b w 48=0 := by
  change (1) * w 73 + (((-1) / ((x^2) * (y^2)))) * w 126=0 at hs
  have hs0 := hs
  change (1) * w 73 + (((-1) / ((x^2) * (y^2)))) * w 126=0
  exact hs0
#print axioms reduced_step48

compact_certificate theorem reduced_step49 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 49=0)
    : reducedRows x y z a b w 49=0 := by
  change (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108=0 at hs
  have hs0 := hs
  change (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108=0
  exact hs0
#print axioms reduced_step49



compact_certificate theorem reduced_step50 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 50=0)
    (h27 : reducedRows x y z a b w 27=0)
    : reducedRows x y z a b w 50=0 := by
  change (1) * w 5 + ((1 / ((x^2) * (y^2)))) * w 120=0 at hs
  have hs0 := hs
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0
  change (1) * w 5 + (((-1) / ((x^2) * (y^2)))) * w 30=0 at h27
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h27
#print axioms reduced_step50

compact_certificate theorem reduced_step51 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 51=0)
    (h21 : reducedRows x y z a b w 21=0)
    : reducedRows x y z a b w 51=0 := by
  change (1) * w 9 + (((y^2) / ((x^2) * (z^2)))) * w 50=0 at hs
  have hs0 := hs
  change (((y^2) / ((x^2) * (z^2)))) * w 50 + ((1 / (x^2))) * w 132=0
  change (((-1) * (x^2))) * w 9 + (1) * w 132=0 at h21
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h21
#print axioms reduced_step51

compact_certificate theorem reduced_step52 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 52=0)
    (h24 : reducedRows x y z a b w 24=0)
    : reducedRows x y z a b w 52=0 := by
  change (((y^2) / ((x^2) * (z^2)))) * w 100 + (1) * w 141=0 at hs
  have hs0 := hs
  change ((1 / (x^2))) * w 18 + (((y^2) / ((x^2) * (z^2)))) * w 100=0
  change (((-1) / (x^2))) * w 18 + (1) * w 141=0 at h24
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h24
#print axioms reduced_step52

compact_certificate theorem reduced_step53 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 53=0)
    (h39 : reducedRows x y z a b w 39=0)
    : reducedRows x y z a b w 53=0 := by
  change (1) * w 10 + ((1 / (y^2))) * w 60=0 at hs
  have hs0 := hs
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h39
#print axioms reduced_step53

compact_certificate theorem reduced_step54 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 54=0)
    : reducedRows x y z a b w 54=0 := by
  change (1) * w 20 + (((x^2) / (y^2))) * w 105=0 at hs
  have hs0 := hs
  change (1) * w 20 + (((x^2) / (y^2))) * w 105=0
  exact hs0
#print axioms reduced_step54

compact_certificate theorem reduced_step55 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 55=0)
    : reducedRows x y z a b w 55=0 := by
  change (((x^2) / (y^2))) * w 45 + (1) * w 130=0 at hs
  have hs0 := hs
  change (((x^2) / (y^2))) * w 45 + (1) * w 130=0
  exact hs0
#print axioms reduced_step55

compact_certificate theorem reduced_step56 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 56=0)
    : reducedRows x y z a b w 56=0 := by
  change (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114=0 at hs
  have hs0 := hs
  change (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114=0
  exact hs0
#print axioms reduced_step56

compact_certificate theorem reduced_step57 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 57=0)
    : reducedRows x y z a b w 57=0 := by
  change (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125=0 at hs
  have hs0 := hs
  change (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125=0
  exact hs0
#print axioms reduced_step57

compact_certificate theorem reduced_step58 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 58=0)
    (h51 : reducedRows x y z a b w 51=0)
    (h52 : reducedRows x y z a b w 52=0)
    : reducedRows x y z a b w 58=0 := by
  change (1) * w 50 + (1) * w 100=0 at hs
  have hs0 := hs
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0
  change (((y^2) / ((x^2) * (z^2)))) * w 50 + ((1 / (x^2))) * w 132=0 at h51
  change ((1 / (x^2))) * w 18 + (((y^2) / ((x^2) * (z^2)))) * w 100=0 at h52
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((x^2) * (z^2)) / (y^2)))*h51-((((x^2) * (z^2)) / (y^2)))*h52
#print axioms reduced_step58

compact_certificate theorem reduced_step59 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 59=0)
    (h53 : reducedRows x y z a b w 53=0)
    : reducedRows x y z a b w 59=0 := by
  change (1) * w 40 + (1) * w 60 + (1) * w 90 + (1) * w 110=0 at hs
  have hs0 := hs
  change (1) * w 40 + (1) * w 110=0
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((y^2))*h53
#print axioms reduced_step59



compact_certificate theorem reduced_step60 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 61=0)
    (h21 : reducedRows x y z a b w 21=0)
    (h37 : reducedRows x y z a b w 37=0)
    (h58 : reducedRows x y z a b w 58=0)
    : reducedRows x y z a b w 60=0 := by
  change (1) * w 9 + ((((-1) * a) / x)) * w 18 + ((1 / (x^2))) * w 36 + (1) * w 84=0 at hs
  have hs0 := hs
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0
  change (((-1) * (x^2))) * w 9 + (1) * w 132=0 at h21
  change (1) * w 84 + ((-1)) * w 132=0 at h37
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h21-(1)*h37-(((((-1) * (y^2)) + ((-1) * (x^2) * (y^2))) / ((x^2) * (z^2))))*h58
#print axioms reduced_step60

compact_certificate theorem reduced_step61 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 62=0)
    (h56 : reducedRows x y z a b w 56=0)
    (h57 : reducedRows x y z a b w 57=0)
    (h60 : reducedRows x y z a b w 60=0)
    : reducedRows x y z a b w 61=0 := by
  change (1) * w 25 + (1) * w 125=0 at hs
  have hs0 := hs
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0
  change (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114=0 at h56
  change (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125=0 at h57
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h56-(1)*h57-((((-1) * (z^2)) / (y^2)))*h60
#print axioms reduced_step61

compact_certificate theorem reduced_step62 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 63=0)
    (h7 : reducedRows x y z a b w 7=0)
    (h60 : reducedRows x y z a b w 60=0)
    : reducedRows x y z a b w 62=0 := by
  change (1) * w 18 + ((((-1) * a) / x)) * w 36 + ((1 / (x^2))) * w 72 + (1) * w 93=0 at hs
  have hs0 := hs
  change (((x + ((-1) * a) + ((-1) * a * (x^2)) + ((-1) * x * (a^2))) / x)) * w 18 + (1) * w 93=0
  change (1) * w 72=0 at h7
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h7-(((-1) * a * x))*h60
#print axioms reduced_step62

compact_certificate theorem reduced_step63 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 64=0)
    (h0 : reducedRows x y z a b w 0=0)
    (h7 : reducedRows x y z a b w 7=0)
    (h60 : reducedRows x y z a b w 60=0)
    : reducedRows x y z a b w 63=0 := by
  change (1) * w 36 + ((((-1) * a) / x)) * w 72 + (1) * w 111 + ((1 / (x^2))) * w 144=0 at hs
  have hs0 := hs
  change ((1 + (x^2) + (a * x))) * w 18 + (1) * w 111=0
  change (1) * w 144=0 at h0
  change (1) * w 72=0 at h7
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h0-((((-1) * a) / x))*h7-((x^2))*h60
#print axioms reduced_step63

compact_certificate theorem reduced_step64 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 65=0)
    (h3 : reducedRows x y z a b w 3=0)
    (h9 : reducedRows x y z a b w 9=0)
    (h61 : reducedRows x y z a b w 61=0)
    : reducedRows x y z a b w 64=0 := by
  change ((1 / (x^2))) * w 6 + (1) * w 39 + ((((-1) * a) / x)) * w 78 + (1) * w 114=0 at hs
  have hs0 := hs
  change (((-1) + ((-1) * (x^2)) + ((-1) * a * x))) * w 18 + (1) * w 39=0
  change ((-1)) * w 6=0 at h3
  change (1) * w 78=0 at h9
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h3-((((-1) * a) / x))*h9-((((-1) * (x^2) * (y^2)) / (z^2)))*h61
#print axioms reduced_step64

compact_certificate theorem reduced_step65 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 66=0)
    (h9 : reducedRows x y z a b w 9=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h61 : reducedRows x y z a b w 61=0)
    : reducedRows x y z a b w 65=0 := by
  change (1) * w 57 + ((1 / (x^2))) * w 78 + ((((-1) * a) / x)) * w 114 + (1) * w 132=0 at hs
  have hs0 := hs
  change (((a + ((-1) * x) + (a * (x^2)) + (x * (a^2))) / x)) * w 18 + (1) * w 57=0
  change (1) * w 78=0 at h9
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h9-((((-1) * (y^2)) / (z^2)))*h58-(((a * x * (y^2)) / (z^2)))*h61
#print axioms reduced_step65

compact_certificate theorem reduced_step66 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 74=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h53 : reducedRows x y z a b w 53=0)
    : reducedRows x y z a b w 66=0 := by
  change (1) * w 15 + ((((-1) * a) / x)) * w 30 + ((1 / (x^2))) * w 60 + (1) * w 90=0 at hs
  have hs0 := hs
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h31-(((2 * (y^2)) / (x^2)))*h53
#print axioms reduced_step66

compact_certificate theorem reduced_step67 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 73=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h66 : reducedRows x y z a b w 66=0)
    : reducedRows x y z a b w 67=0 := by
  change (1) * w 10 + ((((-1) * b) / y)) * w 30 + (1) * w 60 + ((1 / (y^2))) * w 90 + (1) * w 110=0 at hs
  have hs0 := hs
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h39-((y^2))*h53-((((2 * (x^2)) + ((-1) * (x^2) * (y^2))) / ((y^2) * ((-2) + (x^2)))))*h66
#print axioms reduced_step67

compact_certificate theorem reduced_step68 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 75=0)
    (h27 : reducedRows x y z a b w 27=0)
    (h29 : reducedRows x y z a b w 29=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h66 : reducedRows x y z a b w 66=0)
    : reducedRows x y z a b w 68=0 := by
  change (1) * w 5 + ((((-1) * a) / x)) * w 10 + ((1 / (x^2))) * w 20 + (1) * w 80=0 at hs
  have hs0 := hs
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0
  change (1) * w 5 + (((-1) / ((x^2) * (y^2)))) * w 30=0 at h27
  change (1) * w 80 + (((-1) / (y^2))) * w 120=0 at h29
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h27-(1)*h29-((a / (x * (y^2))))*h39-((x^2))*h50-((((-1) * a * x) / ((y^2) * ((-2) + (x^2)))))*h66
#print axioms reduced_step68

compact_certificate theorem reduced_step69 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 60=0)
    (h29 : reducedRows x y z a b w 29=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h59 : reducedRows x y z a b w 59=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h68 : reducedRows x y z a b w 68=0)
    : reducedRows x y z a b w 69=0 := by
  change (1) * w 20 + ((((-1) * a) / x)) * w 40 + ((1 / (x^2))) * w 80 + (1) * w 95=0 at hs
  have hs0 := hs
  change (((2 + (x^2) + (x^6) + ((-3) * (x^4)) + ((a^2) * (x^4)) + ((-2) * (a^2) * (x^2)) + ((a^2) * (x^2) * (y^2)) + (a * b * y * (x^3)) + ((-2) * a * b * x * y)) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 95=0
  change (1) * w 80 + (((-1) / (y^2))) * w 120=0 at h29
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change (1) * w 40 + (1) * w 110=0 at h59
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h29-(1)*h50-((((-1) * a) / x))*h59-((a / x))*h67-((x^2))*h68
#print axioms reduced_step69



compact_certificate theorem reduced_step70 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 76=0)
    (h29 : reducedRows x y z a b w 29=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h54 : reducedRows x y z a b w 54=0)
    (h68 : reducedRows x y z a b w 68=0)
    : reducedRows x y z a b w 70=0 := by
  change ((1 / (x^2))) * w 30 + (1) * w 55 + ((1 / (x^2))) * w 80 + (1) * w 105=0 at hs
  have hs0 := hs
  change (((2 + ((-1) * (x^2)) + ((-4) * (y^2)) + ((-1) * (x^4) * (y^2)) + (4 * (x^2) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 55=0
  change (1) * w 80 + (((-1) / (y^2))) * w 120=0 at h29
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change (1) * w 20 + (((x^2) / (y^2))) * w 105=0 at h54
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h29-(1)*h50-(((y^2) / (x^2)))*h54-(((-1) * (y^2)))*h68
#print axioms reduced_step70

compact_certificate theorem reduced_step71 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 77=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h29 : reducedRows x y z a b w 29=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h51 : reducedRows x y z a b w 51=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h68 : reducedRows x y z a b w 68=0)
    : reducedRows x y z a b w 71=0 := by
  change ((1 / (y^2))) * w 0 + (1) * w 20 + ((1 / (y^2))) * w 30 + (1) * w 50 + ((1 / (y^2))) * w 60 + (1) * w 80 + (1) * w 110 + ((1 / (y^2))) * w 120=0 at hs
  have hs0 := hs
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0
  change (1) * w 0=0 at h15
  change (1) * w 80 + (((-1) / (y^2))) * w 120=0 at h29
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change (((y^2) / ((x^2) * (z^2)))) * w 50 + ((1 / (x^2))) * w 132=0 at h51
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (y^2)))*h15-(1)*h29-((2 * (x^2)))*h50-((((x^2) * (z^2)) / (y^2)))*h51-(1)*h53-(1)*h58-((((-1) * (x^2)) / ((y^2) * ((-2) + (x^2)))))*h66-(1)*h67-((x^2))*h68
#print axioms reduced_step71

compact_certificate theorem reduced_step72 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 78=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h46 : reducedRows x y z a b w 46=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h52 : reducedRows x y z a b w 52=0)
    (h55 : reducedRows x y z a b w 55=0)
    (h59 : reducedRows x y z a b w 59=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h71 : reducedRows x y z a b w 71=0)
    : reducedRows x y z a b w 72=0 := by
  change ((1 / (y^2))) * w 0 + ((1 / (y^2))) * w 30 + (1) * w 40 + (1) * w 70 + ((1 / (y^2))) * w 90 + (1) * w 100 + ((1 / (y^2))) * w 120 + (1) * w 130=0 at hs
  have hs0 := hs
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0
  change (1) * w 0=0 at h15
  change (((-1) / (y^2))) * w 30 + (1) * w 70=0 at h46
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (x^2))) * w 18 + (((y^2) / ((x^2) * (z^2)))) * w 100=0 at h52
  change (((x^2) / (y^2))) * w 45 + (1) * w 130=0 at h55
  change (1) * w 40 + (1) * w 110=0 at h59
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (y^2)))*h15-(1)*h46-((x^2))*h50-((((x^2) * (z^2)) / (y^2)))*h52-(1)*h55-(1)*h59-(((x^2) / ((y^2) * ((-2) + (x^2)))))*h66-((-1))*h67-((((-2) + (x^2) + (2 * b * y) + (3 * a * x) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))*h71
#print axioms reduced_step72

compact_certificate theorem reduced_step73 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 79=0)
    (h46 : reducedRows x y z a b w 46=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h69 : reducedRows x y z a b w 69=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h72 : reducedRows x y z a b w 72=0)
    : reducedRows x y z a b w 73=0 := by
  change (1) * w 45 + ((1 / (x^2))) * w 70 + (1) * w 95 + ((1 / (x^2))) * w 120=0 at hs
  have hs0 := hs
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0
  change (((-1) / (y^2))) * w 30 + (1) * w 70=0 at h46
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change (((2 + (x^2) + (x^6) + ((-3) * (x^4)) + ((a^2) * (x^4)) + ((-2) * (a^2) * (x^2)) + ((a^2) * (x^2) * (y^2)) + (a * b * y * (x^3)) + ((-2) * a * b * x * y)) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 95=0 at h69
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at h72
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h46-((y^2))*h50-(1)*h69-((((-4) + ((-1) * (x^6)) + (2 * (y^2)) + (3 * (x^4)) + ((-1) * (a^2) * (x^4)) + ((-1) * (x^2) * (y^2)) + (2 * (a^2) * (x^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * a * b * y * (x^3)) + (2 * a * b * x * y)) / ((x^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-((((-1) * (y^2)) / (x^2)))*h72
#print axioms reduced_step73

compact_certificate theorem reduced_step74 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 80=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h59 : reducedRows x y z a b w 59=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h68 : reducedRows x y z a b w 68=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 74=0 := by
  change (1) * w 10 + ((((-1) * a) / x)) * w 20 + ((1 / (x^2))) * w 40 + (1) * w 85=0 at hs
  have hs0 := hs
  change (1) * w 85=0
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change (1) * w 40 + (1) * w 110=0 at h59
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h39-((1 / (x^2)))*h59-(((x^2) / ((y^2) * ((-2) + (x^2)))))*h66-(((-1) / (x^2)))*h67-(((-1) * a * x))*h68-(((((-1) * a * (x^5)) + ((-1) * (a^3) * (x^3)) + (2 * b * y) + (4 * a * (x^3)) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((x^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-((((a * (x^5)) + ((a^3) * (x^3)) + ((-4) * a * (x^3)) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / (((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step74

compact_certificate theorem reduced_step75 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 81=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h56 : reducedRows x y z a b w 56=0)
    (h61 : reducedRows x y z a b w 61=0)
    (h70 : reducedRows x y z a b w 70=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h74 : reducedRows x y z a b w 74=0)
    : reducedRows x y z a b w 75=0 := by
  change ((1 / ((x^2) * (y^2)))) * w 0 + (1) * w 25 + (1) * w 55 + ((1 / ((x^2) * (y^2)))) * w 60 + (1) * w 85 + ((1 / ((x^2) * (y^2)))) * w 90 + (1) * w 115 + ((1 / ((x^2) * (y^2)))) * w 120=0 at hs
  have hs0 := hs
  change (1) * w 115=0
  change (1) * w 0=0 at h15
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114=0 at h56
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  change (((2 + ((-1) * (x^2)) + ((-4) * (y^2)) + ((-1) * (x^4) * (y^2)) + (4 * (x^2) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 55=0 at h70
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 85=0 at h74
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / ((x^2) * (y^2))))*h15-(1)*h50-((1 / (x^2)))*h53-(1)*h56-(1)*h61-(1)*h70-((((4 * (y^2)) + ((x^4) * (y^2)) + ((-4) * (x^2) * (y^2)) + ((a^2) * (x^2) * (y^2))) / ((x^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-(((4 + (x^6) + ((-4) * (y^2)) + ((-3) * (x^4)) + (a * x) + (a * (x^5)) + ((a^2) * (x^4)) + ((a^3) * (x^3)) + ((-1) * (x^4) * (y^2)) + ((-7) * a * (x^3)) + ((-2) * b * y) + ((-2) * (a^2) * (x^2)) + (4 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + ((-1) * b * y * (x^2)) + (a * b * y * (x^3)) + ((-2) * a * b * x * y)) / (((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73-(1)*h74
#print axioms reduced_step75

compact_certificate theorem reduced_step76 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 82=0)
    (h23 : reducedRows x y z a b w 23=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h46 : reducedRows x y z a b w 46=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 76=0 := by
  change (1) * w 35 + ((((-1) * a) / x)) * w 70 + (1) * w 110 + ((1 / (x^2))) * w 140=0 at hs
  have hs0 := hs
  change (1) * w 35=0
  change ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140=0 at h23
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change (((-1) / (y^2))) * w 30 + (1) * w 70=0 at h46
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h23-(((-1) / ((x^2) * (y^2))))*h31-((((-1) * a) / x))*h46-((1 / (x^2)))*h53-(((-1) / ((y^2) * ((-2) + (x^2)))))*h66-(1)*h67-(((a + ((-3) * a * (x^2)) + (a * (x^2) * (y^2)) + (b * y * (x^3)) + ((-2) * b * x * y)) / (x * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-(((((-1) * a * x) + (3 * a * (x^3)) + ((-1) * a * (x^3) * (y^2)) + ((-1) * b * y * (x^4)) + (2 * b * y * (x^2))) / (((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step76

compact_certificate theorem reduced_step77 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 83=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h57 : reducedRows x y z a b w 57=0)
    (h60 : reducedRows x y z a b w 60=0)
    (h69 : reducedRows x y z a b w 69=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h76 : reducedRows x y z a b w 76=0)
    : reducedRows x y z a b w 77=0 := by
  change ((1 / ((x^2) * (y^2)))) * w 0 + ((1 / ((x^2) * (y^2)))) * w 30 + (1) * w 35 + ((1 / ((x^2) * (y^2)))) * w 60 + (1) * w 65 + ((1 / ((x^2) * (y^2)))) * w 90 + (1) * w 95 + (1) * w 125=0 at hs
  have hs0 := hs
  change (1) * w 65=0
  change (1) * w 0=0 at h15
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125=0 at h57
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  change (((2 + (x^2) + (x^6) + ((-3) * (x^4)) + ((a^2) * (x^4)) + ((-2) * (a^2) * (x^2)) + ((a^2) * (x^2) * (y^2)) + (a * b * y * (x^3)) + ((-2) * a * b * x * y)) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 95=0 at h69
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 35=0 at h76
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / ((x^2) * (y^2))))*h15-((1 / (x^2)))*h53-(1)*h57-((((-1) * (z^2)) / (y^2)))*h60-(1)*h69-((((-4) + ((-1) * (x^6)) + (3 * (x^4)) + ((-1) * (a^2) * (x^4)) + (2 * (a^2) * (x^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * a * b * y * (x^3)) + (2 * a * b * x * y)) / ((x^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-(((((-1) * a * x) + ((-1) * a * (x^5)) + ((-1) * (a^3) * (x^3)) + (2 * b * y) + (7 * a * (x^3)) + (b * y * (x^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)) + ((-1) * b * y * (x^4))) / (((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73-(1)*h76
#print axioms reduced_step77

compact_certificate theorem reduced_step78 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 67=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h52 : reducedRows x y z a b w 52=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 78=0 := by
  change ((1 / ((x^2) * (z^2)))) * w 0 + (1) * w 51 + ((1 / ((x^2) * (z^2)))) * w 100 + (1) * w 101=0 at hs
  have hs0 := hs
  change (1) * w 51 + (1) * w 101=0
  change (1) * w 0=0 at h15
  change ((1 / (x^2))) * w 18 + (((y^2) / ((x^2) * (z^2)))) * w 100=0 at h52
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / ((x^2) * (z^2))))*h15-((1 / (y^2)))*h52-((((-4) + ((-1) * (x^4)) + (4 * (x^2)) + ((-1) * (a^2) * (x^2)) + (2 * b * y) + (3 * a * x) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step78

compact_certificate theorem reduced_step79 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 68=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h51 : reducedRows x y z a b w 51=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 79=0 := by
  change ((1 / ((x^2) * (z^2)))) * w 0 + (1) * w 49 + ((1 / ((x^2) * (z^2)))) * w 50 + (1) * w 99=0 at hs
  have hs0 := hs
  change (1) * w 49 + (1) * w 99=0
  change (1) * w 0=0 at h15
  change (((y^2) / ((x^2) * (z^2)))) * w 50 + ((1 / (x^2))) * w 132=0 at h51
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / ((x^2) * (z^2))))*h15-((1 / (y^2)))*h51-((1 / ((x^2) * (z^2))))*h58-(((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step79



compact_certificate theorem reduced_step80 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 69=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h51 : reducedRows x y z a b w 51=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 80=0 := by
  change ((1 / (z^2))) * w 0 + ((1 / (z^2))) * w 50 + (1) * w 52 + (1) * w 102=0 at hs
  have hs0 := hs
  change (1) * w 52 + (1) * w 102=0
  change (1) * w 0=0 at h15
  change (((y^2) / ((x^2) * (z^2)))) * w 50 + ((1 / (x^2))) * w 132=0 at h51
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (z^2)))*h15-(((x^2) / (y^2)))*h51-((1 / (z^2)))*h58-((((x^6) + ((-4) * (x^4)) + (4 * (x^2)) + ((a^2) * (x^4)) + ((-3) * a * (x^3)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + ((-2) * b * y * (x^2))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step80

compact_certificate theorem reduced_step81 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 70=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h52 : reducedRows x y z a b w 52=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 81=0 := by
  change ((1 / (z^2))) * w 0 + (1) * w 48 + (1) * w 98 + ((1 / (z^2))) * w 100=0 at hs
  have hs0 := hs
  change (1) * w 48 + (1) * w 98=0
  change (1) * w 0=0 at h15
  change ((1 / (x^2))) * w 18 + (((y^2) / ((x^2) * (z^2)))) * w 100=0 at h52
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (z^2)))*h15-(((x^2) / (y^2)))*h52-(((((-1) * (x^6)) + ((-4) * (x^2)) + (4 * (x^4)) + ((-1) * (a^2) * (x^4)) + (3 * a * (x^3)) + ((-1) * a * (x^3) * (y^2)) + ((-1) * b * y * (x^4)) + (2 * b * y * (x^2))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step81

compact_certificate theorem reduced_step82 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 71=0)
    (h16 : reducedRows x y z a b w 16=0)
    (h43 : reducedRows x y z a b w 43=0)
    (h56 : reducedRows x y z a b w 56=0)
    (h61 : reducedRows x y z a b w 61=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 82=0 := by
  change (((x^2) / (z^2))) * w 25 + (1) * w 54 + (((x^2) / (z^2))) * w 75 + (1) * w 104=0 at hs
  have hs0 := hs
  change ((y^2)) * w 14 + (1) * w 104=0
  change (1) * w 75=0 at h16
  change (((-1) * (y^2))) * w 14 + (1) * w 54=0 at h43
  change (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114=0 at h56
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((x^2) / (z^2)))*h16-(1)*h43-(((x^2) / (z^2)))*h56-(((x^2) / (z^2)))*h61-((((x^8) + ((-3) * (x^6)) + (4 * (x^2)) + (a * (x^3)) + (a * (x^7)) + ((a^2) * (x^6)) + ((a^3) * (x^5)) + ((-7) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + (a * (x^3) * (y^2)) + (a * (x^5) * (y^2)) + (b * y * (x^6)) + ((a^2) * (x^4) * (y^2)) + ((-1) * b * y * (x^4)) + ((-2) * b * y * (x^2)) + (a * b * y * (x^5)) + ((-2) * a * b * y * (x^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step82

compact_certificate theorem reduced_step83 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 72=0)
    (h16 : reducedRows x y z a b w 16=0)
    (h57 : reducedRows x y z a b w 57=0)
    (h60 : reducedRows x y z a b w 60=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 83=0 := by
  change (1) * w 46 + (((x^2) / (z^2))) * w 75 + (1) * w 96 + (((x^2) / (z^2))) * w 125=0 at hs
  have hs0 := hs
  change (1) * w 46 + (1) * w 96=0
  change (1) * w 75=0 at h16
  change (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125=0 at h57
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((x^2) / (z^2)))*h16-(((x^2) / (z^2)))*h57-((((-1) * (x^2)) / (y^2)))*h60-(((((-1) * (x^8)) + ((-4) * (x^2)) + (3 * (x^6)) + ((-1) * a * (x^3)) + ((-1) * a * (x^7)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^3) * (x^5)) + (2 * (a^2) * (x^4)) + (7 * a * (x^5)) + (b * y * (x^4)) + ((-1) * a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + (2 * b * y * (x^2)) + ((-1) * a * b * y * (x^5)) + (2 * a * b * y * (x^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step83

compact_certificate theorem reduced_step84 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 84=0)
    (h32 : reducedRows x y z a b w 32=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h60 : reducedRows x y z a b w 60=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 84=0 := by
  change ((1 / (z^2))) * w 30 + (1) * w 36 + ((1 / (z^2))) * w 60 + (1) * w 66 + ((1 / (z^2))) * w 90 + (1) * w 96 + ((1 / (z^2))) * w 120 + (1) * w 126=0 at hs
  have hs0 := hs
  change (1) * w 96 + (1) * w 126=0
  change ((-1)) * w 18 + (1) * w 66=0 at h32
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h32-((((x^2) * (y^2)) / (z^2)))*h50-(((y^2) / (z^2)))*h53-((x^2))*h60-(((((x^8) * (y^2)) + ((-4) * (x^4) * (y^2)) + ((-2) * (x^6) * (y^2)) + (8 * (x^2) * (y^2)) + (a * (x^5) * (y^4)) + (a * (x^7) * (y^2)) + (b * (x^6) * (y^3)) + ((a^2) * (x^4) * (y^4)) + ((a^2) * (x^6) * (y^2)) + ((a^3) * (x^5) * (y^2)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-7) * a * (x^5) * (y^2)) + ((-4) * b * (x^2) * (y^3)) + ((-2) * a * (x^3) * (y^2)) + (2 * a * (x^3) * (y^4)) + (a * b * (x^5) * (y^3)) + ((-2) * a * b * (x^3) * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step84

compact_certificate theorem reduced_step85 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 85=0)
    (h37 : reducedRows x y z a b w 37=0)
    (h43 : reducedRows x y z a b w 43=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h61 : reducedRows x y z a b w 61=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 85=0 := by
  change (1) * w 24 + ((1 / (z^2))) * w 30 + (1) * w 54 + ((1 / (z^2))) * w 60 + (1) * w 84 + ((1 / (z^2))) * w 90 + (1) * w 114 + ((1 / (z^2))) * w 120=0 at hs
  have hs0 := hs
  change ((y^2)) * w 14 + (1) * w 24=0
  change (1) * w 84 + ((-1)) * w 132=0 at h37
  change (((-1) * (y^2))) * w 14 + (1) * w 54=0 at h43
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h37-(1)*h43-((((x^2) * (y^2)) / (z^2)))*h50-(((y^2) / (z^2)))*h53-((((-1) * (y^2)) / (z^2)))*h58-((((-1) * (x^2) * (y^2)) / (z^2)))*h61-(((((-1) * (x^8) * (y^2)) + ((-8) * (x^2) * (y^2)) + (2 * (x^6) * (y^2)) + (4 * (x^4) * (y^2)) + ((a^2) * (x^4) * (y^2)) + ((-1) * a * (x^5) * (y^4)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * (x^6) * (y^3)) + ((-1) * (a^2) * (x^4) * (y^4)) + ((-1) * (a^2) * (x^6) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + (2 * a * (x^3) * (y^2)) + (4 * b * (x^2) * (y^3)) + (7 * a * (x^5) * (y^2)) + ((-1) * a * b * (x^5) * (y^3)) + (2 * a * b * (x^3) * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step85

compact_certificate theorem reduced_step86 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 86=0)
    (h7 : reducedRows x y z a b w 7=0)
    (h22 : reducedRows x y z a b w 22=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h54 : reducedRows x y z a b w 54=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h68 : reducedRows x y z a b w 68=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h72 : reducedRows x y z a b w 72=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 86=0 := by
  change (((x^2) / (z^2))) * w 15 + (1) * w 42 + (((x^2) / (z^2))) * w 45 + (1) * w 72 + (1) * w 102 + (((x^2) / (z^2))) * w 105 + (1) * w 132 + (((x^2) / (z^2))) * w 135=0 at hs
  have hs0 := hs
  change (1) * w 42 + (1) * w 102=0
  change (1) * w 72=0 at h7
  change ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135=0 at h22
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (1) * w 20 + (((x^2) / (y^2))) * w 105=0 at h54
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at h72
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h7-(((x^2) / (z^2)))*h22-(((-1) / (z^2)))*h31-(((-1) / (z^2)))*h39-(((y^2) / (z^2)))*h53-(((y^2) / (z^2)))*h54-((((-1) * (y^2)) / (z^2)))*h58-((((-1) * (x^2) * (y^2)) / (z^2)))*h68-(((((-2) * (y^2)) + ((-1) * (x^4) * (y^2)) + (3 * (x^2) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2))) / ((z^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-((((-1) * (y^2)) / (z^2)))*h72-(((((-1) * (x^6) * (y^2)) + ((-4) * (x^2) * (y^2)) + (4 * (x^4) * (y^2)) + ((-1) * a * (x^3) * (y^4)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^4) * (y^2)) + (2 * b * (x^2) * (y^3)) + (3 * a * (x^3) * (y^2))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step86

compact_certificate theorem reduced_step87 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 87=0)
    (h9 : reducedRows x y z a b w 9=0)
    (h22 : reducedRows x y z a b w 22=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h54 : reducedRows x y z a b w 54=0)
    (h68 : reducedRows x y z a b w 68=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h72 : reducedRows x y z a b w 72=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 87=0 := by
  change (((x^2) / (z^2))) * w 15 + (1) * w 18 + (((x^2) / (z^2))) * w 45 + (1) * w 48 + (1) * w 78 + (((x^2) / (z^2))) * w 105 + (1) * w 108 + (((x^2) / (z^2))) * w 135=0 at hs
  have hs0 := hs
  change (1) * w 48 + (1) * w 108=0
  change (1) * w 78=0 at h9
  change ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135=0 at h22
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (1) * w 20 + (((x^2) / (y^2))) * w 105=0 at h54
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at h72
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h9-(((x^2) / (z^2)))*h22-(((-1) / (z^2)))*h31-(((-1) / (z^2)))*h39-(((y^2) / (z^2)))*h53-(((y^2) / (z^2)))*h54-((((-1) * (x^2) * (y^2)) / (z^2)))*h68-(((((-2) * (y^2)) + ((-1) * (x^4) * (y^2)) + (3 * (x^2) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2))) / ((z^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-((((-1) * (y^2)) / (z^2)))*h72-(((((x^6) * (y^2)) + ((-4) * (x^4) * (y^2)) + (4 * (x^2) * (y^2)) + (a * (x^3) * (y^4)) + (b * (x^4) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * b * (x^2) * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step87

compact_certificate theorem reduced_step88 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 88=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h52 : reducedRows x y z a b w 52=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 88=0 := by
  change ((1 / (z^2))) * w 0 + (1) * w 26 + ((1 / (z^2))) * w 100 + (1) * w 126=0 at hs
  have hs0 := hs
  change (1) * w 26 + (1) * w 126=0
  change (1) * w 0=0 at h15
  change ((1 / (x^2))) * w 18 + (((y^2) / ((x^2) * (z^2)))) * w 100=0 at h52
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (z^2)))*h15-(((x^2) / (y^2)))*h52-(((((-1) * (x^6)) + ((-4) * (x^2)) + (4 * (x^4)) + ((-1) * (a^2) * (x^4)) + (3 * a * (x^3)) + ((-1) * a * (x^3) * (y^2)) + ((-1) * b * y * (x^4)) + (2 * b * y * (x^2))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step88

compact_certificate theorem reduced_step89 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 89=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h51 : reducedRows x y z a b w 51=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 89=0 := by
  change ((1 / (z^2))) * w 0 + (1) * w 24 + ((1 / (z^2))) * w 50 + (1) * w 124=0 at hs
  have hs0 := hs
  change (1) * w 24 + (1) * w 124=0
  change (1) * w 0=0 at h15
  change (((y^2) / ((x^2) * (z^2)))) * w 50 + ((1 / (x^2))) * w 132=0 at h51
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (z^2)))*h15-(((x^2) / (y^2)))*h51-((1 / (z^2)))*h58-((((x^6) + ((-4) * (x^4)) + (4 * (x^2)) + ((a^2) * (x^4)) + ((-3) * a * (x^3)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + ((-2) * b * y * (x^2))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step89



compact_certificate theorem reduced_step90 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 90=0)
    (h4 : reducedRows x y z a b w 4=0)
    (h14 : reducedRows x y z a b w 14=0)
    (h20 : reducedRows x y z a b w 20=0)
    (h28 : reducedRows x y z a b w 28=0)
    : reducedRows x y z a b w 90=0 := by
  change (1) * w 2 + ((((-1) * a) / x)) * w 4 + ((1 / (x^2))) * w 8 + (1) * w 77=0 at hs
  have hs0 := hs
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0
  change (1) * w 2=0 at h4
  change (((-1) * (y^2))) * w 4=0 at h14
  change (((-1) * (y^2))) * w 8 + (1) * w 126=0 at h20
  change (((-1) / ((x^2) * (y^2)))) * w 24 + (1) * w 77=0 at h28
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h4-((a / (x * (y^2))))*h14-(((-1) / ((x^2) * (y^2))))*h20-(1)*h28
#print axioms reduced_step90

compact_certificate theorem reduced_step91 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 91=0)
    (h32 : reducedRows x y z a b w 32=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 91=0 := by
  change (1) * w 33 + ((((-1) * a) / x)) * w 66 + (1) * w 108 + ((1 / (x^2))) * w 132=0 at hs
  have hs0 := hs
  change (1) * w 33 + (1) * w 108=0
  change ((-1)) * w 18 + (1) * w 66=0 at h32
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((-1) * a) / x))*h32-((((-1) * (y^2)) / ((x^2) * (z^2))))*h58-(((((-4) * (y^2)) + ((-1) * (x^4) * (y^2)) + (2 * b * (y^3)) + (4 * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * b * (x^2) * (y^3)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^3) * (x^3) * (y^2)) + (2 * (a^2) * (x^2) * (y^2)) + (4 * a * (x^3) * (y^2)) + ((-1) * a * b * (x^3) * (y^3)) + (2 * a * b * x * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step91

compact_certificate theorem reduced_step92 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 92=0)
    (h1 : reducedRows x y z a b w 1=0)
    (h10 : reducedRows x y z a b w 10=0)
    : reducedRows x y z a b w 92=0 := by
  change (1) * w 37 + ((((-1) * a) / x)) * w 74 + (1) * w 112 + ((1 / (x^2))) * w 148=0 at hs
  have hs0 := hs
  change (1) * w 37 + (1) * w 112=0
  change (((-1) * (y^2))) * w 148=0 at h1
  change (1) * w 74=0 at h10
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h1-((((-1) * a) / x))*h10
#print axioms reduced_step92

compact_certificate theorem reduced_step93 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 93=0)
    (h4 : reducedRows x y z a b w 4=0)
    (h8 : reducedRows x y z a b w 8=0)
    : reducedRows x y z a b w 93=0 := by
  change ((1 / (x^2))) * w 2 + (1) * w 38 + ((((-1) * a) / x)) * w 76 + (1) * w 113=0 at hs
  have hs0 := hs
  change (1) * w 38 + (1) * w 113=0
  change (1) * w 2=0 at h4
  change (1) * w 76=0 at h8
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h4-((((-1) * a) / x))*h8
#print axioms reduced_step93

compact_certificate theorem reduced_step94 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 94=0)
    (h37 : reducedRows x y z a b w 37=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 94=0 := by
  change ((1 / (x^2))) * w 18 + (1) * w 42 + ((((-1) * a) / x)) * w 84 + (1) * w 117=0 at hs
  have hs0 := hs
  change (1) * w 42 + (1) * w 117=0
  change (1) * w 84 + ((-1)) * w 132=0 at h37
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((-1) * a) / x))*h37-(((a * (y^2)) / (x * (z^2))))*h58-((((4 * (y^2)) + ((x^4) * (y^2)) + ((-4) * (x^2) * (y^2)) + ((-2) * b * (y^3)) + (a * x * (y^2)) + (a * x * (y^4)) + (a * (x^5) * (y^2)) + (b * (x^2) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^3) * (x^3) * (y^2)) + ((-4) * a * (x^3) * (y^2)) + ((-2) * (a^2) * (x^2) * (y^2)) + (a * b * (x^3) * (y^3)) + ((-2) * a * b * x * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step94

compact_certificate theorem reduced_step95 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 95=0)
    (h44 : reducedRows x y z a b w 44=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h62 : reducedRows x y z a b w 62=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h91 : reducedRows x y z a b w 91=0)
    : reducedRows x y z a b w 95=0 := by
  change ((1 / ((x^2) * (z^2)))) * w 30 + (1) * w 33 + ((1 / ((x^2) * (z^2)))) * w 60 + (1) * w 63 + ((1 / ((x^2) * (z^2)))) * w 90 + (1) * w 93 + ((1 / ((x^2) * (z^2)))) * w 120 + (1) * w 123=0 at hs
  have hs0 := hs
  change (((y^2) / (x^2))) * w 16 + ((-1)) * w 108 + (1) * w 123=0
  change ((((-1) * (y^2)) / (x^2))) * w 16 + (1) * w 63=0 at h44
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (((x + ((-1) * a) + ((-1) * a * (x^2)) + ((-1) * x * (a^2))) / x)) * w 18 + (1) * w 93=0 at h62
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 33 + (1) * w 108=0 at h91
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h44-(((y^2) / (z^2)))*h50-(((y^2) / ((x^2) * (z^2))))*h53-(1)*h62-(((((-1) * (x^6) * (y^2)) + ((-4) * (x^2) * (y^2)) + (4 * (x^4) * (y^2)) + (a * (x^7) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^4) * (y^4)) + ((a^2) * (x^6) * (y^2)) + ((a^3) * (x^3) * (y^4)) + ((a^3) * (x^5) * (y^2)) + ((a^4) * (x^4) * (y^2)) + ((-1) * a * (x^3) * (y^4)) + ((-1) * b * (x^4) * (y^3)) + ((-8) * (a^2) * (x^4) * (y^2)) + ((-3) * a * (x^5) * (y^2)) + ((-2) * (a^3) * (x^3) * (y^2)) + (2 * b * (x^2) * (y^3)) + (3 * a * (x^3) * (y^2)) + (4 * a * x * (y^2)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^4) * (y^3)) + ((-1) * a * b * (x^3) * (y^3)) + ((-2) * a * b * x * (y^3)) + ((-2) * b * (a^2) * (x^2) * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73-(1)*h91
#print axioms reduced_step95

compact_certificate theorem reduced_step96 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 96=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h65 : reducedRows x y z a b w 65=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h94 : reducedRows x y z a b w 94=0)
    : reducedRows x y z a b w 96=0 := by
  change (1) * w 27 + ((1 / ((x^2) * (z^2)))) * w 30 + (1) * w 57 + ((1 / ((x^2) * (z^2)))) * w 60 + (1) * w 87 + ((1 / ((x^2) * (z^2)))) * w 90 + (1) * w 117 + ((1 / ((x^2) * (z^2)))) * w 120=0 at hs
  have hs0 := hs
  change (1) * w 27 + ((-1)) * w 42 + (1) * w 87=0
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (((a + ((-1) * x) + (a * (x^2)) + (x * (a^2))) / x)) * w 18 + (1) * w 57=0 at h65
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 42 + (1) * w 117=0 at h94
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((y^2) / (z^2)))*h50-(((y^2) / ((x^2) * (z^2))))*h53-(1)*h65-(((((x^6) * (y^2)) + ((-4) * (x^4) * (y^2)) + (4 * (x^2) * (y^2)) + (a * (x^3) * (y^4)) + (b * (x^4) * (y^3)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^2) * (x^4) * (y^4)) + ((-1) * (a^2) * (x^6) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^4)) + ((-1) * (a^3) * (x^5) * (y^2)) + ((-1) * (a^4) * (x^4) * (y^2)) + ((-4) * a * x * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * b * (x^2) * (y^3)) + (2 * (a^3) * (x^3) * (y^2)) + (3 * a * (x^5) * (y^2)) + (8 * (a^2) * (x^4) * (y^2)) + (a * b * (x^3) * (y^3)) + ((-1) * a * b * (x^5) * (y^3)) + ((-1) * b * (a^2) * (x^4) * (y^3)) + (2 * a * b * x * (y^3)) + (2 * b * (a^2) * (x^2) * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73-(1)*h94
#print axioms reduced_step96

compact_certificate theorem reduced_step97 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 97=0)
    (h23 : reducedRows x y z a b w 23=0)
    (h29 : reducedRows x y z a b w 29=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h33 : reducedRows x y z a b w 33=0)
    (h36 : reducedRows x y z a b w 36=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h64 : reducedRows x y z a b w 64=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h68 : reducedRows x y z a b w 68=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    : reducedRows x y z a b w 97=0 := by
  change (((y^2) / ((x^2) * (z^2)))) * w 20 + (1) * w 39 + (1) * w 69 + (((y^2) / ((x^2) * (z^2)))) * w 80 + (1) * w 99 + (((y^2) / ((x^2) * (z^2)))) * w 110 + (1) * w 129 + (((y^2) / ((x^2) * (z^2)))) * w 140=0 at hs
  have hs0 := hs
  change ((1 / (x^2))) * w 24 + (((y^2) / (x^2))) * w 82 + (1) * w 99=0
  change ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140=0 at h23
  change (1) * w 80 + (((-1) / (y^2))) * w 120=0 at h29
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change (((-1) / (x^2))) * w 24 + (1) * w 69=0 at h33
  change (1) * w 82 + ((((-1) * (x^2)) / (y^2))) * w 129=0 at h36
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (((-1) + ((-1) * (x^2)) + ((-1) * a * x))) * w 18 + (1) * w 39=0 at h64
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((y^2) / ((x^2) * (z^2))))*h23-(((y^2) / ((x^2) * (z^2))))*h29-(((-1) / ((x^2) * (z^2))))*h31-(1)*h33-((((-1) * (y^2)) / (x^2)))*h36-(((y^2) / (z^2)))*h50-(((y^2) / ((x^2) * (z^2))))*h53-(1)*h64-(((-1) / ((z^2) * ((-2) + (x^2)))))*h66-(((y^2) / ((x^2) * (z^2))))*h67-(((y^2) / (z^2)))*h68-(((y^2) / ((x^2) * (z^2))))*h71-(((((-4) * (y^2)) + ((x^8) * (y^2)) + ((-1) * (x^4) * (y^2)) + ((-3) * (x^6) * (y^2)) + (2 * b * (y^3)) + (8 * (x^2) * (y^2)) + (a * (x^3) * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^4)) + (a * (x^7) * (y^2)) + (b * (x^6) * (y^3)) + ((a^2) * (x^4) * (y^4)) + ((a^2) * (x^6) * (y^2)) + ((a^3) * (x^5) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-7) * a * (x^5) * (y^2)) + ((-3) * b * (x^2) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (3 * a * x * (y^2)) + (a * b * (x^5) * (y^3)) + ((-2) * a * b * (x^3) * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73
#print axioms reduced_step97

compact_certificate theorem reduced_step98 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 98=0)
    (h35 : reducedRows x y z a b w 35=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h46 : reducedRows x y z a b w 46=0)
    (h55 : reducedRows x y z a b w 55=0)
    (h59 : reducedRows x y z a b w 59=0)
    (h63 : reducedRows x y z a b w 63=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h72 : reducedRows x y z a b w 72=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h78 : reducedRows x y z a b w 78=0)
    (h90 : reducedRows x y z a b w 90=0)
    : reducedRows x y z a b w 98=0 := by
  change (((y^2) / ((x^2) * (z^2)))) * w 10 + (1) * w 21 + (((y^2) / ((x^2) * (z^2)))) * w 40 + (1) * w 51 + (((y^2) / ((x^2) * (z^2)))) * w 70 + (1) * w 81 + (1) * w 111 + (((y^2) / ((x^2) * (z^2)))) * w 130=0 at hs
  have hs0 := hs
  change (1) * w 21 + (((-1) / (x^2))) * w 24 + ((-1)) * w 101=0
  change (1) * w 81 + (((-1) / (x^2))) * w 126=0 at h35
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change (((-1) / (y^2))) * w 30 + (1) * w 70=0 at h46
  change (((x^2) / (y^2))) * w 45 + (1) * w 130=0 at h55
  change (1) * w 40 + (1) * w 110=0 at h59
  change ((1 + (x^2) + (a * x))) * w 18 + (1) * w 111=0 at h63
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at h72
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 51 + (1) * w 101=0 at h78
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h35-(((-1) / ((x^2) * (z^2))))*h39-(((y^2) / ((x^2) * (z^2))))*h46-(((y^2) / ((x^2) * (z^2))))*h55-(((y^2) / ((x^2) * (z^2))))*h59-(1)*h63-((1 / ((z^2) * ((-2) + (x^2)))))*h66-((((-1) * (y^2)) / ((x^2) * (z^2))))*h67-(((((-2) * (y^2)) + ((x^2) * (y^2)) + (2 * b * (y^3)) + ((-1) * a * x * (y^4)) + ((-1) * b * (x^2) * (y^3)) + (3 * a * x * (y^2))) / ((x^2) * (z^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-(((y^2) / ((x^2) * (z^2))))*h72-((((4 * (y^2)) + ((x^4) * (y^2)) + ((-1) * (x^8) * (y^2)) + ((-8) * (x^2) * (y^2)) + ((-2) * b * (y^3)) + (3 * (x^6) * (y^2)) + (a * x * (y^4)) + (b * (x^4) * (y^3)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + ((-1) * a * (x^3) * (y^4)) + ((-1) * a * (x^5) * (y^4)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * (x^6) * (y^3)) + ((-1) * (a^2) * (x^4) * (y^4)) + ((-1) * (a^2) * (x^6) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + ((-3) * a * x * (y^2)) + (2 * (a^2) * (x^4) * (y^2)) + (3 * b * (x^2) * (y^3)) + (7 * a * (x^5) * (y^2)) + ((-1) * a * b * (x^5) * (y^3)) + (2 * a * b * (x^3) * (y^3))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73-(1)*h78-((y^2))*h90
#print axioms reduced_step98

compact_certificate theorem reduced_step99 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 99=0)
    (h40 : reducedRows x y z a b w 40=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h83 : reducedRows x y z a b w 83=0)
    (h84 : reducedRows x y z a b w 84=0)
    (h90 : reducedRows x y z a b w 90=0)
    : reducedRows x y z a b w 99=0 := by
  change (1) * w 16 + ((1 / ((y^2) * (z^2)))) * w 30 + (1) * w 46 + ((1 / ((y^2) * (z^2)))) * w 60 + ((1 / ((y^2) * (z^2)))) * w 90 + (1) * w 106 + ((1 / ((y^2) * (z^2)))) * w 120 + (1) * w 136=0 at hs
  have hs0 := hs
  change (1) * w 16 + (((1 + ((-1) * (y^2))) / (y^2))) * w 24 + (1) * w 106=0
  change (1) * w 96 + (((-1) * (y^2))) * w 136=0 at h40
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (1) * w 46 + (1) * w 96=0 at h83
  change (1) * w 96 + (1) * w 126=0 at h84
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h40-(((x^2) / (z^2)))*h50-((1 / (z^2)))*h53-(1)*h83-(((1 + ((-1) * (y^2))) / (y^2)))*h84-((((-1) * (x^2)) + ((x^2) * (y^2))))*h90
#print axioms reduced_step99



compact_certificate theorem reduced_step100 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 100=0)
    (h38 : reducedRows x y z a b w 38=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h82 : reducedRows x y z a b w 82=0)
    (h85 : reducedRows x y z a b w 85=0)
    : reducedRows x y z a b w 100=0 := by
  change (1) * w 14 + ((1 / ((y^2) * (z^2)))) * w 30 + (1) * w 44 + ((1 / ((y^2) * (z^2)))) * w 60 + ((1 / ((y^2) * (z^2)))) * w 90 + (1) * w 104 + ((1 / ((y^2) * (z^2)))) * w 120 + (1) * w 134=0 at hs
  have hs0 := hs
  change ((((-1) + (y^2)) / (y^2))) * w 24 + (1) * w 44 + (((x^2) / (y^2))) * w 87=0
  change (1) * w 87 + ((((-1) * (y^2)) / (x^2))) * w 134=0 at h38
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((y^2)) * w 14 + (1) * w 104=0 at h82
  change ((y^2)) * w 14 + (1) * w 24=0 at h85
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((-1) * (x^2)) / (y^2)))*h38-(((x^2) / (z^2)))*h50-((1 / (z^2)))*h53-(1)*h82-(((1 + ((-1) * (y^2))) / (y^2)))*h85
#print axioms reduced_step100

compact_certificate theorem reduced_step101 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 101=0)
    (h14 : reducedRows x y z a b w 14=0)
    (h20 : reducedRows x y z a b w 20=0)
    (h34 : reducedRows x y z a b w 34=0)
    (h86 : reducedRows x y z a b w 86=0)
    (h90 : reducedRows x y z a b w 90=0)
    : reducedRows x y z a b w 101=0 := by
  change (1) * w 4 + ((((-1) * a) / x)) * w 8 + ((1 / (x^2))) * w 16 + (1) * w 79=0 at hs
  have hs0 := hs
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0
  change (((-1) * (y^2))) * w 4=0 at h14
  change (((-1) * (y^2))) * w 8 + (1) * w 126=0 at h20
  change (1) * w 79 + (((-1) / ((x^2) * (y^2)))) * w 102=0 at h34
  change (1) * w 42 + (1) * w 102=0 at h86
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h14-((a / (x * (y^2))))*h20-(1)*h34-((1 / ((x^2) * (y^2))))*h86-(((-1) * a * x))*h90
#print axioms reduced_step101

compact_certificate theorem reduced_step102 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 102=0)
    (h13 : reducedRows x y z a b w 13=0)
    (h87 : reducedRows x y z a b w 87=0)
    (h100 : reducedRows x y z a b w 100=0)
    : reducedRows x y z a b w 102=0 := by
  change (1) * w 12 + ((((-1) * a) / x)) * w 24 + ((1 / (x^2))) * w 48 + (1) * w 87=0 at hs
  have hs0 := hs
  change (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / (x^2))) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 44 + (((-1) / (x^2))) * w 108=0
  change ((-1)) * w 12=0 at h13
  change (1) * w 48 + (1) * w 108=0 at h87
  change ((((-1) + (y^2)) / (y^2))) * w 24 + (1) * w 44 + (((x^2) / (y^2))) * w 87=0 at h100
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((-1))*h13-((1 / (x^2)))*h87-(((y^2) / (x^2)))*h100
#print axioms reduced_step102

compact_certificate theorem reduced_step103 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 103=0)
    (h49 : reducedRows x y z a b w 49=0)
    (h102 : reducedRows x y z a b w 102=0)
    : reducedRows x y z a b w 103=0 := by
  change (1) * w 11 + ((((-1) * a) / x)) * w 22 + ((1 / (x^2))) * w 44 + (1) * w 86=0 at hs
  have hs0 := hs
  change ((((-1) * a) / x)) * w 22 + (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 86=0
  change (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108=0 at h49
  change (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / (x^2))) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 44 + (((-1) / (x^2))) * w 108=0 at h102
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h49-(((-1) / (y^2)))*h102
#print axioms reduced_step103

compact_certificate theorem reduced_step104 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 104=0)
    (h42 : reducedRows x y z a b w 42=0)
    (h60 : reducedRows x y z a b w 60=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h80 : reducedRows x y z a b w 80=0)
    (h86 : reducedRows x y z a b w 86=0)
    (h88 : reducedRows x y z a b w 88=0)
    (h90 : reducedRows x y z a b w 90=0)
    : reducedRows x y z a b w 104=0 := by
  change (1) * w 13 + ((((-1) * a) / x)) * w 26 + ((1 / (x^2))) * w 52 + (1) * w 88=0 at hs
  have hs0 := hs
  change ((((-1) * a) / x)) * w 24 + ((1 / (x^2))) * w 42 + (1) * w 88=0
  change (((-1) * (x^2) * (y^2))) * w 13 + (1) * w 36=0 at h42
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 52 + (1) * w 102=0 at h80
  change (1) * w 42 + (1) * w 102=0 at h86
  change (1) * w 26 + (1) * w 126=0 at h88
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h42-((1 / (y^2)))*h60-(((4 + (x^6) + ((-3) * (x^4)) + (a * x) + (a * (x^5)) + ((a^2) * (x^4)) + ((a^3) * (x^3)) + ((-7) * a * (x^3)) + ((-2) * b * y) + ((-2) * (a^2) * (x^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + ((a^2) * (x^2) * (y^2)) + ((-1) * b * y * (x^2)) + (a * b * y * (x^3)) + ((-2) * a * b * x * y)) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73-((1 / (x^2)))*h80-(((-1) / (x^2)))*h86-((((-1) * a) / x))*h88-((a * x * (y^2)))*h90
#print axioms reduced_step104

compact_certificate theorem reduced_step105 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 105=0)
    (h8 : reducedRows x y z a b w 8=0)
    : reducedRows x y z a b w 105=0 := by
  change (1) * w 19 + ((((-1) * a) / x)) * w 38 + ((1 / (x^2))) * w 76 + (1) * w 94=0 at hs
  have hs0 := hs
  change (1) * w 19 + ((((-1) * a) / x)) * w 38 + (1) * w 94=0
  change (1) * w 76=0 at h8
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h8
#print axioms reduced_step105

compact_certificate theorem reduced_step106 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 106=0)
    (h37 : reducedRows x y z a b w 37=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h84 : reducedRows x y z a b w 84=0)
    (h90 : reducedRows x y z a b w 90=0)
    : reducedRows x y z a b w 106=0 := by
  change (1) * w 21 + ((((-1) * a) / x)) * w 42 + ((1 / (x^2))) * w 84 + (1) * w 96=0 at hs
  have hs0 := hs
  change (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42=0
  change (1) * w 84 + ((-1)) * w 132=0 at h37
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 96 + (1) * w 126=0 at h84
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h37-((((-1) * (y^2)) / ((x^2) * (z^2))))*h58-(((((-4) * (y^2)) + ((-1) * (x^4) * (y^2)) + (2 * b * (y^3)) + (4 * (x^2) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * b * (x^2) * (y^3)) + ((-1) * (a^2) * (x^2) * (y^2)) + (3 * a * x * (y^2))) / ((z^2) * ((-2) + (x^2)) * ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)))))*h73-(1)*h84-(((-1) * (x^2) * (y^2)))*h90
#print axioms reduced_step106

compact_certificate theorem reduced_step107 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 107=0)
    (h84 : reducedRows x y z a b w 84=0)
    (h87 : reducedRows x y z a b w 87=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h97 : reducedRows x y z a b w 97=0)
    : reducedRows x y z a b w 107=0 := by
  change (1) * w 24 + ((((-1) * a) / x)) * w 48 + ((1 / (x^2))) * w 96 + (1) * w 99=0 at hs
  have hs0 := hs
  change (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108=0
  change (1) * w 96 + (1) * w 126=0 at h84
  change (1) * w 48 + (1) * w 108=0 at h87
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change ((1 / (x^2))) * w 24 + (((y^2) / (x^2))) * w 82 + (1) * w 99=0 at h97
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h84-((((-1) * a) / x))*h87-(((-1) * (y^2)))*h90-(1)*h97
#print axioms reduced_step107

compact_certificate theorem reduced_step108 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 108=0)
    (h19 : reducedRows x y z a b w 19=0)
    (h85 : reducedRows x y z a b w 85=0)
    (h107 : reducedRows x y z a b w 107=0)
    : reducedRows x y z a b w 108=0 := by
  change (1) * w 7 + ((((-1) * a) / x)) * w 14 + ((1 / (x^2))) * w 28 + (1) * w 82=0 at hs
  have hs0 := hs
  change (((a + (x^3)) / (x * (y^2)))) * w 24 + ((1 / (x^2))) * w 28 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 108=0
  change (((-1) * (x^2) * (y^2))) * w 7 + (1) * w 108=0 at h19
  change ((y^2)) * w 14 + (1) * w 24=0 at h85
  change (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108=0 at h107
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h19-((((-1) * a) / (x * (y^2))))*h85-((((-1) * (x^2)) / (y^2)))*h107
#print axioms reduced_step108

compact_certificate theorem reduced_step109 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 109=0)
    (h10 : reducedRows x y z a b w 10=0)
    : reducedRows x y z a b w 109=0 := by
  change (1) * w 56 + ((1 / (x^2))) * w 74 + ((((-1) * a) / x)) * w 112 + (1) * w 131=0 at hs
  have hs0 := hs
  change (1) * w 56 + ((((-1) * a) / x)) * w 112 + (1) * w 131=0
  change (1) * w 74=0 at h10
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h10
#print axioms reduced_step109



compact_certificate theorem reduced_step110 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 110=0)
    (h41 : reducedRows x y z a b w 41=0)
    (h61 : reducedRows x y z a b w 61=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h81 : reducedRows x y z a b w 81=0)
    (h87 : reducedRows x y z a b w 87=0)
    (h89 : reducedRows x y z a b w 89=0)
    : reducedRows x y z a b w 110=0 := by
  change (1) * w 62 + ((1 / (x^2))) * w 98 + ((((-1) * a) / x)) * w 124 + (1) * w 137=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change ((a / x)) * w 24 + (1) * w 62 + ((1 / (x^2))) * w 108=0
  change (1) * w 114 + (((-1) * (x^2) * (y^2))) * w 137=0 at h41
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 48 + (1) * w 98=0 at h81
  change (1) * w 48 + (1) * w 108=0 at h87
  change (1) * w 24 + (1) * w 124=0 at h89
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h41 h61 h73 h81 h87 h89 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h41-(((-1) / (z^2)))*h61-((1 / (x^2)))*h81-(((-1) / (x^2)))*h87-((((-1) * a) / x))*h89
#print axioms reduced_step110

compact_certificate theorem reduced_step111 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 111=0)
    (h30 : reducedRows x y z a b w 30=0)
    (h99 : reducedRows x y z a b w 99=0)
    (h101 : reducedRows x y z a b w 101=0)
    : reducedRows x y z a b w 111=0 := by
  change (1) * w 64 + ((1 / (x^2))) * w 106 + ((((-1) * a) / x)) * w 128 + (1) * w 139=0 at hs
  have hs0 := hs
  change ((((-1) + (y^2) + (a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 64 + ((((-1) * a) / x)) * w 128=0
  change (1) * w 42 + (((-1) * (x^2) * (y^2))) * w 139=0 at h30
  change (1) * w 16 + (((1 + ((-1) * (y^2))) / (y^2))) * w 24 + (1) * w 106=0 at h99
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at h101
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h30-((1 / (x^2)))*h99-((-1))*h101
#print axioms reduced_step111

compact_certificate theorem reduced_step112 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 112=0)
    (h26 : reducedRows x y z a b w 26=0)
    (h40 : reducedRows x y z a b w 40=0)
    (h45 : reducedRows x y z a b w 45=0)
    (h84 : reducedRows x y z a b w 84=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h106 : reducedRows x y z a b w 106=0)
    : reducedRows x y z a b w 112=0 := by
  change (1) * w 68 + ((1 / (x^2))) * w 122 + ((((-1) * a) / x)) * w 136 + (1) * w 143=0 at hs
  have hs0 := hs
  change (((((-1) * a) + ((-1) * (x^3))) / (x * (y^2)))) * w 24 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 42 + ((1 / (x^2))) * w 122=0
  change (((-1) / ((x^2) * (y^2)))) * w 42 + (1) * w 143=0 at h26
  change (1) * w 96 + (((-1) * (y^2))) * w 136=0 at h40
  change ((((-1) * (x^2)) / (y^2))) * w 21 + (1) * w 68=0 at h45
  change (1) * w 96 + (1) * w 126=0 at h84
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42=0 at h106
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h26-((a / (x * (y^2))))*h40-(1)*h45-((((-1) * a) / (x * (y^2))))*h84-((a * x))*h90-(((x^2) / (y^2)))*h106
#print axioms reduced_step112

compact_certificate theorem reduced_step113 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 113=0)
    (h3 : reducedRows x y z a b w 3=0)
    (h43 : reducedRows x y z a b w 43=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h85 : reducedRows x y z a b w 85=0)
    (h99 : reducedRows x y z a b w 99=0)
    (h101 : reducedRows x y z a b w 101=0)
    : reducedRows x y z a b w 113=0 := by
  change (1) * w 6 + ((((-1) * b) / y)) * w 18 + ((1 / (y^2))) * w 54 + (1) * w 56 + (1) * w 106=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change ((((-2) + (y^2) + (a * x)) / (y^2))) * w 24 + (((-1) / (y^2))) * w 42 + (1) * w 56=0
  change ((-1)) * w 6=0 at h3
  change (((-1) * (y^2))) * w 14 + (1) * w 54=0 at h43
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change ((y^2)) * w 14 + (1) * w 24=0 at h85
  change (1) * w 16 + (((1 + ((-1) * (y^2))) / (y^2))) * w 24 + (1) * w 106=0 at h99
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at h101
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h3 h43 h73 h85 h99 h101 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((-1))*h3-((1 / (y^2)))*h43-((1 / (y^2)))*h85-(1)*h99-(((-1) * (x^2)))*h101
#print axioms reduced_step113

compact_certificate theorem reduced_step114 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 114=0)
    (h7 : reducedRows x y z a b w 7=0)
    (h20 : reducedRows x y z a b w 20=0)
    (h90 : reducedRows x y z a b w 90=0)
    : reducedRows x y z a b w 114=0 := by
  change (1) * w 8 + ((((-1) * b) / y)) * w 24 + (1) * w 58 + ((1 / (y^2))) * w 72 + (1) * w 108=0 at hs
  have hs0 := hs
  change ((((-1) + ((-1) * b * y)) / (y^2))) * w 24 + (1) * w 58 + (1) * w 108=0
  change (1) * w 72=0 at h7
  change (((-1) * (y^2))) * w 8 + (1) * w 126=0 at h20
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (y^2)))*h7-(((-1) / (y^2)))*h20-((x^2))*h90
#print axioms reduced_step114

compact_certificate theorem reduced_step115 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 115=0)
    (h49 : reducedRows x y z a b w 49=0)
    (h63 : reducedRows x y z a b w 63=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h91 : reducedRows x y z a b w 91=0)
    (h97 : reducedRows x y z a b w 97=0)
    (h107 : reducedRows x y z a b w 107=0)
    : reducedRows x y z a b w 115=0 := by
  change (1) * w 11 + ((((-1) * b) / y)) * w 33 + (1) * w 61 + ((1 / (y^2))) * w 99 + (1) * w 111=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change ((((-1) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 24 + (1) * w 61 + (((1 + ((-1) * a * x) + (b * y * (x^2))) / ((x^2) * (y^2)))) * w 108=0
  change (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108=0 at h49
  change ((1 + (x^2) + (a * x))) * w 18 + (1) * w 111=0 at h63
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 33 + (1) * w 108=0 at h91
  change ((1 / (x^2))) * w 24 + (((y^2) / (x^2))) * w 82 + (1) * w 99=0 at h97
  change (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108=0 at h107
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h49 h63 h73 h91 h97 h107 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h49-(1)*h63-((((-1) * b) / y))*h91-((1 / (y^2)))*h97-((1 / (y^2)))*h107
#print axioms reduced_step115

compact_certificate theorem reduced_step116 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 116=0)
    (h13 : reducedRows x y z a b w 13=0)
    (h60 : reducedRows x y z a b w 60=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h110 : reducedRows x y z a b w 110=0)
    : reducedRows x y z a b w 116=0 := by
  change (1) * w 12 + ((((-1) * b) / y)) * w 36 + (1) * w 62 + ((1 / (y^2))) * w 108 + (1) * w 112=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change ((((-1) * a) / x)) * w 24 + ((((x^2) + ((-1) * (y^2))) / ((x^2) * (y^2)))) * w 108 + (1) * w 112=0
  change ((-1)) * w 12=0 at h13
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change ((a / x)) * w 24 + (1) * w 62 + ((1 / (x^2))) * w 108=0 at h110
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h13 h60 h73 h110 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((-1))*h13-((((-1) * b * (x^2)) / y))*h60-(1)*h110
#print axioms reduced_step116

compact_certificate theorem reduced_step117 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 117=0)
    (h42 : reducedRows x y z a b w 42=0)
    (h44 : reducedRows x y z a b w 44=0)
    (h60 : reducedRows x y z a b w 60=0)
    (h64 : reducedRows x y z a b w 64=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h93 : reducedRows x y z a b w 93=0)
    (h94 : reducedRows x y z a b w 94=0)
    (h101 : reducedRows x y z a b w 101=0)
    : reducedRows x y z a b w 117=0 := by
  change (1) * w 13 + ((((-1) * b) / y)) * w 39 + (1) * w 63 + (1) * w 113 + ((1 / (y^2))) * w 117=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change ((((-1) * a) / x)) * w 24 + ((-1)) * w 38 + ((((y^2) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 42=0
  change (((-1) * (x^2) * (y^2))) * w 13 + (1) * w 36=0 at h42
  change ((((-1) * (y^2)) / (x^2))) * w 16 + (1) * w 63=0 at h44
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  change (((-1) + ((-1) * (x^2)) + ((-1) * a * x))) * w 18 + (1) * w 39=0 at h64
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 38 + (1) * w 113=0 at h93
  change (1) * w 42 + (1) * w 117=0 at h94
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at h101
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h42 h44 h60 h64 h73 h93 h94 h101 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h42-(1)*h44-((1 / (y^2)))*h60-((((-1) * b) / y))*h64-(1)*h93-((1 / (y^2)))*h94-((y^2))*h101
#print axioms reduced_step117

compact_certificate theorem reduced_step118 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 118=0)
    (h61 : reducedRows x y z a b w 61=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h85 : reducedRows x y z a b w 85=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h111 : reducedRows x y z a b w 111=0)
    : reducedRows x y z a b w 118=0 := by
  change (1) * w 14 + ((((-1) * b) / y)) * w 42 + (1) * w 64 + (1) * w 114 + ((1 / (y^2))) * w 126=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change ((y^2)) * w 14 + (1) * w 24=0 at h85
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change ((((-1) + (y^2) + (a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 64 + ((((-1) * a) / x)) * w 128=0 at h111
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h61 h73 h85 h90 h111 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((-1) * (x^2) * (y^2)) / (z^2)))*h61-((1 / (y^2)))*h85-((x^2))*h90-(1)*h111
#print axioms reduced_step118

compact_certificate theorem reduced_step119 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 119=0)
    (h9 : reducedRows x y z a b w 9=0)
    (h11 : reducedRows x y z a b w 11=0)
    (h20 : reducedRows x y z a b w 20=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h45 : reducedRows x y z a b w 45=0)
    (h46 : reducedRows x y z a b w 46=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h55 : reducedRows x y z a b w 55=0)
    (h59 : reducedRows x y z a b w 59=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h72 : reducedRows x y z a b w 72=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h106 : reducedRows x y z a b w 106=0)
    (h117 : reducedRows x y z a b w 117=0)
    (h118 : reducedRows x y z a b w 118=0)
    : reducedRows x y z a b w 119=0 := by
  change (1) * w 8 + ((1 / (z^2))) * w 10 + (1) * w 18 + ((1 / (z^2))) * w 30 + (1) * w 38 + ((1 / (z^2))) * w 40 + ((1 / (z^2))) * w 60 + (1) * w 68 + ((1 / (z^2))) * w 70 + (1) * w 78 + ((1 / (z^2))) * w 90 + (1) * w 108 + ((1 / (z^2))) * w 120 + (1) * w 128 + ((1 / (z^2))) * w 130 + (1) * w 138=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0
  change (1) * w 78=0 at h9
  change (1) * w 138=0 at h11
  change (((-1) * (y^2))) * w 8 + (1) * w 126=0 at h20
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change ((((-1) * (x^2)) / (y^2))) * w 21 + (1) * w 68=0 at h45
  change (((-1) / (y^2))) * w 30 + (1) * w 70=0 at h46
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (((x^2) / (y^2))) * w 45 + (1) * w 130=0 at h55
  change (1) * w 40 + (1) * w 110=0 at h59
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at h72
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42=0 at h106
  change ((((-1) * a) / x)) * w 24 + ((-1)) * w 38 + ((((y^2) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 42=0 at h117
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h9 h11 h20 h39 h45 h46 h50 h53 h55 h59 h66 h67 h71 h72 h73 h90 h106 h117 h118 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h9-(1)*h11-(((-1) / (y^2)))*h20-(((-1) / ((y^2) * (z^2))))*h39-(1)*h45-((1 / (z^2)))*h46-((((x^2) * (y^2)) / (z^2)))*h50-(((y^2) / (z^2)))*h53-((1 / (z^2)))*h55-((1 / (z^2)))*h59-(((x^2) / ((y^2) * (z^2) * ((-2) + (x^2)))))*h66-(((-1) / (z^2)))*h67-((((-2) + (x^2) + (2 * b * y) + (3 * a * x) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((z^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-((1 / (z^2)))*h72-((x^2))*h90-(((x^2) / (y^2)))*h106-((-1))*h117-((((x^2) + (x^4) + (a * x * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118
#print axioms reduced_step119



compact_certificate theorem reduced_step122 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 122=0)
    (h24 : reducedRows x y z a b w 24=0)
    (h35 : reducedRows x y z a b w 35=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h46 : reducedRows x y z a b w 46=0)
    (h47 : reducedRows x y z a b w 47=0)
    (h49 : reducedRows x y z a b w 49=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h55 : reducedRows x y z a b w 55=0)
    (h59 : reducedRows x y z a b w 59=0)
    (h63 : reducedRows x y z a b w 63=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h72 : reducedRows x y z a b w 72=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h87 : reducedRows x y z a b w 87=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h106 : reducedRows x y z a b w 106=0)
    (h109 : reducedRows x y z a b w 109=0)
    (h113 : reducedRows x y z a b w 113=0)
    (h116 : reducedRows x y z a b w 116=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 122=0 := by
  change ((1 / ((x^2) * (z^2)))) * w 10 + (1) * w 11 + (1) * w 21 + ((1 / ((x^2) * (z^2)))) * w 30 + ((1 / ((x^2) * (z^2)))) * w 40 + (1) * w 41 + ((1 / ((x^2) * (z^2)))) * w 60 + ((1 / ((x^2) * (z^2)))) * w 70 + (1) * w 71 + (1) * w 81 + ((1 / ((x^2) * (z^2)))) * w 90 + (1) * w 111 + ((1 / ((x^2) * (z^2)))) * w 120 + ((1 / ((x^2) * (z^2)))) * w 130 + (1) * w 131 + (1) * w 141=0 at hs
  have hs0 := hs
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  have hw30 := pivot71_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w hw18 h71
  change (1) * w 41 + (((((-1) * (x^5)) + (2 * (x^7)) + (a * (y^6)) + ((a^2) * (x^9)) + ((a^3) * (x^8)) + ((a^4) * (x^7)) + ((a^4) * (x^11)) + ((x^5) * (y^4)) + ((-1) * a * (y^4)) + ((-1) * (a^2) * (x^11)) + ((-4) * (a^2) * (x^7)) + ((-2) * a * (x^8)) + ((-2) * (a^3) * (x^6)) + ((-2) * (a^3) * (x^10)) + (2 * a * (x^6)) + (2 * a * (x^10)) + (2 * (a^2) * (x^5)) + (2 * (x^7) * (y^2)) + (a * (x^2) * (y^2)) + (a * (x^4) * (y^4)) + (a * (x^6) * (y^2)) + (a * (x^8) * (y^2)) + (x * (a^2) * (y^4)) + ((a^2) * (x^3) * (y^4)) + ((a^2) * (x^7) * (y^2)) + ((a^2) * (x^9) * (y^4)) + ((a^3) * (x^6) * (y^4)) + ((a^3) * (x^10) * (y^2)) + ((a^4) * (x^5) * (y^4)) + ((a^4) * (x^7) * (y^4)) + ((a^5) * (x^8) * (y^2)) + ((-1) * a * (x^4) * (y^6)) + ((-1) * a * (x^10) * (y^2)) + ((-1) * b * (x^5) * (y^3)) + ((-1) * b * (x^5) * (y^5)) + ((-1) * (a^2) * (x^5) * (y^2)) + ((-1) * (a^2) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^2) * (y^4)) + ((-1) * (a^4) * (x^7) * (y^2)) + ((-3) * (a^2) * (x^3) * (y^2)) + ((-3) * (a^2) * (x^5) * (y^4)) + ((-2) * a * (x^4) * (y^2)) + ((-2) * a * (x^6) * (y^4)) + ((-2) * b * y * (x^7)) + ((-2) * b * (x^7) * (y^3)) + ((-2) * (a^2) * (x^9) * (y^2)) + ((-2) * (a^3) * (x^8) * (y^2)) + (3 * (a^3) * (x^4) * (y^2)) + (a * b * (x^4) * (y^3)) + (a * b * (x^6) * (y^3)) + (b * y * (a^2) * (x^7)) + (b * y * (a^2) * (x^11)) + (b * (a^2) * (x^3) * (y^5)) + (b * (a^2) * (x^5) * (y^5)) + (b * (a^3) * (x^8) * (y^3)) + ((-1) * a * b * y * (x^6)) + ((-1) * a * b * y * (x^10)) + ((-1) * a * b * (x^8) * (y^3)) + ((-1) * b * (a^2) * (x^5) * (y^3))) / ((x^5) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0
  change (((-1) / (x^2))) * w 18 + (1) * w 141=0 at h24
  change (1) * w 81 + (((-1) / (x^2))) * w 126=0 at h35
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change (((-1) / (y^2))) * w 30 + (1) * w 70=0 at h46
  change (((-1) / ((x^2) * (y^2)))) * w 48 + (1) * w 71=0 at h47
  change (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108=0 at h49
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (((x^2) / (y^2))) * w 45 + (1) * w 130=0 at h55
  change (1) * w 40 + (1) * w 110=0 at h59
  change ((1 + (x^2) + (a * x))) * w 18 + (1) * w 111=0 at h63
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at h72
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 48 + (1) * w 108=0 at h87
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42=0 at h106
  change (1) * w 56 + ((((-1) * a) / x)) * w 112 + (1) * w 131=0 at h109
  change ((((-2) + (y^2) + (a * x)) / (y^2))) * w 24 + (((-1) / (y^2))) * w 42 + (1) * w 56=0 at h113
  change ((((-1) * a) / x)) * w 24 + ((((x^2) + ((-1) * (y^2))) / ((x^2) * (y^2)))) * w 108 + (1) * w 112=0 at h116
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h24 h35 h39 h46 h47 h49 h50 h53 h55 h59 h63 h66 h67 h71 h72 h73 h87 h90 h106 h109 h113 h116 h118 h119 h120 ⊢
  simp only [hw42,hw128,mul_zero,zero_add,add_zero] at hs0 h24 h35 h39 h46 h47 h49 h50 h53 h55 h59 h63 h66 h67 h71 h72 h73 h87 h90 h106 h109 h113 h116 h118 h119 h120 ⊢
  simp only [hw30,mul_zero,zero_add,add_zero] at hs0 h24 h35 h39 h46 h47 h49 h50 h53 h55 h59 h63 h66 h67 h71 h72 h73 h87 h90 h106 h109 h113 h116 h118 h119 h120 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h24-(1)*h35-(((-1) / ((x^2) * (y^2) * (z^2))))*h39-((1 / ((x^2) * (z^2))))*h46-(1)*h47-(((-1) / ((x^2) * (y^2))))*h49-(((y^2) / (z^2)))*h50-(((y^2) / ((x^2) * (z^2))))*h53-((1 / ((x^2) * (z^2))))*h55-((1 / ((x^2) * (z^2))))*h59-(1)*h63-((1 / ((y^2) * (z^2) * ((-2) + (x^2)))))*h66-(((-1) / ((x^2) * (z^2))))*h67-((1 / ((x^2) * (z^2))))*h72-((1 / ((x^2) * (y^2))))*h87-((y^2))*h90-(1)*h106-(1)*h109-((-1))*h113-((a / x))*h116-((((y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((((a * (y^2)) + ((-1) * a * (x^2))) / ((x^3) * (y^2))))*h119
#print axioms reduced_step122



compact_certificate theorem reduced_step123 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 123=0)
    (h7 : reducedRows x y z a b w 7=0)
    (h13 : reducedRows x y z a b w 13=0)
    (h23 : reducedRows x y z a b w 23=0)
    (h25 : reducedRows x y z a b w 25=0)
    (h29 : reducedRows x y z a b w 29=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h68 : reducedRows x y z a b w 68=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h107 : reducedRows x y z a b w 107=0)
    (h116 : reducedRows x y z a b w 116=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    : reducedRows x y z a b w 123=0 := by
  change (1) * w 12 + ((1 / (z^2))) * w 20 + (1) * w 22 + ((1 / (z^2))) * w 30 + (1) * w 42 + ((1 / (z^2))) * w 60 + (1) * w 72 + ((1 / (z^2))) * w 80 + (1) * w 82 + ((1 / (z^2))) * w 90 + ((1 / (z^2))) * w 110 + (1) * w 112 + ((1 / (z^2))) * w 120 + (1) * w 132 + ((1 / (z^2))) * w 140 + (1) * w 142=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  have hw30 := pivot71_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w hw18 h71
  change (1) * w 22 + ((((y^6) + ((-1) * (y^4)) + (a * (x^5)) + ((a^2) * (x^8)) + ((a^2) * (x^10)) + ((a^3) * (x^9)) + ((x^2) * (y^2)) + ((x^2) * (y^4)) + ((-1) * a * (x^9)) + ((-1) * (a^4) * (x^8)) + ((-1) * (x^4) * (y^2)) + ((-1) * (x^4) * (y^6)) + ((-3) * (a^2) * (x^6)) + ((-2) * a * (x^7)) + ((-2) * (x^6) * (y^2)) + ((-2) * (x^6) * (y^4)) + (3 * (a^3) * (x^7)) + (a * x * (y^4)) + (a * (x^9) * (y^4)) + (b * y * (x^10)) + (b * (x^4) * (y^3)) + ((a^2) * (x^6) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((a^3) * (x^5) * (y^4)) + ((a^3) * (x^7) * (y^4)) + ((a^4) * (x^8) * (y^2)) + ((-1) * a * (x^7) * (y^4)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^2) * (x^8) * (y^2)) + ((-1) * (a^3) * (x^7) * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * a * (x^5) * (y^4)) + ((-2) * a * (x^9) * (y^2)) + ((-2) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^3) * (y^4)) + (2 * a * (x^5) * (y^2)) + (2 * b * (x^6) * (y^3)) + (2 * (a^2) * (x^6) * (y^2)) + (3 * a * (x^7) * (y^2)) + (4 * (a^2) * (x^4) * (y^2)) + (a * b * (x^3) * (y^5)) + (a * b * (x^5) * (y^5)) + (b * (a^2) * (x^6) * (y^3)) + (b * (a^2) * (x^8) * (y^3)) + ((-1) * a * b * (x^5) * (y^3)) + ((-1) * b * y * (a^2) * (x^8)) + (2 * a * b * y * (x^7)) + (2 * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0
  change (1) * w 72=0 at h7
  change ((-1)) * w 12=0 at h13
  change ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140=0 at h23
  change (((-1) / (y^2))) * w 24 + (1) * w 142=0 at h25
  change (1) * w 80 + (((-1) / (y^2))) * w 120=0 at h29
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108=0 at h107
  change ((((-1) * a) / x)) * w 24 + ((((x^2) + ((-1) * (y^2))) / ((x^2) * (y^2)))) * w 108 + (1) * w 112=0 at h116
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h7 h13 h23 h25 h29 h31 h50 h53 h58 h66 h67 h68 h71 h73 h107 h116 h118 h119 h120 ⊢
  simp only [hw30,mul_zero,zero_add,add_zero] at hs0 h7 h13 h23 h25 h29 h31 h50 h53 h58 h66 h67 h68 h71 h73 h107 h116 h118 h119 h120 ⊢
  set D3 : ℂ := (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2))) with hD3
  set D4 : ℂ := ((-1) + (y^2) + (2 * (x^2)) + (a * x)) with hD4
  set D6 : ℂ := ((-2) + (x^2)) with hD6
  linear_combination (norm := (field_simp [hx,hy,hz,hP3,hP4,hP6]; dsimp only [D3,D4,D6]; ring)) hs0-(1)*h7-((-1))*h13-((1 / (z^2)))*h23-(1)*h25-((1 / (z^2)))*h29-(((-1) / ((y^2) * (z^2))))*h31-((((x^2) + ((x^2) * (y^2))) / (z^2)))*h50-(((1 + (y^2)) / (z^2)))*h53-((((-1) * (y^2)) / (z^2)))*h58-((((-1) * (x^2)) / ((y^2) * (z^2) * D6)))*h66-((1 / (z^2)))*h67-(((x^2) / (z^2)))*h68-((((-1) * (x^2)) / (y^2)))*h107-(1)*h116-(((((-1) * (x^2)) + ((-1) * (x^4)) + ((-1) * a * x * (y^2))) / D4))*h118-((((y^2) + ((-1) * (x^2)) + (a * (x^3))) / ((x^2) * (y^2))))*h119-((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((x^2) * (y^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^4)) + (3 * a * (x^5)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((x^2) * D3)))*h120
#print axioms reduced_step123



compact_certificate theorem reduced_step124 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 124=0)
    (h7 : reducedRows x y z a b w 7=0)
    (h32 : reducedRows x y z a b w 32=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h87 : reducedRows x y z a b w 87=0)
    (h112 : reducedRows x y z a b w 112=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h123 : reducedRows x y z a b w 123=0)
    : reducedRows x y z a b w 124=0 := by
  change (1) * w 22 + ((1 / (y^2))) * w 48 + ((((-1) * b) / y)) * w 66 + (1) * w 72 + (1) * w 122=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0
  change (1) * w 72=0 at h7
  change ((-1)) * w 18 + (1) * w 66=0 at h32
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 48 + (1) * w 108=0 at h87
  change (((((-1) * a) + ((-1) * (x^3))) / (x * (y^2)))) * w 24 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 42 + ((1 / (x^2))) * w 122=0 at h112
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change (1) * w 22 + ((((y^6) + ((-1) * (y^4)) + (a * (x^5)) + ((a^2) * (x^8)) + ((a^2) * (x^10)) + ((a^3) * (x^9)) + ((x^2) * (y^2)) + ((x^2) * (y^4)) + ((-1) * a * (x^9)) + ((-1) * (a^4) * (x^8)) + ((-1) * (x^4) * (y^2)) + ((-1) * (x^4) * (y^6)) + ((-3) * (a^2) * (x^6)) + ((-2) * a * (x^7)) + ((-2) * (x^6) * (y^2)) + ((-2) * (x^6) * (y^4)) + (3 * (a^3) * (x^7)) + (a * x * (y^4)) + (a * (x^9) * (y^4)) + (b * y * (x^10)) + (b * (x^4) * (y^3)) + ((a^2) * (x^6) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((a^3) * (x^5) * (y^4)) + ((a^3) * (x^7) * (y^4)) + ((a^4) * (x^8) * (y^2)) + ((-1) * a * (x^7) * (y^4)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^2) * (x^8) * (y^2)) + ((-1) * (a^3) * (x^7) * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * a * (x^5) * (y^4)) + ((-2) * a * (x^9) * (y^2)) + ((-2) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^3) * (y^4)) + (2 * a * (x^5) * (y^2)) + (2 * b * (x^6) * (y^3)) + (2 * (a^2) * (x^6) * (y^2)) + (3 * a * (x^7) * (y^2)) + (4 * (a^2) * (x^4) * (y^2)) + (a * b * (x^3) * (y^5)) + (a * b * (x^5) * (y^5)) + (b * (a^2) * (x^6) * (y^3)) + (b * (a^2) * (x^8) * (y^3)) + ((-1) * a * b * (x^5) * (y^3)) + ((-1) * b * y * (a^2) * (x^8)) + (2 * a * b * y * (x^7)) + (2 * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h123
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h7 h32 h73 h87 h112 h118 h119 h120 h123 ⊢
  set D3 : ℂ := (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2))) with hD3
  set D4 : ℂ := ((-1) + (y^2) + (2 * (x^2)) + (a * x)) with hD4
  linear_combination (norm := (field_simp [hx,hy,hz,hP3,hP4]; dsimp only [D3,D4]; ring)) hs0-(1)*h7-((((-1) * b) / y))*h32-((1 / (y^2)))*h87-((x^2))*h112-(((((-1) * (x^6)) + ((-1) * a * (x^3))) / D4))*h118-(((-1) / (y^2)))*h119-(((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + (a * (x^3)) + ((a^2) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2))) / D3))*h120-(1)*h123
#print axioms reduced_step124




compact_certificate theorem reduced_step125 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 125=0)
    (h22 : reducedRows x y z a b w 22=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h54 : reducedRows x y z a b w 54=0)
    (h68 : reducedRows x y z a b w 68=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h72 : reducedRows x y z a b w 72=0)
    (h88 : reducedRows x y z a b w 88=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h103 : reducedRows x y z a b w 103=0)
    (h113 : reducedRows x y z a b w 113=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h123 : reducedRows x y z a b w 123=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 125=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (((x^2) / ((y^2) * (z^2)))) * w 15 + (1) * w 26 + (((x^2) / ((y^2) * (z^2)))) * w 45 + (1) * w 56 + (1) * w 86 + (((x^2) / ((y^2) * (z^2)))) * w 105 + (1) * w 116 + (((x^2) / ((y^2) * (z^2)))) * w 135=0 at hs
  have hs0 := hs
  change (1) * w 116=0
  change ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135=0 at h22
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (1) * w 20 + (((x^2) / (y^2))) * w 105=0 at h54
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at h72
  change (1) * w 26 + (1) * w 126=0 at h88
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change ((((-1) * a) / x)) * w 22 + (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 86=0 at h103
  change ((((-2) + (y^2) + (a * x)) / (y^2))) * w 24 + (((-1) / (y^2))) * w 42 + (1) * w 56=0 at h113
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change (1) * w 22 + ((((y^6) + ((-1) * (y^4)) + (a * (x^5)) + ((a^2) * (x^8)) + ((a^2) * (x^10)) + ((a^3) * (x^9)) + ((x^2) * (y^2)) + ((x^2) * (y^4)) + ((-1) * a * (x^9)) + ((-1) * (a^4) * (x^8)) + ((-1) * (x^4) * (y^2)) + ((-1) * (x^4) * (y^6)) + ((-3) * (a^2) * (x^6)) + ((-2) * a * (x^7)) + ((-2) * (x^6) * (y^2)) + ((-2) * (x^6) * (y^4)) + (3 * (a^3) * (x^7)) + (a * x * (y^4)) + (a * (x^9) * (y^4)) + (b * y * (x^10)) + (b * (x^4) * (y^3)) + ((a^2) * (x^6) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((a^3) * (x^5) * (y^4)) + ((a^3) * (x^7) * (y^4)) + ((a^4) * (x^8) * (y^2)) + ((-1) * a * (x^7) * (y^4)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^2) * (x^8) * (y^2)) + ((-1) * (a^3) * (x^7) * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * a * (x^5) * (y^4)) + ((-2) * a * (x^9) * (y^2)) + ((-2) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^3) * (y^4)) + (2 * a * (x^5) * (y^2)) + (2 * b * (x^6) * (y^3)) + (2 * (a^2) * (x^6) * (y^2)) + (3 * a * (x^7) * (y^2)) + (4 * (a^2) * (x^4) * (y^2)) + (a * b * (x^3) * (y^5)) + (a * b * (x^5) * (y^5)) + (b * (a^2) * (x^6) * (y^3)) + (b * (a^2) * (x^8) * (y^3)) + ((-1) * a * b * (x^5) * (y^3)) + ((-1) * b * y * (a^2) * (x^8)) + (2 * a * b * y * (x^7)) + (2 * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h123
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h22 h31 h39 h53 h54 h68 h71 h72 h88 h90 h103 h113 h118 h120 h123 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((x^2) / ((y^2) * (z^2))))*h22-(((-1) / ((y^2) * (z^2))))*h31-(((-1) / ((y^2) * (z^2))))*h39-((1 / (z^2)))*h53-((1 / (z^2)))*h54-((((-1) * (x^2)) / (z^2)))*h68-((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((z^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-(((-1) / (z^2)))*h72-(1)*h88-(((-1) * (x^2) * (y^2)))*h90-(1)*h103-(1)*h113-(((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + (a * (x^3)) + ((-1) * a * x)) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((a / x))*h123
#print axioms reduced_step125



compact_certificate theorem reduced_step126 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 126=0)
    (h85 : reducedRows x y z a b w 85=0)
    (h108 : reducedRows x y z a b w 108=0)
    (h113 : reducedRows x y z a b w 113=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 126=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 14 + ((((-1) * a) / x)) * w 28 + ((1 / (x^2))) * w 56 + (1) * w 89=0 at hs
  have hs0 := hs
  change (1) * w 89=0
  change ((y^2)) * w 14 + (1) * w 24=0 at h85
  change (((a + (x^3)) / (x * (y^2)))) * w 24 + ((1 / (x^2))) * w 28 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 108=0 at h108
  change ((((-2) + (y^2) + (a * x)) / (y^2))) * w 24 + (((-1) / (y^2))) * w 42 + (1) * w 56=0 at h113
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h85 h108 h113 h118 h119 h120 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (y^2)))*h85-(((-1) * a * x))*h108-((1 / (x^2)))*h113-((((-2) + (x^2) + (y^2) + (a * x) + ((-1) * a * (x^5)) + ((-1) * (a^2) * (x^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-(((a + ((a^2) * (x^3))) / (x * (y^2))))*h119
#print axioms reduced_step126




compact_certificate theorem reduced_step127 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 127=0)
    (h102 : reducedRows x y z a b w 102=0)
    (h104 : reducedRows x y z a b w 104=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h123 : reducedRows x y z a b w 123=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 127=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 22 + ((((-1) * a) / x)) * w 44 + ((1 / (x^2))) * w 88 + (1) * w 97=0 at hs
  have hs0 := hs
  change (1) * w 97=0
  change (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / (x^2))) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 44 + (((-1) / (x^2))) * w 108=0 at h102
  change ((((-1) * a) / x)) * w 24 + ((1 / (x^2))) * w 42 + (1) * w 88=0 at h104
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change (1) * w 22 + ((((y^6) + ((-1) * (y^4)) + (a * (x^5)) + ((a^2) * (x^8)) + ((a^2) * (x^10)) + ((a^3) * (x^9)) + ((x^2) * (y^2)) + ((x^2) * (y^4)) + ((-1) * a * (x^9)) + ((-1) * (a^4) * (x^8)) + ((-1) * (x^4) * (y^2)) + ((-1) * (x^4) * (y^6)) + ((-3) * (a^2) * (x^6)) + ((-2) * a * (x^7)) + ((-2) * (x^6) * (y^2)) + ((-2) * (x^6) * (y^4)) + (3 * (a^3) * (x^7)) + (a * x * (y^4)) + (a * (x^9) * (y^4)) + (b * y * (x^10)) + (b * (x^4) * (y^3)) + ((a^2) * (x^6) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((a^3) * (x^5) * (y^4)) + ((a^3) * (x^7) * (y^4)) + ((a^4) * (x^8) * (y^2)) + ((-1) * a * (x^7) * (y^4)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^2) * (x^8) * (y^2)) + ((-1) * (a^3) * (x^7) * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * a * (x^5) * (y^4)) + ((-2) * a * (x^9) * (y^2)) + ((-2) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^3) * (y^4)) + (2 * a * (x^5) * (y^2)) + (2 * b * (x^6) * (y^3)) + (2 * (a^2) * (x^6) * (y^2)) + (3 * a * (x^7) * (y^2)) + (4 * (a^2) * (x^4) * (y^2)) + (a * b * (x^3) * (y^5)) + (a * b * (x^5) * (y^5)) + (b * (a^2) * (x^6) * (y^3)) + (b * (a^2) * (x^8) * (y^3)) + ((-1) * a * b * (x^5) * (y^3)) + ((-1) * b * y * (a^2) * (x^8)) + (2 * a * b * y * (x^7)) + (2 * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h123
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h102 h104 h118 h119 h120 h123 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((a * x) / (y^2)))*h102-((1 / (x^2)))*h104-((((a * (x^2)) + ((-1) * a * (y^2)) + ((-1) * (a^2) * (x^3)) + ((-1) * a * (x^2) * (y^2))) / (x * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))))*h118-((a / (x * (y^2))))*h119-(1)*h123
#print axioms reduced_step127



compact_certificate theorem reduced_step128 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 128=0)
    (h108 : reducedRows x y z a b w 108=0)
    (h113 : reducedRows x y z a b w 113=0)
    (h116 : reducedRows x y z a b w 116=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 128=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 28 + ((((-1) * a) / x)) * w 56 + (1) * w 103 + ((1 / (x^2))) * w 112=0 at hs
  have hs0 := hs
  change (1) * w 103=0
  change (((a + (x^3)) / (x * (y^2)))) * w 24 + ((1 / (x^2))) * w 28 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 108=0 at h108
  change ((((-2) + (y^2) + (a * x)) / (y^2))) * w 24 + (((-1) / (y^2))) * w 42 + (1) * w 56=0 at h113
  change ((((-1) * a) / x)) * w 24 + ((((x^2) + ((-1) * (y^2))) / ((x^2) * (y^2)))) * w 108 + (1) * w 112=0 at h116
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h108 h113 h116 h118 h119 h120 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((x^2))*h108-((((-1) * a) / x))*h113-((1 / (x^2)))*h116-((((x^7) + (a * (x^4)) + ((-1) * a * (y^2)) + ((-1) * (a^2) * (x^3)) + (2 * a * (x^2)) + ((-1) * a * (x^2) * (y^2))) / (x * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))))*h118-((((y^2) + ((-1) * (x^2)) + ((-1) * (x^4)) + ((-1) * a * (x^7))) / ((x^4) * (y^2))))*h119
#print axioms reduced_step128




compact_certificate theorem reduced_step129 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 129=0)
    (h82 : reducedRows x y z a b w 82=0)
    (h85 : reducedRows x y z a b w 85=0)
    (h114 : reducedRows x y z a b w 114=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h125 : reducedRows x y z a b w 125=0)
    : reducedRows x y z a b w 129=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 29 + ((((-1) * a) / x)) * w 58 + (1) * w 104 + ((1 / (x^2))) * w 116=0 at hs
  have hs0 := hs
  change (1) * w 29=0
  change ((y^2)) * w 14 + (1) * w 104=0 at h82
  change ((y^2)) * w 14 + (1) * w 24=0 at h85
  change ((((-1) + ((-1) * b * y)) / (y^2))) * w 24 + (1) * w 58 + (1) * w 108=0 at h114
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 116=0 at h125
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h82 h85 h114 h118 h119 h120 h124 h125 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h82-((-1))*h85-((((-1) * a) / x))*h114-((((a * x) + ((-1) * (x^2) * (y^2)) + (a * b * x * y)) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((a / x))*h119-((1 / (x^2)))*h125
#print axioms reduced_step129

end QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative
end

section
/-! One complete certificate family; numbered development parts merged. -/


section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 16384

namespace QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative

compact_certificate theorem reduced_step120 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 120=0)
    (h9 : reducedRows x y z a b w 9=0)
    (h37 : reducedRows x y z a b w 37=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h86 : reducedRows x y z a b w 86=0)
    (h108 : reducedRows x y z a b w 108=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    : reducedRows x y z a b w 120=0 := by
  change (1) * w 28 + (1) * w 78 + ((((-1) * b) / y)) * w 84 + ((1 / (y^2))) * w 102 + (1) * w 128=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0
  change (1) * w 78=0 at h9
  change (1) * w 84 + ((-1)) * w 132=0 at h37
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 42 + (1) * w 102=0 at h86
  change (((a + (x^3)) / (x * (y^2)))) * w 24 + ((1 / (x^2))) * w 28 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 108=0 at h108
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h9 h37 h58 h73 h86 h108 h118 h119 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h9-((((-1) * b) / y))*h37-(((b * y) / (z^2)))*h58-((1 / (y^2)))*h86-((x^2))*h108-((((x^6) + (a * (x^3))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((((-1) + ((-1) * a * (x^3))) / (y^2)))*h119
#print axioms reduced_step120

compact_certificate theorem reduced_step121 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 121=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h104 : reducedRows x y z a b w 104=0)
    (h108 : reducedRows x y z a b w 108=0)
    (h114 : reducedRows x y z a b w 114=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 121=0 := by
  change (1) * w 28 + ((1 / ((y^2) * (z^2)))) * w 30 + (1) * w 58 + ((1 / ((y^2) * (z^2)))) * w 60 + (1) * w 88 + ((1 / ((y^2) * (z^2)))) * w 90 + (1) * w 118 + ((1 / ((y^2) * (z^2)))) * w 120=0 at hs
  have hs0 := hs
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change ((((a * (x^2)) + ((a^2) * (x^5)) + ((-1) * a * (x^4)) + ((-1) * (a^2) * (x^7)) + (a * b * (y^3)) + ((a^2) * (x^7) * (y^2)) + ((a^3) * (x^2) * (y^2)) + ((a^3) * (x^4) * (y^2)) + ((a^4) * (x^5) * (y^2)) + ((b^2) * (x^3) * (y^2)) + ((b^2) * (x^3) * (y^4)) + ((-1) * a * (x^2) * (y^2)) + ((-1) * a * (x^2) * (y^4)) + ((-1) * a * (x^4) * (y^2)) + ((-1) * b * y * (x^5)) + ((-1) * b * (x^5) * (y^3)) + ((-1) * (a^2) * (x^3) * (y^2)) + ((-2) * (a^2) * (x^5) * (y^2)) + (a * (b^2) * (x^6) * (y^2)) + (b * y * (a^2) * (x^3)) + (b * y * (a^3) * (x^6)) + (b * (a^2) * (x^3) * (y^3)) + ((-1) * a * b * y * (x^2)) + ((-1) * a * b * y * (x^8)) + ((-1) * a * b * (x^2) * (y^3)) + ((-1) * b * y * (a^2) * (x^5))) / (x * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42 + (1) * w 118=0
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) * a) / x)) * w 24 + ((1 / (x^2))) * w 42 + (1) * w 88=0 at h104
  change (((a + (x^3)) / (x * (y^2)))) * w 24 + ((1 / (x^2))) * w 28 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 108=0 at h108
  change ((((-1) + ((-1) * b * y)) / (y^2))) * w 24 + (1) * w 58 + (1) * w 108=0 at h114
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  simp only [hw42,hw128,mul_zero,zero_add,add_zero] at hs0 h50 h53 h104 h108 h114 h118 h119 h120 ⊢
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((x^2) / (z^2)))*h50-((1 / (z^2)))*h53-(1)*h104-((x^2))*h108-(1)*h114-((((x^6) + ((-1) * (x^2)) + (a * (x^3)) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((((-1) + ((-1) * (y^2)) + ((-1) * a * (x^3))) / (y^2)))*h119
#print axioms reduced_step121

end QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative
end
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 0
set_option maxRecDepth 16384

namespace QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative

compact_certificate theorem reduced_step130 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 130=0)
    (h89 : reducedRows x y z a b w 89=0)
    (h99 : reducedRows x y z a b w 99=0)
    (h101 : reducedRows x y z a b w 101=0)
    (h110 : reducedRows x y z a b w 110=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 130=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 31 + ((((-1) * a) / x)) * w 62 + (1) * w 106 + ((1 / (x^2))) * w 124=0 at hs
  have hs0 := hs
  change (1) * w 31=0
  change (1) * w 24 + (1) * w 124=0 at h89
  change (1) * w 16 + (((1 + ((-1) * (y^2))) / (y^2))) * w 24 + (1) * w 106=0 at h99
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at h101
  change ((a / x)) * w 24 + (1) * w 62 + ((1 / (x^2))) * w 108=0 at h110
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h89 h99 h101 h110 h118 h119 h120 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h89-(1)*h99-(((-1) * (x^2)))*h101-((((-1) * a) / x))*h110-((((x^2) + (y^2) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2)) + ((-1) * (x^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((a / (x^3)))*h119
#print axioms reduced_step130




compact_certificate theorem reduced_step131 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 131=0)
    (h103 : reducedRows x y z a b w 103=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h121 : reducedRows x y z a b w 121=0)
    (h123 : reducedRows x y z a b w 123=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 131=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change ((1 / (x^2))) * w 22 + (1) * w 43 + ((((-1) * a) / x)) * w 86 + (1) * w 118=0 at hs
  have hs0 := hs
  change (1) * w 43=0
  change ((((-1) * a) / x)) * w 22 + (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 86=0 at h103
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((a * (x^2)) + ((a^2) * (x^5)) + ((-1) * a * (x^4)) + ((-1) * (a^2) * (x^7)) + (a * b * (y^3)) + ((a^2) * (x^7) * (y^2)) + ((a^3) * (x^2) * (y^2)) + ((a^3) * (x^4) * (y^2)) + ((a^4) * (x^5) * (y^2)) + ((b^2) * (x^3) * (y^2)) + ((b^2) * (x^3) * (y^4)) + ((-1) * a * (x^2) * (y^2)) + ((-1) * a * (x^2) * (y^4)) + ((-1) * a * (x^4) * (y^2)) + ((-1) * b * y * (x^5)) + ((-1) * b * (x^5) * (y^3)) + ((-1) * (a^2) * (x^3) * (y^2)) + ((-2) * (a^2) * (x^5) * (y^2)) + (a * (b^2) * (x^6) * (y^2)) + (b * y * (a^2) * (x^3)) + (b * y * (a^3) * (x^6)) + (b * (a^2) * (x^3) * (y^3)) + ((-1) * a * b * y * (x^2)) + ((-1) * a * b * y * (x^8)) + ((-1) * a * b * (x^2) * (y^3)) + ((-1) * b * y * (a^2) * (x^5))) / (x * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42 + (1) * w 118=0 at h121
  change (1) * w 22 + ((((y^6) + ((-1) * (y^4)) + (a * (x^5)) + ((a^2) * (x^8)) + ((a^2) * (x^10)) + ((a^3) * (x^9)) + ((x^2) * (y^2)) + ((x^2) * (y^4)) + ((-1) * a * (x^9)) + ((-1) * (a^4) * (x^8)) + ((-1) * (x^4) * (y^2)) + ((-1) * (x^4) * (y^6)) + ((-3) * (a^2) * (x^6)) + ((-2) * a * (x^7)) + ((-2) * (x^6) * (y^2)) + ((-2) * (x^6) * (y^4)) + (3 * (a^3) * (x^7)) + (a * x * (y^4)) + (a * (x^9) * (y^4)) + (b * y * (x^10)) + (b * (x^4) * (y^3)) + ((a^2) * (x^6) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((a^3) * (x^5) * (y^4)) + ((a^3) * (x^7) * (y^4)) + ((a^4) * (x^8) * (y^2)) + ((-1) * a * (x^7) * (y^4)) + ((-1) * (a^2) * (x^2) * (y^4)) + ((-1) * (a^2) * (x^8) * (y^2)) + ((-1) * (a^3) * (x^7) * (y^2)) + ((-3) * a * (x^3) * (y^2)) + ((-2) * a * (x^5) * (y^4)) + ((-2) * a * (x^9) * (y^2)) + ((-2) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^3) * (y^4)) + (2 * a * (x^5) * (y^2)) + (2 * b * (x^6) * (y^3)) + (2 * (a^2) * (x^6) * (y^2)) + (3 * a * (x^7) * (y^2)) + (4 * (a^2) * (x^4) * (y^2)) + (a * b * (x^3) * (y^5)) + (a * b * (x^5) * (y^5)) + (b * (a^2) * (x^6) * (y^3)) + (b * (a^2) * (x^8) * (y^3)) + ((-1) * a * b * (x^5) * (y^3)) + ((-1) * b * y * (a^2) * (x^8)) + (2 * a * b * y * (x^7)) + (2 * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h123
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h103 h118 h120 h121 h123 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((-1) * a) / x))*h103-(((((-1) * a) + (a * (y^2)) + (x * (a^2))) / (x * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))))*h118-(1)*h121-(((1 + ((-1) * (a^2))) / (x^2)))*h123
#print axioms reduced_step131




compact_certificate theorem reduced_step132 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 132=0)
    (h88 : reducedRows x y z a b w 88=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h102 : reducedRows x y z a b w 102=0)
    (h104 : reducedRows x y z a b w 104=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 132=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change ((1 / (x^2))) * w 26 + (1) * w 44 + ((((-1) * a) / x)) * w 88 + (1) * w 119=0 at hs
  have hs0 := hs
  change (1) * w 119=0
  change (1) * w 26 + (1) * w 126=0 at h88
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change (((1 + ((-1) * (y^2)) + ((-1) * a * x)) / (x^2))) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 44 + (((-1) / (x^2))) * w 108=0 at h102
  change ((((-1) * a) / x)) * w 24 + ((1 / (x^2))) * w 42 + (1) * w 88=0 at h104
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h88 h90 h102 h104 h118 h119 h120 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h88-(((-1) * (y^2)))*h90-((((-1) * (x^2)) / (y^2)))*h102-((((-1) * a) / x))*h104-(((((-1) * (x^2)) + ((-1) * (y^2)) + (a * (x^3)) + ((a^2) * (y^2)) + ((x^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-(((-1) / (y^2)))*h119
#print axioms reduced_step132




compact_certificate theorem reduced_step133 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 133=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h126 : reducedRows x y z a b w 126=0)
    (h129 : reducedRows x y z a b w 129=0)
    (h132 : reducedRows x y z a b w 132=0)
    : reducedRows x y z a b w 133=0 := by
  change (1) * w 29 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 30 + (1) * w 59 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 60 + (1) * w 89 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 90 + (1) * w 119 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 120=0 at hs
  have hs0 := hs
  change (1) * w 59=0
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (1) * w 89=0 at h126
  change (1) * w 29=0 at h129
  change (1) * w 119=0 at h132
  linear_combination (norm := (field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (z^2)))*h50-((1 / ((x^2) * (z^2))))*h53-(1)*h126-(1)*h129-(1)*h132
#print axioms reduced_step133




compact_certificate theorem reduced_step134 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 134=0)
    (h80 : reducedRows x y z a b w 80=0)
    (h82 : reducedRows x y z a b w 82=0)
    (h85 : reducedRows x y z a b w 85=0)
    (h86 : reducedRows x y z a b w 86=0)
    (h114 : reducedRows x y z a b w 114=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 134=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 52 + ((1 / (x^2))) * w 58 + ((((-1) * a) / x)) * w 104 + (1) * w 127=0 at hs
  have hs0 := hs
  change (1) * w 127=0
  change (1) * w 52 + (1) * w 102=0 at h80
  change ((y^2)) * w 14 + (1) * w 104=0 at h82
  change ((y^2)) * w 14 + (1) * w 24=0 at h85
  change (1) * w 42 + (1) * w 102=0 at h86
  change ((((-1) + ((-1) * b * y)) / (y^2))) * w 24 + (1) * w 58 + (1) * w 108=0 at h114
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h80 h82 h85 h86 h114 h118 h119 h120 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(1)*h80-((((-1) * a) / x))*h82-((a / x))*h85-((-1))*h86-((1 / (x^2)))*h114-((((-1) + ((-1) * b * y) + (a * x * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-(((-1) / (x^2)))*h119
#print axioms reduced_step134




compact_certificate theorem reduced_step135 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 135=0)
    (h99 : reducedRows x y z a b w 99=0)
    (h101 : reducedRows x y z a b w 101=0)
    (h110 : reducedRows x y z a b w 110=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 135=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 53 + ((1 / (x^2))) * w 62 + ((((-1) * a) / x)) * w 106 + (1) * w 128=0 at hs
  have hs0 := hs
  change (1) * w 53=0
  change (1) * w 16 + (((1 + ((-1) * (y^2))) / (y^2))) * w 24 + (1) * w 106=0 at h99
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at h101
  change ((a / x)) * w 24 + (1) * w 62 + ((1 / (x^2))) * w 108=0 at h110
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h99 h101 h110 h118 h119 h120 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((-1) * a) / x))*h99-((a * x))*h101-((1 / (x^2)))*h110-((((a * (y^2)) + ((a^2) * (x^3)) + ((-1) * a * (x^2)) + (a * (x^2) * (y^2))) / (x * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))))*h118-(((-1) / (x^4)))*h119
#print axioms reduced_step135




compact_certificate theorem reduced_step136 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 136=0)
    (h107 : reducedRows x y z a b w 107=0)
    (h114 : reducedRows x y z a b w 114=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h125 : reducedRows x y z a b w 125=0)
    : reducedRows x y z a b w 136=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 58 + ((1 / (x^2))) * w 82 + ((((-1) * a) / x)) * w 116 + (1) * w 133=0 at hs
  have hs0 := hs
  change (1) * w 133=0
  change (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108=0 at h107
  change ((((-1) + ((-1) * b * y)) / (y^2))) * w 24 + (1) * w 58 + (1) * w 108=0 at h114
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 116=0 at h125
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h107 h114 h118 h119 h120 h124 h125 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h107-(1)*h114-(((((-2) * (x^2)) + ((-1) * b * y * (x^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-(((a + ((-1) * x * (y^2))) / (x * (y^2))))*h119-((((-1) * a) / x))*h125
#print axioms reduced_step136




compact_certificate theorem reduced_step137 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 137=0)
    (h40 : reducedRows x y z a b w 40=0)
    (h84 : reducedRows x y z a b w 84=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h112 : reducedRows x y z a b w 112=0)
    (h115 : reducedRows x y z a b w 115=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 137=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 61 + ((1 / (x^2))) * w 94 + ((((-1) * a) / x)) * w 122 + (1) * w 136=0 at hs
  have hs0 := hs
  change ((1 / (x^2))) * w 94=0
  change (1) * w 96 + (((-1) * (y^2))) * w 136=0 at h40
  change (1) * w 96 + (1) * w 126=0 at h84
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change (((((-1) * a) + ((-1) * (x^3))) / (x * (y^2)))) * w 24 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 42 + ((1 / (x^2))) * w 122=0 at h112
  change ((((-1) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 24 + (1) * w 61 + (((1 + ((-1) * a * x) + (b * y * (x^2))) / ((x^2) * (y^2)))) * w 108=0 at h115
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h40 h84 h90 h112 h115 h118 h119 h120 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h40-((1 / (y^2)))*h84-(((-1) * (x^2)))*h90-(((-1) * a * x))*h112-(1)*h115-((((-1) + ((-2) * (x^2)) + (a * (x^5)) + ((a^2) * (x^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((((-1) + (a * x) + ((-1) * b * y * (x^2))) / ((x^2) * (y^2))))*h119
#print axioms reduced_step137




compact_certificate theorem reduced_step138 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 138=0)
    (h22 : reducedRows x y z a b w 22=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h39 : reducedRows x y z a b w 39=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h54 : reducedRows x y z a b w 54=0)
    (h68 : reducedRows x y z a b w 68=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h72 : reducedRows x y z a b w 72=0)
    (h89 : reducedRows x y z a b w 89=0)
    (h111 : reducedRows x y z a b w 111=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h137 : reducedRows x y z a b w 137=0)
    : reducedRows x y z a b w 138=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (((x^2) / ((y^2) * (z^2)))) * w 15 + (1) * w 34 + (((x^2) / ((y^2) * (z^2)))) * w 45 + (1) * w 64 + (1) * w 94 + (((x^2) / ((y^2) * (z^2)))) * w 105 + (1) * w 124 + (((x^2) / ((y^2) * (z^2)))) * w 135=0 at hs
  have hs0 := hs
  change (1) * w 34=0
  change ((((-1) * (y^2)) / (x^2))) * w 10 + (1) * w 135=0 at h22
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change (((-1) * (y^2))) * w 10 + (1) * w 90=0 at h39
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (1) * w 20 + (((x^2) / (y^2))) * w 105=0 at h54
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change (((((-2) * (z^2)) + ((-1) * (x^4) * (z^2)) + (3 * (x^2) * (z^2)) + ((-1) * (a^2) * (x^2) * (z^2))) / ((y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18 + ((((-1) * (x^2)) / (y^2))) * w 45=0 at h72
  change (1) * w 24 + (1) * w 124=0 at h89
  change ((((-1) + (y^2) + (a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 64 + ((((-1) * a) / x)) * w 128=0 at h111
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change ((1 / (x^2))) * w 94=0 at h137
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h22 h31 h39 h53 h54 h68 h71 h72 h89 h111 h118 h120 h124 h137 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((x^2) / ((y^2) * (z^2))))*h22-(((-1) / ((y^2) * (z^2))))*h31-(((-1) / ((y^2) * (z^2))))*h39-((1 / (z^2)))*h53-((1 / (z^2)))*h54-((((-1) * (x^2)) / (z^2)))*h68-((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((z^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-(((-1) / (z^2)))*h72-(1)*h89-(1)*h111-((((-1) + (y^2) + (a * x) + ((x^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((x^2))*h137
#print axioms reduced_step138




compact_certificate theorem reduced_step139 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 139=0)
    (h21 : reducedRows x y z a b w 21=0)
    (h23 : reducedRows x y z a b w 23=0)
    (h29 : reducedRows x y z a b w 29=0)
    (h30 : reducedRows x y z a b w 30=0)
    (h31 : reducedRows x y z a b w 31=0)
    (h33 : reducedRows x y z a b w 33=0)
    (h34 : reducedRows x y z a b w 34=0)
    (h36 : reducedRows x y z a b w 36=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h64 : reducedRows x y z a b w 64=0)
    (h66 : reducedRows x y z a b w 66=0)
    (h67 : reducedRows x y z a b w 67=0)
    (h68 : reducedRows x y z a b w 68=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h86 : reducedRows x y z a b w 86=0)
    (h105 : reducedRows x y z a b w 105=0)
    (h107 : reducedRows x y z a b w 107=0)
    (h117 : reducedRows x y z a b w 117=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h137 : reducedRows x y z a b w 137=0)
    : reducedRows x y z a b w 139=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 9 + (1) * w 19 + ((1 / ((x^2) * (z^2)))) * w 20 + ((1 / ((x^2) * (z^2)))) * w 30 + (1) * w 39 + ((1 / ((x^2) * (z^2)))) * w 60 + (1) * w 69 + (1) * w 79 + ((1 / ((x^2) * (z^2)))) * w 80 + ((1 / ((x^2) * (z^2)))) * w 90 + (1) * w 109 + ((1 / ((x^2) * (z^2)))) * w 110 + ((1 / ((x^2) * (z^2)))) * w 120 + (1) * w 129 + (1) * w 139 + ((1 / ((x^2) * (z^2)))) * w 140=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change (1) * w 109=0
  change (((-1) * (x^2))) * w 9 + (1) * w 132=0 at h21
  change ((((-1) * (x^2)) / (y^2))) * w 15 + (1) * w 140=0 at h23
  change (1) * w 80 + (((-1) / (y^2))) * w 120=0 at h29
  change (1) * w 42 + (((-1) * (x^2) * (y^2))) * w 139=0 at h30
  change (((-1) * (x^2))) * w 15 + (1) * w 60=0 at h31
  change (((-1) / (x^2))) * w 24 + (1) * w 69=0 at h33
  change (1) * w 79 + (((-1) / ((x^2) * (y^2)))) * w 102=0 at h34
  change (1) * w 82 + ((((-1) * (x^2)) / (y^2))) * w 129=0 at h36
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change (((-1) + ((-1) * (x^2)) + ((-1) * a * x))) * w 18 + (1) * w 39=0 at h64
  change ((((-1) * a) / x)) * w 30 + ((((-2) + (x^2)) / (x^2))) * w 90=0 at h66
  change ((((2 * a * x) + (2 * b * y) + ((-1) * a * x * (y^2)) + ((-1) * b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 110=0 at h67
  change ((1 / (x^2))) * w 20 + ((((-2) + ((-1) * (x^4)) + (3 * (x^2)) + ((-1) * (a^2) * (x^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30=0 at h68
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 42 + (1) * w 102=0 at h86
  change (1) * w 19 + ((((-1) * a) / x)) * w 38 + (1) * w 94=0 at h105
  change (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108=0 at h107
  change ((((-1) * a) / x)) * w 24 + ((-1)) * w 38 + ((((y^2) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 42=0 at h117
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change ((1 / (x^2))) * w 94=0 at h137
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h21 h23 h29 h30 h31 h33 h34 h36 h50 h53 h58 h64 h66 h67 h68 h71 h73 h86 h105 h107 h117 h118 h119 h120 h124 h137 ⊢
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h21 h23 h29 h30 h31 h33 h34 h36 h50 h53 h58 h64 h66 h67 h68 h71 h73 h86 h105 h107 h117 h118 h119 h120 h124 h137 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (x^2)))*h21-((1 / ((x^2) * (z^2))))*h23-((1 / ((x^2) * (z^2))))*h29-(((-1) / ((x^2) * (y^2))))*h30-(((-1) / ((x^2) * (y^2) * (z^2))))*h31-(1)*h33-(1)*h34-((((-1) * (y^2)) / (x^2)))*h36-(((1 + (y^2)) / (z^2)))*h50-(((1 + (y^2)) / ((x^2) * (z^2))))*h53-((((-1) * (y^2)) / ((x^2) * (z^2))))*h58-(1)*h64-(((-1) / ((y^2) * (z^2) * ((-2) + (x^2)))))*h66-((1 / ((x^2) * (z^2))))*h67-((1 / (z^2)))*h68-((1 / ((x^2) * (z^2))))*h71-((1 / ((x^2) * (y^2))))*h86-(1)*h105-((-1))*h107-((((-1) * a) / x))*h117-(((((-1) * (y^2)) + ((a^2) * (y^2)) + ((-1) * (x^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((a / x))*h119-(((-1) * (x^2)))*h137
#print axioms reduced_step139



compact_certificate theorem reduced_step140 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 140=0)
    (h3 : reducedRows x y z a b w 3=0)
    (h7 : reducedRows x y z a b w 7=0)
    (h9 : reducedRows x y z a b w 9=0)
    (h11 : reducedRows x y z a b w 11=0)
    (h13 : reducedRows x y z a b w 13=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h18 : reducedRows x y z a b w 18=0)
    (h19 : reducedRows x y z a b w 19=0)
    (h30 : reducedRows x y z a b w 30=0)
    (h32 : reducedRows x y z a b w 32=0)
    (h34 : reducedRows x y z a b w 34=0)
    (h42 : reducedRows x y z a b w 42=0)
    (h48 : reducedRows x y z a b w 48=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h56 : reducedRows x y z a b w 56=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h60 : reducedRows x y z a b w 60=0)
    (h61 : reducedRows x y z a b w 61=0)
    (h70 : reducedRows x y z a b w 70=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h74 : reducedRows x y z a b w 74=0)
    (h75 : reducedRows x y z a b w 75=0)
    (h79 : reducedRows x y z a b w 79=0)
    (h84 : reducedRows x y z a b w 84=0)
    (h86 : reducedRows x y z a b w 86=0)
    (h87 : reducedRows x y z a b w 87=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h92 : reducedRows x y z a b w 92=0)
    (h97 : reducedRows x y z a b w 97=0)
    (h105 : reducedRows x y z a b w 105=0)
    (h107 : reducedRows x y z a b w 107=0)
    (h116 : reducedRows x y z a b w 116=0)
    (h117 : reducedRows x y z a b w 117=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h127 : reducedRows x y z a b w 127=0)
    (h128 : reducedRows x y z a b w 128=0)
    (h131 : reducedRows x y z a b w 131=0)
    (h134 : reducedRows x y z a b w 134=0)
    (h136 : reducedRows x y z a b w 136=0)
    (h137 : reducedRows x y z a b w 137=0)
    (h139 : reducedRows x y z a b w 139=0)
    : reducedRows x y z a b w 140=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change ((1 / ((x^2) * (y^2)))) * w 0 + ((1 / ((x^2) * (y^2)))) * w 6 + (1) * w 7 + ((1 / ((x^2) * (y^2)))) * w 12 + (1) * w 13 + ((1 / ((x^2) * (y^2)))) * w 18 + (1) * w 19 + (1) * w 25 + ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 36 + (1) * w 37 + ((1 / ((x^2) * (y^2)))) * w 42 + (1) * w 43 + ((1 / ((x^2) * (y^2)))) * w 48 + (1) * w 49 + (1) * w 55 + ((1 / ((x^2) * (y^2)))) * w 60 + ((1 / ((x^2) * (y^2)))) * w 66 + (1) * w 67 + ((1 / ((x^2) * (y^2)))) * w 72 + (1) * w 73 + ((1 / ((x^2) * (y^2)))) * w 78 + (1) * w 79 + (1) * w 85 + ((1 / ((x^2) * (y^2)))) * w 90 + ((1 / ((x^2) * (y^2)))) * w 96 + (1) * w 97 + ((1 / ((x^2) * (y^2)))) * w 102 + (1) * w 103 + ((1 / ((x^2) * (y^2)))) * w 108 + (1) * w 109 + (1) * w 115 + ((1 / ((x^2) * (y^2)))) * w 120 + ((1 / ((x^2) * (y^2)))) * w 126 + (1) * w 127 + ((1 / ((x^2) * (y^2)))) * w 132 + (1) * w 133 + ((1 / ((x^2) * (y^2)))) * w 138 + (1) * w 139 + (1) * w 145=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change (1) * w 67=0
  change ((-1)) * w 6=0 at h3
  change (1) * w 72=0 at h7
  change (1) * w 78=0 at h9
  change (1) * w 138=0 at h11
  change ((-1)) * w 12=0 at h13
  change (1) * w 0=0 at h15
  change (1) * w 120 + (((-1) * (x^2) * (y^2))) * w 145=0 at h18
  change (((-1) * (x^2) * (y^2))) * w 7 + (1) * w 108=0 at h19
  change (1) * w 42 + (((-1) * (x^2) * (y^2))) * w 139=0 at h30
  change ((-1)) * w 18 + (1) * w 66=0 at h32
  change (1) * w 79 + (((-1) / ((x^2) * (y^2)))) * w 102=0 at h34
  change (((-1) * (x^2) * (y^2))) * w 13 + (1) * w 36=0 at h42
  change (1) * w 73 + (((-1) / ((x^2) * (y^2)))) * w 126=0 at h48
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (1) * w 25 + (((z^2) / ((x^2) * (y^2)))) * w 114=0 at h56
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  change (((2 + ((-1) * (x^2)) + ((-4) * (y^2)) + ((-1) * (x^4) * (y^2)) + (4 * (x^2) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2))) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 55=0 at h70
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 85=0 at h74
  change (1) * w 115=0 at h75
  change (1) * w 49 + (1) * w 99=0 at h79
  change (1) * w 96 + (1) * w 126=0 at h84
  change (1) * w 42 + (1) * w 102=0 at h86
  change (1) * w 48 + (1) * w 108=0 at h87
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change (1) * w 37 + (1) * w 112=0 at h92
  change ((1 / (x^2))) * w 24 + (((y^2) / (x^2))) * w 82 + (1) * w 99=0 at h97
  change (1) * w 19 + ((((-1) * a) / x)) * w 38 + (1) * w 94=0 at h105
  change (1) * w 24 + ((((-1) * (y^2)) / (x^2))) * w 82 + ((a / x)) * w 108=0 at h107
  change ((((-1) * a) / x)) * w 24 + ((((x^2) + ((-1) * (y^2))) / ((x^2) * (y^2)))) * w 108 + (1) * w 112=0 at h116
  change ((((-1) * a) / x)) * w 24 + ((-1)) * w 38 + ((((y^2) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 42=0 at h117
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 97=0 at h127
  change (1) * w 103=0 at h128
  change (1) * w 43=0 at h131
  change (1) * w 127=0 at h134
  change (1) * w 133=0 at h136
  change ((1 / (x^2))) * w 94=0 at h137
  change (1) * w 109=0 at h139
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h3 h7 h9 h11 h13 h15 h18 h19 h30 h32 h34 h42 h48 h50 h53 h56 h58 h60 h61 h70 h71 h73 h74 h75 h79 h84 h86 h87 h90 h92 h97 h105 h107 h116 h117 h118 h119 h120 h124 h127 h128 h131 h134 h136 h137 h139 ⊢
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h3 h7 h9 h11 h13 h15 h18 h19 h30 h32 h34 h42 h48 h50 h53 h56 h58 h60 h61 h70 h71 h73 h74 h75 h79 h84 h86 h87 h90 h92 h97 h105 h107 h116 h117 h118 h119 h120 h124 h127 h128 h131 h134 h136 h137 h139 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h3-((1 / ((x^2) * (y^2))))*h7-((1 / ((x^2) * (y^2))))*h9-((1 / ((x^2) * (y^2))))*h11-(((-1) / ((x^2) * (y^2))))*h13-((1 / ((x^2) * (y^2))))*h15-(((-1) / ((x^2) * (y^2))))*h18-(((-1) / ((x^2) * (y^2))))*h19-(((-1) / ((x^2) * (y^2))))*h30-((1 / ((x^2) * (y^2))))*h32-(1)*h34-(((-1) / ((x^2) * (y^2))))*h42-(1)*h48-(2)*h50-((1 / (x^2)))*h53-(1)*h56-(((-1) / ((x^2) * (z^2))))*h58-((2 / (y^2)))*h60-(1)*h61-(1)*h70-((((4 * (y^2)) + ((x^4) * (y^2)) + ((-4) * (x^2) * (y^2)) + ((a^2) * (x^2) * (y^2))) / ((x^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-(1)*h74-(1)*h75-(1)*h79-((1 / ((x^2) * (y^2))))*h84-((2 / ((x^2) * (y^2))))*h86-((1 / ((x^2) * (y^2))))*h87-(1)*h90-(1)*h92-((-1))*h97-(1)*h105-((-1))*h107-((-1))*h116-((((-1) * a) / x))*h117-(((1 + ((-1) * (y^2)) + ((a^2) * (y^2)) + ((-1) * (x^2) * (y^2)) + (a * x * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-(((1 + (x^2) + ((-1) * (y^2)) + (a * x * (y^2))) / ((x^2) * (y^2))))*h119-(1)*h127-(1)*h128-(1)*h131-(1)*h134-(1)*h136-(((-1) * (x^2)))*h137-(1)*h139
#print axioms reduced_step140




compact_certificate theorem reduced_step141 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 141=0)
    (h112 : reducedRows x y z a b w 112=0)
    (h117 : reducedRows x y z a b w 117=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h137 : reducedRows x y z a b w 137=0)
    : reducedRows x y z a b w 141=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change ((1 / (x^2))) * w 38 + (1) * w 47 + ((((-1) * a) / x)) * w 94 + (1) * w 122=0 at hs
  have hs0 := hs
  change (1) * w 47=0
  change (((((-1) * a) + ((-1) * (x^3))) / (x * (y^2)))) * w 24 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 42 + ((1 / (x^2))) * w 122=0 at h112
  change ((((-1) * a) / x)) * w 24 + ((-1)) * w 38 + ((((y^2) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 42=0 at h117
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change ((1 / (x^2))) * w 94=0 at h137
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h112 h117 h118 h120 h124 h137 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((x^2))*h112-(((-1) / (x^2)))*h117-(((((-1) * (x^7)) + (a * (y^2)) + ((-1) * a * (x^4))) / (x * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))))*h118-(((-1) * a * x))*h137
#print axioms reduced_step141




compact_certificate theorem reduced_step142 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 142=0)
    (h19 : reducedRows x y z a b w 19=0)
    (h44 : reducedRows x y z a b w 44=0)
    (h65 : reducedRows x y z a b w 65=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h101 : reducedRows x y z a b w 101=0)
    (h106 : reducedRows x y z a b w 106=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    : reducedRows x y z a b w 142=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 7 + ((((-1) * b) / y)) * w 21 + (1) * w 57 + ((1 / (y^2))) * w 63 + (1) * w 107=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change (1) * w 107=0
  change (((-1) * (x^2) * (y^2))) * w 7 + (1) * w 108=0 at h19
  change ((((-1) * (y^2)) / (x^2))) * w 16 + (1) * w 63=0 at h44
  change (((a + ((-1) * x) + (a * (x^2)) + (x * (a^2))) / x)) * w 18 + (1) * w 57=0 at h65
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at h101
  change (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42=0 at h106
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h19 h44 h65 h73 h101 h106 h118 h119 h120 h124 ⊢
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h19 h44 h65 h73 h101 h106 h118 h119 h120 h124 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / ((x^2) * (y^2))))*h19-((1 / (y^2)))*h44-(1)*h65-(1)*h101-((((-1) * b) / y))*h106-((((a * x) + ((-1) * b * y * (x^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((1 / ((x^2) * (y^2))))*h119
#print axioms reduced_step142




compact_certificate theorem reduced_step143 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 143=0)
    (h111 : reducedRows x y z a b w 111=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h142 : reducedRows x y z a b w 142=0)
    : reducedRows x y z a b w 143=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 32 + ((((-1) * a) / x)) * w 64 + (1) * w 107 + ((1 / (x^2))) * w 128=0 at hs
  have hs0 := hs
  change (1) * w 32=0
  change ((((-1) + (y^2) + (a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 64 + ((((-1) * a) / x)) * w 128=0 at h111
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 107=0 at h142
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h111 h118 h120 h124 h142 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((((-1) * a) / x))*h111-(((a + ((-1) * a * (y^2)) + ((-1) * x * (a^2))) / (x * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))))*h118-(1)*h142
#print axioms reduced_step143




compact_certificate theorem reduced_step144 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 144=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h110 : reducedRows x y z a b w 110=0)
    (h112 : reducedRows x y z a b w 112=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h143 : reducedRows x y z a b w 143=0)
    : reducedRows x y z a b w 144=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change ((1 / ((y^2) * (z^2)))) * w 30 + (1) * w 32 + ((1 / ((y^2) * (z^2)))) * w 60 + (1) * w 62 + ((1 / ((y^2) * (z^2)))) * w 90 + (1) * w 92 + ((1 / ((y^2) * (z^2)))) * w 120 + (1) * w 122=0 at hs
  have hs0 := hs
  change (1) * w 92=0
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((a / x)) * w 24 + (1) * w 62 + ((1 / (x^2))) * w 108=0 at h110
  change (((((-1) * a) + ((-1) * (x^3))) / (x * (y^2)))) * w 24 + (((1 + (a * (x^3))) / ((x^2) * (y^2)))) * w 42 + ((1 / (x^2))) * w 122=0 at h112
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 32=0 at h143
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h50 h53 h110 h112 h118 h119 h120 h124 h143 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((x^2) / (z^2)))*h50-((1 / (z^2)))*h53-(1)*h110-((x^2))*h112-(((((-1) * (x^6)) + ((-1) * a * (x^3)) + (a * x * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-(((-1) / (x^2)))*h119-(1)*h143
#print axioms reduced_step144




compact_certificate theorem reduced_step145 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 145=0)
    (h20 : reducedRows x y z a b w 20=0)
    (h90 : reducedRows x y z a b w 90=0)
    (h101 : reducedRows x y z a b w 101=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h143 : reducedRows x y z a b w 143=0)
    : reducedRows x y z a b w 145=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 8 + ((((-1) * a) / x)) * w 16 + ((1 / (x^2))) * w 32 + (1) * w 83=0 at hs
  have hs0 := hs
  change (1) * w 83=0
  change (((-1) * (y^2))) * w 8 + (1) * w 126=0 at h20
  change ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 126=0 at h90
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at h101
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 32=0 at h143
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h20 h90 h101 h118 h120 h124 h143 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-(((-1) / (y^2)))*h20-((x^2))*h90-(((-1) * a * x))*h101-((((x^2) + ((-1) * (a^2) * (x^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((1 / (x^2)))*h143
#print axioms reduced_step145




compact_certificate theorem reduced_step146 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 146=0)
    (h101 : reducedRows x y z a b w 101=0)
    (h111 : reducedRows x y z a b w 111=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h143 : reducedRows x y z a b w 143=0)
    : reducedRows x y z a b w 146=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 16 + ((((-1) * a) / x)) * w 32 + ((1 / (x^2))) * w 64 + (1) * w 91=0 at hs
  have hs0 := hs
  change (1) * w 91=0
  change ((1 / (x^2))) * w 16 + ((a / (x * (y^2)))) * w 24 + (((-1) / ((x^2) * (y^2)))) * w 42=0 at h101
  change ((((-1) + (y^2) + (a * x)) / ((x^2) * (y^2)))) * w 24 + (1) * w 64 + ((((-1) * a) / x)) * w 128=0 at h111
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 32=0 at h143
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h101 h111 h118 h120 h124 h143 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((x^2))*h101-((1 / (x^2)))*h111-((((-1) + (y^2) + (a * x) + (a * (x^5))) / ((x^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x)))))*h118-((((-1) * a) / x))*h143
#print axioms reduced_step146




compact_certificate theorem reduced_step147 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 147=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h115 : reducedRows x y z a b w 115=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h130 : reducedRows x y z a b w 130=0)
    (h146 : reducedRows x y z a b w 146=0)
    : reducedRows x y z a b w 147=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change ((1 / ((x^2) * (y^2) * (z^2)))) * w 30 + (1) * w 31 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 60 + (1) * w 61 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 90 + (1) * w 91 + ((1 / ((x^2) * (y^2) * (z^2)))) * w 120 + (1) * w 121=0 at hs
  have hs0 := hs
  change (1) * w 121=0
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change ((((-1) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 24 + (1) * w 61 + (((1 + ((-1) * a * x) + (b * y * (x^2))) / ((x^2) * (y^2)))) * w 108=0 at h115
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 31=0 at h130
  change (1) * w 91=0 at h146
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h50 h53 h115 h118 h119 h120 h124 h130 h146 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (z^2)))*h50-((1 / ((x^2) * (z^2))))*h53-(1)*h115-((((-1) + ((-1) * (x^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((((-1) + (a * x) + ((-1) * b * y * (x^2))) / ((x^2) * (y^2))))*h119-(1)*h130-(1)*h146
#print axioms reduced_step147




compact_certificate theorem reduced_step148 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 148=0)
    (h45 : reducedRows x y z a b w 45=0)
    (h106 : reducedRows x y z a b w 106=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h138 : reducedRows x y z a b w 138=0)
    (h144 : reducedRows x y z a b w 144=0)
    : reducedRows x y z a b w 148=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change (1) * w 17 + ((((-1) * a) / x)) * w 34 + ((1 / (x^2))) * w 68 + (1) * w 92=0 at hs
  have hs0 := hs
  change (1) * w 17=0
  change ((((-1) * (x^2)) / (y^2))) * w 21 + (1) * w 68=0 at h45
  change (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42=0 at h106
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 34=0 at h138
  change (1) * w 92=0 at h144
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h45 h106 h118 h120 h124 h138 h144 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / (x^2)))*h45-((1 / (y^2)))*h106-(((x^2) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((((-1) * a) / x))*h138-(1)*h144
#print axioms reduced_step148




compact_certificate theorem reduced_step149 (x y z a b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (hP0 : ((y^2) + ((-1) * (x^2)) + ((-1) * (y^4)) + (2 * (x^4)) + (a * (x^7)) + ((a^3) * (x^5)) + ((x^2) * (y^4)) + ((-3) * a * (x^5)) + ((-2) * (a^2) * (x^4)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (2 * (x^4) * (y^2)) + (b * y * (x^8)) + ((a^2) * (x^2) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^7) * (y^2)) + ((-1) * b * y * (x^4)) + ((-1) * b * y * (x^6)) + ((-1) * (a^2) * (x^4) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^2)) + (2 * a * (x^5) * (y^2)) + (a * b * y * (x^5)) + ((-1) * a * b * (x^3) * (y^3)))≠0)
    (hP1 : ((-2) + (x^4) + ((-1) * (x^2)) + (2 * (y^2)) + ((a^2) * (x^2)) + ((-1) * (x^2) * (y^2)) + (a * b * x * y))≠0)
    (hP2 : (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))≠0)
    (hP3 : (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))≠0)
    (hP4 : ((-1) + (y^2) + (2 * (x^2)) + (a * x))≠0)
    (hP5 : ((x^2) + (y^2) + (a * (x^3)) + (a * (x^5)) + ((x^2) * (y^2)))≠0)
    (hP6 : ((-2) + (x^2))≠0)
    (w : Fin 150→ℂ)
    (hs : sourceRows x y z a b w 149=0)
    (h0 : reducedRows x y z a b w 0=0)
    (h7 : reducedRows x y z a b w 7=0)
    (h9 : reducedRows x y z a b w 9=0)
    (h11 : reducedRows x y z a b w 11=0)
    (h13 : reducedRows x y z a b w 13=0)
    (h15 : reducedRows x y z a b w 15=0)
    (h26 : reducedRows x y z a b w 26=0)
    (h27 : reducedRows x y z a b w 27=0)
    (h28 : reducedRows x y z a b w 28=0)
    (h37 : reducedRows x y z a b w 37=0)
    (h41 : reducedRows x y z a b w 41=0)
    (h43 : reducedRows x y z a b w 43=0)
    (h47 : reducedRows x y z a b w 47=0)
    (h49 : reducedRows x y z a b w 49=0)
    (h50 : reducedRows x y z a b w 50=0)
    (h53 : reducedRows x y z a b w 53=0)
    (h57 : reducedRows x y z a b w 57=0)
    (h58 : reducedRows x y z a b w 58=0)
    (h60 : reducedRows x y z a b w 60=0)
    (h61 : reducedRows x y z a b w 61=0)
    (h69 : reducedRows x y z a b w 69=0)
    (h71 : reducedRows x y z a b w 71=0)
    (h73 : reducedRows x y z a b w 73=0)
    (h76 : reducedRows x y z a b w 76=0)
    (h77 : reducedRows x y z a b w 77=0)
    (h85 : reducedRows x y z a b w 85=0)
    (h86 : reducedRows x y z a b w 86=0)
    (h87 : reducedRows x y z a b w 87=0)
    (h93 : reducedRows x y z a b w 93=0)
    (h98 : reducedRows x y z a b w 98=0)
    (h106 : reducedRows x y z a b w 106=0)
    (h109 : reducedRows x y z a b w 109=0)
    (h113 : reducedRows x y z a b w 113=0)
    (h116 : reducedRows x y z a b w 116=0)
    (h117 : reducedRows x y z a b w 117=0)
    (h118 : reducedRows x y z a b w 118=0)
    (h119 : reducedRows x y z a b w 119=0)
    (h120 : reducedRows x y z a b w 120=0)
    (h122 : reducedRows x y z a b w 122=0)
    (h124 : reducedRows x y z a b w 124=0)
    (h135 : reducedRows x y z a b w 135=0)
    (h141 : reducedRows x y z a b w 141=0)
    (h142 : reducedRows x y z a b w 142=0)
    (h145 : reducedRows x y z a b w 145=0)
    (h148 : reducedRows x y z a b w 148=0)
    : reducedRows x y z a b w 149=0 := by
  obtain ⟨hw42,hw128⟩ := last_pivots_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h120 h124
  change ((1 / ((x^2) * (y^2)))) * w 0 + (1) * w 5 + (1) * w 11 + ((1 / ((x^2) * (y^2)))) * w 12 + (1) * w 17 + ((1 / ((x^2) * (y^2)))) * w 18 + (1) * w 23 + ((1 / ((x^2) * (y^2)))) * w 24 + ((1 / ((x^2) * (y^2)))) * w 30 + (1) * w 35 + (1) * w 41 + ((1 / ((x^2) * (y^2)))) * w 42 + (1) * w 47 + ((1 / ((x^2) * (y^2)))) * w 48 + (1) * w 53 + ((1 / ((x^2) * (y^2)))) * w 54 + ((1 / ((x^2) * (y^2)))) * w 60 + (1) * w 65 + (1) * w 71 + ((1 / ((x^2) * (y^2)))) * w 72 + (1) * w 77 + ((1 / ((x^2) * (y^2)))) * w 78 + (1) * w 83 + ((1 / ((x^2) * (y^2)))) * w 84 + ((1 / ((x^2) * (y^2)))) * w 90 + (1) * w 95 + (1) * w 101 + ((1 / ((x^2) * (y^2)))) * w 102 + (1) * w 107 + ((1 / ((x^2) * (y^2)))) * w 108 + (1) * w 113 + ((1 / ((x^2) * (y^2)))) * w 114 + ((1 / ((x^2) * (y^2)))) * w 120 + (1) * w 125 + (1) * w 131 + ((1 / ((x^2) * (y^2)))) * w 132 + (1) * w 137 + ((1 / ((x^2) * (y^2)))) * w 138 + (1) * w 143 + ((1 / ((x^2) * (y^2)))) * w 144=0 at hs
  have hs0 := hs
  have hw18 := pivot73_zero x y z a b hx hy hz hP0 hP1 hP2 hP3 hP4 hP5 hP6 w h73
  change (1) * w 23=0
  change (1) * w 144=0 at h0
  change (1) * w 72=0 at h7
  change (1) * w 78=0 at h9
  change (1) * w 138=0 at h11
  change ((-1)) * w 12=0 at h13
  change (1) * w 0=0 at h15
  change (((-1) / ((x^2) * (y^2)))) * w 42 + (1) * w 143=0 at h26
  change (1) * w 5 + (((-1) / ((x^2) * (y^2)))) * w 30=0 at h27
  change (((-1) / ((x^2) * (y^2)))) * w 24 + (1) * w 77=0 at h28
  change (1) * w 84 + ((-1)) * w 132=0 at h37
  change (1) * w 114 + (((-1) * (x^2) * (y^2))) * w 137=0 at h41
  change (((-1) * (y^2))) * w 14 + (1) * w 54=0 at h43
  change (((-1) / ((x^2) * (y^2)))) * w 48 + (1) * w 71=0 at h47
  change (((-1) * (x^2) * (y^2))) * w 11 + (1) * w 108=0 at h49
  change ((1 / ((x^2) * (y^2)))) * w 30 + ((1 / ((x^2) * (y^2)))) * w 120=0 at h50
  change ((1 / (y^2))) * w 60 + ((1 / (y^2))) * w 90=0 at h53
  change (((z^2) / ((x^2) * (y^2)))) * w 36 + (1) * w 125=0 at h57
  change ((((-1) * (z^2)) / (y^2))) * w 18 + ((((-1) * (z^2)) / (y^2))) * w 132=0 at h58
  change ((((-1) + ((-1) * (x^2)) + ((-1) * a * x)) / (x^2))) * w 18 + ((1 / (x^2))) * w 36=0 at h60
  change (((((-1) * (z^2)) + ((-1) * (x^2) * (z^2)) + ((-1) * a * x * (z^2))) / ((x^2) * (y^2)))) * w 18 + ((((-1) * (z^2)) / ((x^2) * (y^2)))) * w 114=0 at h61
  change (((2 + (x^2) + (x^6) + ((-3) * (x^4)) + ((a^2) * (x^4)) + ((-2) * (a^2) * (x^2)) + ((a^2) * (x^2) * (y^2)) + (a * b * y * (x^3)) + ((-2) * a * b * x * y)) / ((x^2) * (y^2) * ((-2) + (x^2))))) * w 30 + (1) * w 95=0 at h69
  change (((z^2) / (y^2))) * w 18 + (((4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))) / ((y^2) * ((-2) + (x^2))))) * w 30=0 at h71
  change ((((4 * (z^2)) + ((x^6) * (z^2)) + ((-4) * (y^2) * (z^2)) + ((-3) * (x^4) * (z^2)) + ((a^2) * (x^4) * (z^2)) + ((-1) * (x^4) * (y^2) * (z^2)) + ((-2) * (a^2) * (x^2) * (z^2)) + (4 * (x^2) * (y^2) * (z^2)) + (a * b * y * (x^3) * (z^2)) + ((-2) * a * b * x * y * (z^2))) / ((x^2) * (y^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2)))))) * w 18=0 at h73
  change (1) * w 35=0 at h76
  change (1) * w 65=0 at h77
  change ((y^2)) * w 14 + (1) * w 24=0 at h85
  change (1) * w 42 + (1) * w 102=0 at h86
  change (1) * w 48 + (1) * w 108=0 at h87
  change (1) * w 38 + (1) * w 113=0 at h93
  change (1) * w 21 + (((-1) / (x^2))) * w 24 + ((-1)) * w 101=0 at h98
  change (1) * w 21 + (1) * w 24 + ((((-1) * a) / x)) * w 42=0 at h106
  change (1) * w 56 + ((((-1) * a) / x)) * w 112 + (1) * w 131=0 at h109
  change ((((-2) + (y^2) + (a * x)) / (y^2))) * w 24 + (((-1) / (y^2))) * w 42 + (1) * w 56=0 at h113
  change ((((-1) * a) / x)) * w 24 + ((((x^2) + ((-1) * (y^2))) / ((x^2) * (y^2)))) * w 108 + (1) * w 112=0 at h116
  change ((((-1) * a) / x)) * w 24 + ((-1)) * w 38 + ((((y^2) + ((-1) * (x^2))) / ((x^2) * (y^2)))) * w 42=0 at h117
  change (((1 + ((-1) * (y^2)) + ((-2) * (x^2)) + ((-1) * a * x)) / ((x^2) * (y^2)))) * w 24 + ((((-1) * b) / y)) * w 42 + ((a / x)) * w 128=0 at h118
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((x^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (a * b * (x^3) * (y^3))) / ((x^2) * (y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + (1) * w 108 + ((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x)))) * w 128=0 at h119
  change ((((x^2) + (y^4) + ((-1) * (y^2)) + ((-2) * (x^4)) + ((a^2) * (x^4)) + ((a^3) * (x^7)) + ((-1) * (x^2) * (y^4)) + ((-2) * a * (x^3)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^6)) + ((-2) * (x^4) * (y^2)) + (2 * (a^2) * (x^8)) + (2 * (x^2) * (y^2)) + (3 * a * (x^5)) + (a * x * (y^2)) + (a * (x^3) * (y^4)) + (a * (x^5) * (y^2)) + (b * y * (x^4)) + (b * y * (x^6)) + (b * (x^8) * (y^3)) + ((a^2) * (x^4) * (y^2)) + ((a^2) * (x^6) * (y^2)) + ((-1) * a * (x^3) * (y^2)) + (a * b * y * (x^7)) + (a * b * y * (x^9)) + (a * b * (x^3) * (y^3)) + (a * b * (x^5) * (y^3)) + (b * (a^2) * (x^6) * (y^3))) / ((x^2) * (y^4) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 42 + ((((-1) + (y^4) + (2 * (x^2)) + ((-1) * (a^2) * (x^6)) + ((-1) * (a^2) * (y^2)) + ((-2) * a * (x^3)) + (2 * a * (x^5)) + (2 * (x^2) * (y^2)) + (a * x * (y^2)) + (a * (x^3) * (y^2)) + ((-1) * a * (x^5) * (y^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * (a^3) * (x^3) * (y^2))) / ((y^2) * ((-1) + (y^2) + (2 * (x^2)) + (a * x))))) * w 128=0 at h120
  change (1) * w 41 + (((((-1) * (x^5)) + (2 * (x^7)) + (a * (y^6)) + ((a^2) * (x^9)) + ((a^3) * (x^8)) + ((a^4) * (x^7)) + ((a^4) * (x^11)) + ((x^5) * (y^4)) + ((-1) * a * (y^4)) + ((-1) * (a^2) * (x^11)) + ((-4) * (a^2) * (x^7)) + ((-2) * a * (x^8)) + ((-2) * (a^3) * (x^6)) + ((-2) * (a^3) * (x^10)) + (2 * a * (x^6)) + (2 * a * (x^10)) + (2 * (a^2) * (x^5)) + (2 * (x^7) * (y^2)) + (a * (x^2) * (y^2)) + (a * (x^4) * (y^4)) + (a * (x^6) * (y^2)) + (a * (x^8) * (y^2)) + (x * (a^2) * (y^4)) + ((a^2) * (x^3) * (y^4)) + ((a^2) * (x^7) * (y^2)) + ((a^2) * (x^9) * (y^4)) + ((a^3) * (x^6) * (y^4)) + ((a^3) * (x^10) * (y^2)) + ((a^4) * (x^5) * (y^4)) + ((a^4) * (x^7) * (y^4)) + ((a^5) * (x^8) * (y^2)) + ((-1) * a * (x^4) * (y^6)) + ((-1) * a * (x^10) * (y^2)) + ((-1) * b * (x^5) * (y^3)) + ((-1) * b * (x^5) * (y^5)) + ((-1) * (a^2) * (x^5) * (y^2)) + ((-1) * (a^2) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^2) * (y^4)) + ((-1) * (a^4) * (x^7) * (y^2)) + ((-3) * (a^2) * (x^3) * (y^2)) + ((-3) * (a^2) * (x^5) * (y^4)) + ((-2) * a * (x^4) * (y^2)) + ((-2) * a * (x^6) * (y^4)) + ((-2) * b * y * (x^7)) + ((-2) * b * (x^7) * (y^3)) + ((-2) * (a^2) * (x^9) * (y^2)) + ((-2) * (a^3) * (x^8) * (y^2)) + (3 * (a^3) * (x^4) * (y^2)) + (a * b * (x^4) * (y^3)) + (a * b * (x^6) * (y^3)) + (b * y * (a^2) * (x^7)) + (b * y * (a^2) * (x^11)) + (b * (a^2) * (x^3) * (y^5)) + (b * (a^2) * (x^5) * (y^5)) + (b * (a^3) * (x^8) * (y^3)) + ((-1) * a * b * y * (x^6)) + ((-1) * a * b * y * (x^10)) + ((-1) * a * b * (x^8) * (y^3)) + ((-1) * b * (a^2) * (x^5) * (y^3))) / ((x^5) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h122
  change ((((y^4) + ((-1) * (x^4)) + ((-1) * (y^6)) + (2 * (x^6)) + (a * (x^5)) + ((a^2) * (x^12)) + ((a^4) * (x^8)) + ((a^4) * (x^10)) + ((x^4) * (y^4)) + ((x^4) * (y^6)) + ((-1) * (a^2) * (x^8)) + ((-1) * (a^3) * (x^7)) + ((-1) * (x^4) * (y^2)) + ((-2) * a * (x^7)) + ((-2) * (a^2) * (x^10)) + ((-2) * (a^3) * (x^9)) + ((-2) * (x^2) * (y^4)) + (2 * (x^6) * (y^4)) + (3 * a * (x^9)) + (4 * (x^6) * (y^2)) + (b * y * (x^10)) + (b * (x^10) * (y^3)) + ((a^2) * (x^2) * (y^4)) + ((a^2) * (x^10) * (y^2)) + ((-1) * a * x * (y^4)) + ((-1) * a * (x^9) * (y^4)) + ((-1) * b * y * (x^6)) + ((-1) * b * y * (x^8)) + ((-1) * b * (x^4) * (y^3)) + ((-1) * (a^2) * (x^6) * (y^4)) + ((-1) * (a^2) * (x^12) * (y^2)) + ((-1) * (a^3) * (x^5) * (y^4)) + ((-1) * (a^3) * (x^7) * (y^4)) + ((-1) * (a^3) * (x^9) * (y^2)) + ((-1) * (a^4) * (x^8) * (y^2)) + ((-1) * (a^4) * (x^10) * (y^2)) + ((-4) * (a^2) * (x^6) * (y^2)) + ((-2) * a * (x^3) * (y^4)) + ((-2) * a * (x^5) * (y^2)) + ((-2) * b * (x^6) * (y^3)) + ((-2) * (a^2) * (x^4) * (y^2)) + (2 * a * (x^3) * (y^2)) + (2 * a * (x^5) * (y^4)) + (2 * a * (x^7) * (y^4)) + (2 * a * (x^9) * (y^2)) + (2 * (a^2) * (x^8) * (y^2)) + (2 * (a^3) * (x^5) * (y^2)) + (a * b * y * (x^13)) + (a * b * (x^7) * (y^3)) + (b * y * (a^2) * (x^8)) + (b * y * (a^2) * (x^10)) + ((-1) * a * b * (x^3) * (y^5)) + ((-1) * a * b * (x^5) * (y^5)) + ((-1) * b * (a^2) * (x^6) * (y^3)) + ((-1) * b * (a^2) * (x^8) * (y^3)) + ((-2) * a * b * y * (x^9))) / ((x^4) * (y^2) * (1 + ((-1) * (y^4)) + ((-2) * (x^2)) + ((a^2) * (x^6)) + ((a^2) * (y^2)) + ((-2) * a * (x^5)) + ((-2) * (x^2) * (y^2)) + (2 * a * (x^3)) + (a * (x^5) * (y^2)) + ((a^2) * (x^2) * (y^2)) + ((a^3) * (x^3) * (y^2)) + ((-1) * a * x * (y^2)) + ((-1) * a * (x^3) * (y^2)))))) * w 42=0 at h124
  change (1) * w 53=0 at h135
  change (1) * w 47=0 at h141
  change (1) * w 107=0 at h142
  change (1) * w 83=0 at h145
  change (1) * w 17=0 at h148
  simp only [hw42,hw128,mul_zero,zero_mul,zero_add,add_zero] at hs0 h0 h7 h9 h11 h13 h15 h26 h27 h28 h37 h41 h43 h47 h49 h50 h53 h57 h58 h60 h61 h69 h71 h73 h76 h77 h85 h86 h87 h93 h98 h106 h109 h113 h116 h117 h118 h119 h120 h122 h124 h135 h141 h142 h145 h148 ⊢
  simp only [hw18,mul_zero,zero_add,add_zero] at hs0 h0 h7 h9 h11 h13 h15 h26 h27 h28 h37 h41 h43 h47 h49 h50 h53 h57 h58 h60 h61 h69 h71 h73 h76 h77 h85 h86 h87 h93 h98 h106 h109 h113 h116 h117 h118 h119 h120 h122 h124 h135 h141 h142 h145 h148 ⊢
  linear_combination (norm := (simp only [mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero]; field_simp (disch := first | field_simp_discharge | assumption | (solve | norm_num [hx,hy,hz]) | (solve | convert hP0 using 1 <;> ring) | (solve | convert hP1 using 1 <;> ring) | (solve | convert hP2 using 1 <;> ring) | (solve | convert hP3 using 1 <;> ring) | (solve | convert hP4 using 1 <;> ring) | (solve | convert hP5 using 1 <;> ring) | (solve | convert hP6 using 1 <;> ring)); all_goals ring)) hs0-((1 / ((x^2) * (y^2))))*h0-((1 / ((x^2) * (y^2))))*h7-((1 / ((x^2) * (y^2))))*h9-((1 / ((x^2) * (y^2))))*h11-(((-1) / ((x^2) * (y^2))))*h13-((1 / ((x^2) * (y^2))))*h15-(1)*h26-(1)*h27-(1)*h28-((1 / ((x^2) * (y^2))))*h37-(((-1) / ((x^2) * (y^2))))*h41-((1 / ((x^2) * (y^2))))*h43-(1)*h47-(((-1) / ((x^2) * (y^2))))*h49-(1)*h50-((1 / (x^2)))*h53-(1)*h57-(((-2) / ((x^2) * (z^2))))*h58-((((-1) * (z^2)) / (y^2)))*h60-(((-2) / (z^2)))*h61-(1)*h69-((((-4) + ((-1) * (x^6)) + (3 * (x^4)) + ((-1) * (a^2) * (x^4)) + (2 * (a^2) * (x^2)) + ((-1) * (a^2) * (x^2) * (y^2)) + ((-1) * a * b * y * (x^3)) + (2 * a * b * x * y)) / ((x^2) * (4 + (x^4) + ((-4) * (x^2)) + ((a^2) * (x^2)) + ((-3) * a * x) + ((-2) * b * y) + (a * x * (y^2)) + (b * y * (x^2))))))*h71-(1)*h76-(1)*h77-((1 / ((x^2) * (y^2))))*h85-((1 / ((x^2) * (y^2))))*h86-((2 / ((x^2) * (y^2))))*h87-(1)*h93-((-1))*h98-(1)*h106-(1)*h109-((-1))*h113-((a / x))*h116-(1)*h117-((((-1) + (y^2) + (2 * (x^2)) + ((-1) * a * (x^3)) + ((-1) * (a^2) * (y^2)) + ((-1) * a * x * (y^2))) / ((-1) + (y^2) + (2 * (x^2)) + (a * x))))*h118-((((a * (y^2)) + ((-1) * a * (x^2))) / ((x^3) * (y^2))))*h119-(1)*h122-(1)*h135-(1)*h141-(1)*h142-(1)*h145-(1)*h148
#print axioms reduced_step149

end QuantitativeArithmeticSmallLevelTwentyFive.ContinuationNegative
end
end
end
