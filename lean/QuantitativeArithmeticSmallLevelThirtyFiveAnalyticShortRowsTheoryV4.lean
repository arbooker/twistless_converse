module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import QuantitativeArithmeticAnalyticGermTheoryV4
public import QuantitativeArithmeticCompact35AnalyticWeightsV1
public import QuantitativeArithmeticCompact35ColumnsSynchronousV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveAnalyticRowIndexIdentitySeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open scoped Topology

theorem identity0 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients0 x y z w a b i*sources0 x y z w a b v i)=
      reduced0 x y z w a b v := by
  norm_num [coefficients0,sources0,reduced0,Fin.sum_univ_succ]
  linear_combination (closedRow0Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow0Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow0Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow0Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow0Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow0Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow0Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow0Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow0Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow0Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow0Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow0Column16 x y z w a b hx hy hz hw)*v 16 +
    (closedRow0Column18 x y z w a b hx hy hz hw)*v 18 +
    (closedRow0Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow0Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow0Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow0Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow0Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow0Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow0Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow0Column36 x y z w a b hx hy hz hw)*v 36 +
    (closedRow0Column39 x y z w a b hx hy hz hw)*v 39 +
    (closedRow0Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow0Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow0Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow0Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow0Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow0Column51 x y z w a b hx hy hz hw)*v 51 +
    (closedRow0Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow0Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow0Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow0Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow0Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow0Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow0Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow0Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow0Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow0Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow0Column81 x y z w a b hx hy hz hw)*v 81 +
    (closedRow0Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow0Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow0Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow0Column93 x y z w a b hx hy hz hw)*v 93 +
    (closedRow0Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow0Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow0Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow0Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow0Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow0Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow0Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow0Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow0Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow0Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow0Column109 x y z w a b hx hy hz hw)*v 109 +
    (closedRow0Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow0Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow0Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow0Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow0Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow0Column123 x y z w a b hx hy hz hw)*v 123 +
    (closedRow0Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow0Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow0Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow0Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow0Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow0Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow0Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow0Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow0Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow0Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow0Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow0Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow0Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow0Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow0Column162 x y z w a b hx hy hz hw)*v 162 +
    (closedRow0Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow0Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow0Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow0Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow0Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow0Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow0Column175 x y z w a b hx hy hz hw)*v 175 +
    (closedRow0Column177 x y z w a b hx hy hz hw)*v 177 +
    (closedRow0Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow0Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow0Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow0Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow0Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow0Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow0Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow0Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow0Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow0Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow0Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow0Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow0Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow0Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow0Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow0Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow0Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity0


theorem identity13 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients13 x y z w a b i*sources13 x y z w a b v i)=
      reduced13 x y z w a b v := by
  norm_num [coefficients13,sources13,reduced13,Fin.sum_univ_succ]
  linear_combination (closedRow13Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow13Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow13Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow13Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow13Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow13Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow13Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow13Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow13Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow13Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow13Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow13Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow13Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow13Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow13Column25 x y z w a b hx hy hz hw)*v 25 +
    (closedRow13Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow13Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow13Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow13Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow13Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow13Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow13Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow13Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow13Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow13Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow13Column55 x y z w a b hx hy hz hw)*v 55 +
    (closedRow13Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow13Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow13Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow13Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow13Column66 x y z w a b hx hy hz hw)*v 66 +
    (closedRow13Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow13Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow13Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow13Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow13Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow13Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow13Column85 x y z w a b hx hy hz hw)*v 85 +
    (closedRow13Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow13Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow13Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow13Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow13Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow13Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow13Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow13Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow13Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow13Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow13Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow13Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow13Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow13Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow13Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow13Column115 x y z w a b hx hy hz hw)*v 115 +
    (closedRow13Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow13Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow13Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow13Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow13Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow13Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow13Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow13Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow13Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow13Column145 x y z w a b hx hy hz hw)*v 145 +
    (closedRow13Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow13Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow13Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow13Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow13Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow13Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow13Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow13Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow13Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow13Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow13Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow13Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow13Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow13Column175 x y z w a b hx hy hz hw)*v 175 +
    (closedRow13Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow13Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow13Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow13Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow13Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow13Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow13Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow13Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow13Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow13Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow13Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow13Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow13Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow13Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow13Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow13Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow13Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity13


theorem identity14 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients14 x y z w a b i*sources14 x y z w a b v i)=
      reduced14 x y z w a b v := by
  norm_num [coefficients14,sources14,reduced14,Fin.sum_univ_succ]
  linear_combination (closedRow14Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow14Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow14Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow14Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow14Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow14Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow14Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow14Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow14Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow14Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow14Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow14Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow14Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow14Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow14Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow14Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow14Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow14Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow14Column36 x y z w a b hx hy hz hw)*v 36 +
    (closedRow14Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow14Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow14Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow14Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow14Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow14Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow14Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow14Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow14Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow14Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow14Column66 x y z w a b hx hy hz hw)*v 66 +
    (closedRow14Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow14Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow14Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow14Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow14Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow14Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow14Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow14Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow14Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow14Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow14Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow14Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow14Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow14Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow14Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow14Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow14Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow14Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow14Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow14Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow14Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow14Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow14Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow14Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow14Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow14Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow14Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow14Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow14Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow14Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow14Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow14Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow14Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow14Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow14Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow14Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow14Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow14Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow14Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow14Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow14Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow14Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow14Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow14Column175 x y z w a b hx hy hz hw)*v 175 +
    (closedRow14Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow14Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow14Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow14Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow14Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow14Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow14Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow14Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow14Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow14Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow14Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow14Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow14Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow14Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow14Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow14Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow14Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity14


theorem identity163 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients163 x y z w a b i*sources163 x y z w a b v i)=
      reduced163 x y z w a b v := by
  norm_num [coefficients163,sources163,reduced163,Fin.sum_univ_succ]
  linear_combination (closedRow163Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow163Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow163Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow163Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow163Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow163Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow163Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow163Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow163Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow163Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow163Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow163Column16 x y z w a b hx hy hz hw)*v 16 +
    (closedRow163Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow163Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow163Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow163Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow163Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow163Column32 x y z w a b hx hy hz hw)*v 32 +
    (closedRow163Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow163Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow163Column36 x y z w a b hx hy hz hw)*v 36 +
    (closedRow163Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow163Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow163Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow163Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow163Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow163Column51 x y z w a b hx hy hz hw)*v 51 +
    (closedRow163Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow163Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow163Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow163Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow163Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow163Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow163Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow163Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow163Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow163Column78 x y z w a b hx hy hz hw)*v 78 +
    (closedRow163Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow163Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow163Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow163Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow163Column93 x y z w a b hx hy hz hw)*v 93 +
    (closedRow163Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow163Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow163Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow163Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow163Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow163Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow163Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow163Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow163Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow163Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow163Column109 x y z w a b hx hy hz hw)*v 109 +
    (closedRow163Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow163Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow163Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow163Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow163Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow163Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow163Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow163Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow163Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow163Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow163Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow163Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow163Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow163Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow163Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow163Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow163Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow163Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow163Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow163Column162 x y z w a b hx hy hz hw)*v 162 +
    (closedRow163Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow163Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow163Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow163Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow163Column172 x y z w a b hx hy hz hw)*v 172 +
    (closedRow163Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow163Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow163Column175 x y z w a b hx hy hz hw)*v 175 +
    (closedRow163Column177 x y z w a b hx hy hz hw)*v 177 +
    (closedRow163Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow163Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow163Column183 x y z w a b hx hy hz hw)*v 183 +
    (closedRow163Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow163Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow163Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow163Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow163Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow163Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow163Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow163Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow163Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow163Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow163Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow163Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow163Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow163Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow163Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity163


theorem identity164 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients164 x y z w a b i*sources164 x y z w a b v i)=
      reduced164 x y z w a b v := by
  norm_num [coefficients164,sources164,reduced164,Fin.sum_univ_succ]
  linear_combination (closedRow164Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow164Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow164Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow164Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow164Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow164Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow164Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow164Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow164Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow164Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow164Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow164Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow164Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow164Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow164Column27 x y z w a b hx hy hz hw)*v 27 +
    (closedRow164Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow164Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow164Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow164Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow164Column38 x y z w a b hx hy hz hw)*v 38 +
    (closedRow164Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow164Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow164Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow164Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow164Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow164Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow164Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow164Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow164Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow164Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow164Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow164Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow164Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow164Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow164Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow164Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow164Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow164Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow164Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow164Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow164Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow164Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow164Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow164Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow164Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow164Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow164Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow164Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow164Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow164Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow164Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow164Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow164Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow164Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow164Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow164Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow164Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow164Column132 x y z w a b hx hy hz hw)*v 132 +
    (closedRow164Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow164Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow164Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow164Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow164Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow164Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow164Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow164Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow164Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow164Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow164Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow164Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow164Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow164Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow164Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow164Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow164Column178 x y z w a b hx hy hz hw)*v 178 +
    (closedRow164Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow164Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow164Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow164Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow164Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow164Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow164Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow164Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow164Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow164Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow164Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow164Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow164Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow164Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow164Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow164Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow164Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity164


theorem identity16 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients16 x y z w a b i*sources16 x y z w a b v i)=
      reduced16 x y z w a b v := by
  norm_num [coefficients16,sources16,reduced16,Fin.sum_univ_succ]
  linear_combination (closedRow16Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow16Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow16Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow16Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow16Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow16Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow16Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow16Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow16Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow16Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow16Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow16Column16 x y z w a b hx hy hz hw)*v 16 +
    (closedRow16Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow16Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow16Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow16Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow16Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow16Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow16Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow16Column39 x y z w a b hx hy hz hw)*v 39 +
    (closedRow16Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow16Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow16Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow16Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow16Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow16Column51 x y z w a b hx hy hz hw)*v 51 +
    (closedRow16Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow16Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow16Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow16Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow16Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow16Column66 x y z w a b hx hy hz hw)*v 66 +
    (closedRow16Column69 x y z w a b hx hy hz hw)*v 69 +
    (closedRow16Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow16Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow16Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow16Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow16Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow16Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow16Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow16Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow16Column93 x y z w a b hx hy hz hw)*v 93 +
    (closedRow16Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow16Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow16Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow16Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow16Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow16Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow16Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow16Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow16Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow16Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow16Column109 x y z w a b hx hy hz hw)*v 109 +
    (closedRow16Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow16Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow16Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow16Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow16Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow16Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow16Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow16Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow16Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow16Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow16Column138 x y z w a b hx hy hz hw)*v 138 +
    (closedRow16Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow16Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow16Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow16Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow16Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow16Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow16Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow16Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow16Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow16Column162 x y z w a b hx hy hz hw)*v 162 +
    (closedRow16Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow16Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow16Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow16Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow16Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow16Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow16Column177 x y z w a b hx hy hz hw)*v 177 +
    (closedRow16Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow16Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow16Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow16Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow16Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow16Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow16Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow16Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow16Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow16Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow16Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow16Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow16Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow16Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow16Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow16Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow16Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity16


theorem identity19 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients19 x y z w a b i*sources19 x y z w a b v i)=
      reduced19 x y z w a b v := by
  norm_num [coefficients19,sources19,reduced19,Fin.sum_univ_succ]
  linear_combination (closedRow19Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow19Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow19Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow19Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow19Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow19Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow19Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow19Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow19Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow19Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow19Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow19Column16 x y z w a b hx hy hz hw)*v 16 +
    (closedRow19Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow19Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow19Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow19Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow19Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow19Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow19Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow19Column36 x y z w a b hx hy hz hw)*v 36 +
    (closedRow19Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow19Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow19Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow19Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow19Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow19Column51 x y z w a b hx hy hz hw)*v 51 +
    (closedRow19Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow19Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow19Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow19Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow19Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow19Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow19Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow19Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow19Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow19Column78 x y z w a b hx hy hz hw)*v 78 +
    (closedRow19Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow19Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow19Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow19Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow19Column93 x y z w a b hx hy hz hw)*v 93 +
    (closedRow19Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow19Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow19Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow19Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow19Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow19Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow19Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow19Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow19Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow19Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow19Column109 x y z w a b hx hy hz hw)*v 109 +
    (closedRow19Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow19Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow19Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow19Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow19Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow19Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow19Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow19Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow19Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow19Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow19Column138 x y z w a b hx hy hz hw)*v 138 +
    (closedRow19Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow19Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow19Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow19Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow19Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow19Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow19Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow19Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow19Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow19Column162 x y z w a b hx hy hz hw)*v 162 +
    (closedRow19Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow19Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow19Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow19Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow19Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow19Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow19Column175 x y z w a b hx hy hz hw)*v 175 +
    (closedRow19Column177 x y z w a b hx hy hz hw)*v 177 +
    (closedRow19Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow19Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow19Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow19Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow19Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow19Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow19Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow19Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow19Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow19Column198 x y z w a b hx hy hz hw)*v 198 +
    (closedRow19Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow19Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow19Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow19Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow19Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow19Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow19Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow19Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity19


theorem identity21 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients21 x y z w a b i*sources21 x y z w a b v i)=
      reduced21 x y z w a b v := by
  norm_num [coefficients21,sources21,reduced21,Fin.sum_univ_succ]
  linear_combination (closedRow21Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow21Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow21Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow21Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow21Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow21Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow21Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow21Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow21Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow21Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow21Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow21Column16 x y z w a b hx hy hz hw)*v 16 +
    (closedRow21Column18 x y z w a b hx hy hz hw)*v 18 +
    (closedRow21Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow21Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow21Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow21Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow21Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow21Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow21Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow21Column36 x y z w a b hx hy hz hw)*v 36 +
    (closedRow21Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow21Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow21Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow21Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow21Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow21Column51 x y z w a b hx hy hz hw)*v 51 +
    (closedRow21Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow21Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow21Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow21Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow21Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow21Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow21Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow21Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow21Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow21Column78 x y z w a b hx hy hz hw)*v 78 +
    (closedRow21Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow21Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow21Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow21Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow21Column93 x y z w a b hx hy hz hw)*v 93 +
    (closedRow21Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow21Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow21Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow21Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow21Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow21Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow21Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow21Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow21Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow21Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow21Column109 x y z w a b hx hy hz hw)*v 109 +
    (closedRow21Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow21Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow21Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow21Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow21Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow21Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow21Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow21Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow21Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow21Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow21Column138 x y z w a b hx hy hz hw)*v 138 +
    (closedRow21Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow21Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow21Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow21Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow21Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow21Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow21Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow21Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow21Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow21Column162 x y z w a b hx hy hz hw)*v 162 +
    (closedRow21Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow21Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow21Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow21Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow21Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow21Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow21Column175 x y z w a b hx hy hz hw)*v 175 +
    (closedRow21Column177 x y z w a b hx hy hz hw)*v 177 +
    (closedRow21Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow21Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow21Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow21Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow21Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow21Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow21Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow21Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow21Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow21Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow21Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow21Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow21Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow21Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow21Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow21Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow21Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity21


theorem identity26 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients26 x y z w a b i*sources26 x y z w a b v i)=
      reduced26 x y z w a b v := by
  norm_num [coefficients26,sources26,reduced26,Fin.sum_univ_succ]
  linear_combination (closedRow26Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow26Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow26Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow26Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow26Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow26Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow26Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow26Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow26Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow26Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow26Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow26Column16 x y z w a b hx hy hz hw)*v 16 +
    (closedRow26Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow26Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow26Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow26Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow26Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow26Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow26Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow26Column36 x y z w a b hx hy hz hw)*v 36 +
    (closedRow26Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow26Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow26Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow26Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow26Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow26Column51 x y z w a b hx hy hz hw)*v 51 +
    (closedRow26Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow26Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow26Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow26Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow26Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow26Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow26Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow26Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow26Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow26Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow26Column81 x y z w a b hx hy hz hw)*v 81 +
    (closedRow26Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow26Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow26Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow26Column93 x y z w a b hx hy hz hw)*v 93 +
    (closedRow26Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow26Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow26Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow26Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow26Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow26Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow26Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow26Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow26Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow26Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow26Column109 x y z w a b hx hy hz hw)*v 109 +
    (closedRow26Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow26Column111 x y z w a b hx hy hz hw)*v 111 +
    (closedRow26Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow26Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow26Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow26Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow26Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow26Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow26Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow26Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow26Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow26Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow26Column141 x y z w a b hx hy hz hw)*v 141 +
    (closedRow26Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow26Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow26Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow26Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow26Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow26Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow26Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow26Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow26Column162 x y z w a b hx hy hz hw)*v 162 +
    (closedRow26Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow26Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow26Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow26Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow26Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow26Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow26Column175 x y z w a b hx hy hz hw)*v 175 +
    (closedRow26Column177 x y z w a b hx hy hz hw)*v 177 +
    (closedRow26Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow26Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow26Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow26Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow26Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow26Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow26Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow26Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow26Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow26Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow26Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow26Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow26Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow26Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow26Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow26Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow26Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity26


theorem identity3 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients3 x y z w a b i*sources3 x y z w a b v i)=
      reduced3 x y z w a b v := by
  norm_num [coefficients3,sources3,reduced3,Fin.sum_univ_succ]
  linear_combination (closedRow3Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow3Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow3Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow3Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow3Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow3Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow3Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow3Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow3Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow3Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow3Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow3Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow3Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow3Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow3Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow3Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow3Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow3Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow3Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow3Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow3Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow3Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow3Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow3Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow3Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow3Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow3Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow3Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow3Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow3Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow3Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow3Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow3Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow3Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow3Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow3Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow3Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow3Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow3Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow3Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow3Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow3Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow3Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow3Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow3Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow3Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow3Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow3Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow3Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow3Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow3Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow3Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow3Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow3Column138 x y z w a b hx hy hz hw)*v 138 +
    (closedRow3Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow3Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow3Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow3Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow3Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow3Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow3Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow3Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow3Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow3Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow3Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow3Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow3Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow3Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow3Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow3Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow3Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow3Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow3Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow3Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow3Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow3Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow3Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow3Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow3Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow3Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow3Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow3Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity3


theorem identity9 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients9 x y z w a b i*sources9 x y z w a b v i)=
      reduced9 x y z w a b v := by
  norm_num [coefficients9,sources9,reduced9,Fin.sum_univ_succ]
  linear_combination (closedRow9Column0 x y z w a b hx hy hz hw)*v 0 +
    (closedRow9Column2 x y z w a b hx hy hz hw)*v 2 +
    (closedRow9Column4 x y z w a b hx hy hz hw)*v 4 +
    (closedRow9Column5 x y z w a b hx hy hz hw)*v 5 +
    (closedRow9Column6 x y z w a b hx hy hz hw)*v 6 +
    (closedRow9Column7 x y z w a b hx hy hz hw)*v 7 +
    (closedRow9Column8 x y z w a b hx hy hz hw)*v 8 +
    (closedRow9Column10 x y z w a b hx hy hz hw)*v 10 +
    (closedRow9Column12 x y z w a b hx hy hz hw)*v 12 +
    (closedRow9Column14 x y z w a b hx hy hz hw)*v 14 +
    (closedRow9Column15 x y z w a b hx hy hz hw)*v 15 +
    (closedRow9Column16 x y z w a b hx hy hz hw)*v 16 +
    (closedRow9Column18 x y z w a b hx hy hz hw)*v 18 +
    (closedRow9Column20 x y z w a b hx hy hz hw)*v 20 +
    (closedRow9Column21 x y z w a b hx hy hz hw)*v 21 +
    (closedRow9Column24 x y z w a b hx hy hz hw)*v 24 +
    (closedRow9Column28 x y z w a b hx hy hz hw)*v 28 +
    (closedRow9Column30 x y z w a b hx hy hz hw)*v 30 +
    (closedRow9Column33 x y z w a b hx hy hz hw)*v 33 +
    (closedRow9Column35 x y z w a b hx hy hz hw)*v 35 +
    (closedRow9Column36 x y z w a b hx hy hz hw)*v 36 +
    (closedRow9Column40 x y z w a b hx hy hz hw)*v 40 +
    (closedRow9Column42 x y z w a b hx hy hz hw)*v 42 +
    (closedRow9Column45 x y z w a b hx hy hz hw)*v 45 +
    (closedRow9Column48 x y z w a b hx hy hz hw)*v 48 +
    (closedRow9Column50 x y z w a b hx hy hz hw)*v 50 +
    (closedRow9Column51 x y z w a b hx hy hz hw)*v 51 +
    (closedRow9Column54 x y z w a b hx hy hz hw)*v 54 +
    (closedRow9Column56 x y z w a b hx hy hz hw)*v 56 +
    (closedRow9Column60 x y z w a b hx hy hz hw)*v 60 +
    (closedRow9Column63 x y z w a b hx hy hz hw)*v 63 +
    (closedRow9Column65 x y z w a b hx hy hz hw)*v 65 +
    (closedRow9Column70 x y z w a b hx hy hz hw)*v 70 +
    (closedRow9Column72 x y z w a b hx hy hz hw)*v 72 +
    (closedRow9Column75 x y z w a b hx hy hz hw)*v 75 +
    (closedRow9Column77 x y z w a b hx hy hz hw)*v 77 +
    (closedRow9Column78 x y z w a b hx hy hz hw)*v 78 +
    (closedRow9Column80 x y z w a b hx hy hz hw)*v 80 +
    (closedRow9Column84 x y z w a b hx hy hz hw)*v 84 +
    (closedRow9Column87 x y z w a b hx hy hz hw)*v 87 +
    (closedRow9Column90 x y z w a b hx hy hz hw)*v 90 +
    (closedRow9Column93 x y z w a b hx hy hz hw)*v 93 +
    (closedRow9Column95 x y z w a b hx hy hz hw)*v 95 +
    (closedRow9Column96 x y z w a b hx hy hz hw)*v 96 +
    (closedRow9Column98 x y z w a b hx hy hz hw)*v 98 +
    (closedRow9Column99 x y z w a b hx hy hz hw)*v 99 +
    (closedRow9Column100 x y z w a b hx hy hz hw)*v 100 +
    (closedRow9Column102 x y z w a b hx hy hz hw)*v 102 +
    (closedRow9Column103 x y z w a b hx hy hz hw)*v 103 +
    (closedRow9Column105 x y z w a b hx hy hz hw)*v 105 +
    (closedRow9Column107 x y z w a b hx hy hz hw)*v 107 +
    (closedRow9Column108 x y z w a b hx hy hz hw)*v 108 +
    (closedRow9Column109 x y z w a b hx hy hz hw)*v 109 +
    (closedRow9Column110 x y z w a b hx hy hz hw)*v 110 +
    (closedRow9Column112 x y z w a b hx hy hz hw)*v 112 +
    (closedRow9Column114 x y z w a b hx hy hz hw)*v 114 +
    (closedRow9Column117 x y z w a b hx hy hz hw)*v 117 +
    (closedRow9Column120 x y z w a b hx hy hz hw)*v 120 +
    (closedRow9Column123 x y z w a b hx hy hz hw)*v 123 +
    (closedRow9Column125 x y z w a b hx hy hz hw)*v 125 +
    (closedRow9Column126 x y z w a b hx hy hz hw)*v 126 +
    (closedRow9Column129 x y z w a b hx hy hz hw)*v 129 +
    (closedRow9Column130 x y z w a b hx hy hz hw)*v 130 +
    (closedRow9Column135 x y z w a b hx hy hz hw)*v 135 +
    (closedRow9Column140 x y z w a b hx hy hz hw)*v 140 +
    (closedRow9Column144 x y z w a b hx hy hz hw)*v 144 +
    (closedRow9Column147 x y z w a b hx hy hz hw)*v 147 +
    (closedRow9Column150 x y z w a b hx hy hz hw)*v 150 +
    (closedRow9Column153 x y z w a b hx hy hz hw)*v 153 +
    (closedRow9Column154 x y z w a b hx hy hz hw)*v 154 +
    (closedRow9Column155 x y z w a b hx hy hz hw)*v 155 +
    (closedRow9Column156 x y z w a b hx hy hz hw)*v 156 +
    (closedRow9Column159 x y z w a b hx hy hz hw)*v 159 +
    (closedRow9Column160 x y z w a b hx hy hz hw)*v 160 +
    (closedRow9Column162 x y z w a b hx hy hz hw)*v 162 +
    (closedRow9Column165 x y z w a b hx hy hz hw)*v 165 +
    (closedRow9Column168 x y z w a b hx hy hz hw)*v 168 +
    (closedRow9Column170 x y z w a b hx hy hz hw)*v 170 +
    (closedRow9Column171 x y z w a b hx hy hz hw)*v 171 +
    (closedRow9Column173 x y z w a b hx hy hz hw)*v 173 +
    (closedRow9Column174 x y z w a b hx hy hz hw)*v 174 +
    (closedRow9Column175 x y z w a b hx hy hz hw)*v 175 +
    (closedRow9Column177 x y z w a b hx hy hz hw)*v 177 +
    (closedRow9Column180 x y z w a b hx hy hz hw)*v 180 +
    (closedRow9Column182 x y z w a b hx hy hz hw)*v 182 +
    (closedRow9Column183 x y z w a b hx hy hz hw)*v 183 +
    (closedRow9Column185 x y z w a b hx hy hz hw)*v 185 +
    (closedRow9Column186 x y z w a b hx hy hz hw)*v 186 +
    (closedRow9Column189 x y z w a b hx hy hz hw)*v 189 +
    (closedRow9Column190 x y z w a b hx hy hz hw)*v 190 +
    (closedRow9Column192 x y z w a b hx hy hz hw)*v 192 +
    (closedRow9Column195 x y z w a b hx hy hz hw)*v 195 +
    (closedRow9Column196 x y z w a b hx hy hz hw)*v 196 +
    (closedRow9Column200 x y z w a b hx hy hz hw)*v 200 +
    (closedRow9Column201 x y z w a b hx hy hz hw)*v 201 +
    (closedRow9Column202 x y z w a b hx hy hz hw)*v 202 +
    (closedRow9Column203 x y z w a b hx hy hz hw)*v 203 +
    (closedRow9Column204 x y z w a b hx hy hz hw)*v 204 +
    (closedRow9Column205 x y z w a b hx hy hz hw)*v 205 +
    (closedRow9Column207 x y z w a b hx hy hz hw)*v 207 +
    (closedRow9Column208 x y z w a b hx hy hz hw)*v 208

#print axioms identity9
end QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
end
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open scoped Topology

theorem analytic_reduced0 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources0 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced0 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 94) : AnalyticAt ℂ
      (fun t => coefficients0 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow0Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight85_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight86_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight87_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight88_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight89_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight90_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight91_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight92_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow0Weight93_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients0 (X t) (Y t) (Z t) (W t) a b i*
      sources0 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity0 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced0

def coefficients104 (x y z w a b : ℂ) : Fin 79 → ℂ :=
  ![((-1 + (-2)*w + (-1)*x*a)/(z*w)),
    ((-2 + (-2)*x*a + (4)*x^(3:ℕ)*a + (4)*x^(4:ℕ))/(w)),
    ((8 + (2)*w + (4)*z + (-2)*z*w + (4)*x*a + x*y^(2:ℕ)*a + (-3)*x^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ))/(z*w)),
    ((3)*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y^(4:ℕ)),
    ((-3)*x*y^(2:ℕ)*a + (-1)*x*y^(4:ℕ)*a),
    (((4)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ)*y^(2:ℕ))/(z)),
    (-2),
    (((-2)*x^(4:ℕ)*y^(2:ℕ))/(w)),
    (((4)*y^(2:ℕ) + (-2)*x*y^(2:ℕ)*a + (2)*x^(2:ℕ)*y^(2:ℕ) + (-4)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-4)*x^(3:ℕ)*y^(2:ℕ)*a)/(z)),
    (-1),
    ((y^(2:ℕ) + (-2)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ))/(w)),
    (((2)*x^(2:ℕ) + (2)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ) + (-2)*x^(4:ℕ)*y*b + (2)*x^(4:ℕ)*y^(2:ℕ) + (2)*x^(5:ℕ)*a)/(z)),
    (((2)*x*y^(2:ℕ)*a + (2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-2)*x^(2:ℕ) + (2)*x^(3:ℕ)*y*a*b + (2)*x^(4:ℕ) + (2)*x^(4:ℕ)*y*b)/(w)),
    ((-2 + (-4)*y*b + (-2)*y^(2:ℕ) + (-2)*x*a + (-2)*x*z*a + (2)*x*y*a*b + (-4)*x*y^(2:ℕ)*a + (2)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-4)*x^(3:ℕ)*a + (2)*x^(3:ℕ)*y*a*b + (-2)*x^(3:ℕ)*y^(2:ℕ)*a + (-2)*x^(4:ℕ)*a^(2:ℕ))/(z)),
    (((2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (-1),
    (((-1)*w + (-3)*z + (-4)*y*b + (-4)*y^(2:ℕ) + (6)*x*a + (-2)*x*z*a + (4)*x*y*a*b + (-4)*x*y^(2:ℕ)*a + (2)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2)*x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-6)*x^(3:ℕ)*a + (2)*x^(3:ℕ)*y*a*b + (-2)*x^(3:ℕ)*y^(2:ℕ)*a + (-2)*x^(4:ℕ)*a^(2:ℕ))/(w)),
    (((2)*x^(2:ℕ) + (-2)*x^(3:ℕ)*a)/(z)),
    (((2)*x^(2:ℕ) + (2)*x^(3:ℕ)*a)/(z)),
    (((-2)*y^(2:ℕ) + (-2)*y^(2:ℕ)*z)/(z*w)),
    ((-3 + (-1)*z + (2)*x*a + (2)*x*y*a*b + (2)*x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ) + (-2)*x^(4:ℕ)*y*b + (2)*x^(4:ℕ)*y^(2:ℕ) + (2)*x^(5:ℕ)*a)/(w)),
    ((1 + (-2)*x*a)/(z)),
    (((-1)*x^(2:ℕ))/(z*w)),
    ((-1 + (-1)*z + (-2)*y^(2:ℕ) + (-4)*x*a + (2)*x*y*a*b + (-2)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ) + (2)*x^(2:ℕ)*y*b + (-2)*x^(2:ℕ)*y^(2:ℕ))/(w)),
    (((-2)*y^(2:ℕ))/(z*w)),
    ((2 + w + z + (4)*y*b + (2)*y^(2:ℕ) + (-6)*x*a + (2)*x*z*a + (-2)*x*y*a*b + (2)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ) + (-2)*x^(2:ℕ)*y*a^(2:ℕ)*b + (2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (6)*x^(3:ℕ)*a + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (2)*x^(4:ℕ)*a^(2:ℕ))/(z)),
    ((-2)*y^(2:ℕ)),
    (-3 + (-1)*y^(2:ℕ)),
    ((3)*y^(2:ℕ) + y^(3:ℕ)*b + y^(4:ℕ)),
    (-2),
    (((2)*x^(2:ℕ) + (2)*x^(2:ℕ)*z + (3)*x^(3:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a)/(z*w)),
    ((3)*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y^(4:ℕ)),
    (((-2)*y^(2:ℕ) + (-2)*x*y^(2:ℕ)*a + (4)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ)*y^(2:ℕ))/(z)),
    ((1 + (-1)*z + (-2)*y^(2:ℕ) + (-2)*x*a + (2)*x*y*a*b + (-2)*x*y^(2:ℕ)*a + (2)*x^(2:ℕ)*y*b + (-2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (-2),
    (x^(2:ℕ)*y*b),
    (((-2)*x*y^(2:ℕ)*a + (2)*x^(3:ℕ)*y^(2:ℕ)*a)/(w)),
    (2),
    ((-3 + (-1)*z + (2)*x*a + (2)*x*y*a*b + (2)*x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ) + (-2)*x^(4:ℕ)*y*b + (2)*x^(4:ℕ)*y^(2:ℕ) + (2)*x^(5:ℕ)*a)/(z)),
    (((-2)*x*y^(2:ℕ)*a)/(w)),
    ((-1)*x^(2:ℕ)*y^(2:ℕ)),
    ((2 + w + z + (4)*y*b + (2)*y^(2:ℕ) + (-6)*x*a + (2)*x*z*a + (-2)*x*y*a*b + (2)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ) + (-2)*x^(2:ℕ)*y*a^(2:ℕ)*b + (2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (6)*x^(3:ℕ)*a + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (2)*x^(4:ℕ)*a^(2:ℕ))/(w)),
    (-1 + (-2)*w + (-1)*x*a),
    ((x^(2:ℕ)*y^(2:ℕ))/(z*w)),
    (((-2)*y^(2:ℕ) + (-2)*x*y^(2:ℕ)*a)/(z)),
    ((-1)*x^(2:ℕ)*y^(2:ℕ)),
    (y^(2:ℕ)),
    (((2)*y^(2:ℕ) + y^(2:ℕ)*z)/(z*w)),
    (((2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-2)*x^(3:ℕ)*y^(2:ℕ)*a + (-2)*x^(4:ℕ)*y^(2:ℕ))/(w)),
    (((2)*y^(2:ℕ) + (-2)*x*y^(2:ℕ)*a)/(z)),
    (((-2)*x*y^(2:ℕ)*a)/(z)),
    ((1 + (-2)*w + (-1)*z + (-2)*y^(2:ℕ) + (4)*x*a + (2)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ) + (-2)*x^(3:ℕ)*a)/(w)),
    (-1),
    (-1),
    (-2),
    (((-1)*y^(2:ℕ))/(w)),
    ((y^(2:ℕ))/(w)),
    ((2 + (2)*y^(2:ℕ) + (-2)*x*y*a*b + (2)*x*y^(2:ℕ)*a + (2)*x^(2:ℕ) + (-2)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((2)*x^(2:ℕ) + (-2)*x^(3:ℕ)*a + (-2)*x^(4:ℕ))/(w)),
    (((-1)*y^(2:ℕ) + (2)*x*y^(2:ℕ)*a)/(w)),
    (((2)*x*y^(2:ℕ)*a)/(z)),
    (1),
    ((-3)*x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(2:ℕ)*y^(4:ℕ)),
    (((-4)*x^(3:ℕ)*y^(2:ℕ)*a + (-4)*x^(4:ℕ)*y^(2:ℕ))/(z)),
    (((-2)*x^(3:ℕ)*y^(2:ℕ)*a)/(w)),
    (((-2)*x^(2:ℕ) + (-2)*x^(2:ℕ)*z + (-2)*x^(2:ℕ)*y^(2:ℕ) + (2)*x^(3:ℕ)*y*a*b + (-2)*x^(3:ℕ)*y^(2:ℕ)*a + (-4)*x^(4:ℕ) + (2)*x^(4:ℕ)*y*b + (-2)*x^(4:ℕ)*y^(2:ℕ) + (-2)*x^(5:ℕ)*a)/(z)),
    (((2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-4)*x^(2:ℕ))/(z)),
    (((2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    ((-1)*x^(2:ℕ)),
    (((2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((2)*x^(3:ℕ)*y^(2:ℕ)*a + (2)*x^(4:ℕ)*y^(2:ℕ))/(w)),
    (((-4)*y^(2:ℕ) + (-2)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (x^(2:ℕ)*y^(2:ℕ))]

def sources104 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Fin 79 → ℂ :=
  ![(1)*v 0 + (z*w)*v 204,
    (1)*v 42 + ((x^(2:ℕ)*y^(2:ℕ)*w)/(z))*v 205,
    (1)*v 0,
    ((1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 2,
    (1)*v 4 + ((x^(2:ℕ))/(y^(2:ℕ)*z*w))*v 105,
    (1)*v 5 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168,
    ((1)/(z*w))*v 0 + (1)*v 6,
    (1)*v 7 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30,
    (1)*v 10 + ((z)/(y^(2:ℕ)*w))*v 84,
    (1)*v 12 + ((x^(2:ℕ))/(z*w))*v 105,
    (1)*v 14 + ((w)/(y^(2:ℕ)*z))*v 120,
    (1)*v 15 + ((z)/(x^(2:ℕ)*w))*v 126,
    (1)*v 20 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147,
    (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150,
    (1)*v 30 + ((z)/(w))*v 168,
    (1)*v 35 + ((z*w)/(x^(2:ℕ)*y^(2:ℕ)))*v 174,
    (1)*v 36 + ((x^(2:ℕ)*y^(2:ℕ))/(z*w))*v 175,
    (1)*v 42 + ((w)/(z))*v 180,
    (1)*v 45 + ((y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182,
    (1)*v 60 + ((x^(2:ℕ)*z)/(w))*v 189,
    (1)*v 70 + ((z*w)/(y^(2:ℕ)))*v 192,
    (1)*v 84 + ((x^(2:ℕ)*w)/(z))*v 195,
    (1)*v 90 + ((y^(2:ℕ)*z)/(w))*v 196,
    (1)*v 105 + ((z*w)/(x^(2:ℕ)))*v 198,
    (1)*v 126 + ((y^(2:ℕ)*w)/(z))*v 200,
    (1)*v 140 + ((x^(2:ℕ)*z*w)/(y^(2:ℕ)))*v 201,
    (1)*v 180 + ((x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203,
    ((1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 208,
    ((-1)*y^(2:ℕ))*v 8 + (1)*v 186,
    ((-1)/(y^(2:ℕ)))*v 24 + (1)*v 202,
    (1)*v 102 + ((-1)*y^(2:ℕ))*v 208,
    ((-1)/(x^(2:ℕ)))*v 0 + (1)*v 105,
    (1)*v 107 + ((-1)/(x^(2:ℕ)))*v 202,
    (1)*v 110 + ((-1)*x^(2:ℕ))*v 205,
    (1)*v 90 + ((-1)*y^(2:ℕ))*v 200,
    (1)*v 96 + ((-1)*x^(2:ℕ))*v 201,
    (1)*v 99 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202,
    (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189,
    (1)*v 114 + (-1)*v 192,
    (1)*v 120 + ((-1)*x^(2:ℕ))*v 195,
    (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98,
    (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186,
    (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203,
    (1)*v 174 + (-1)*v 204,
    ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 0 + (1)*v 175,
    (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170,
    ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173,
    ((-1)*x^(2:ℕ))*v 33 + (1)*v 186,
    (1)*v 70 + (1)*v 140,
    (1)*v 65 + ((z)/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + ((z)/(x^(2:ℕ)*w))*v 168,
    ((w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + ((w)/(x^(2:ℕ)*z))*v 120 + (1)*v 147,
    ((z)/(w))*v 56 + (1)*v 80 + ((z)/(w))*v 126 + (1)*v 150,
    (1)*v 60 + ((z)/(w))*v 84 + (1)*v 130 + ((z)/(w))*v 154,
    (1)*v 42 + (1)*v 84 + (1)*v 126 + (1)*v 168,
    ((1)/(w))*v 0 + ((1)/(w))*v 42 + (1)*v 48 + ((1)/(w))*v 84 + (1)*v 90 + ((1)/(w))*v 126 + (1)*v 132 + (1)*v 174,
    ((1)/(w))*v 0 + (1)*v 36 + (1)*v 78 + ((1)/(w))*v 84 + (1)*v 120 + ((1)/(w))*v 126 + (1)*v 162 + ((1)/(w))*v 168,
    (1)*v 30 + ((x^(2:ℕ))/(w))*v 63 + (1)*v 72 + ((x^(2:ℕ))/(w))*v 105 + (1)*v 114 + ((x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((x^(2:ℕ))/(w))*v 189,
    ((w)/(y^(2:ℕ)))*v 24 + (1)*v 56 + ((w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + ((w)/(y^(2:ℕ)))*v 108 + (1)*v 140 + ((w)/(y^(2:ℕ)))*v 150 + (1)*v 182,
    (1)*v 28 + ((w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + ((w)/(y^(2:ℕ)))*v 102 + (1)*v 112 + ((w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((w)/(y^(2:ℕ)))*v 186,
    (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180,
    ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 24 + (1)*v 35 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 84 + (1)*v 95 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 204,
    (1)*v 21 + (1)*v 63 + (1)*v 147 + (1)*v 189,
    (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196,
    (1)*v 10 + (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200,
    (2)*v 0 + (2)*v 6 + (1)*v 12 + (1)*v 24 + (2)*v 30 + (2)*v 36 + (1)*v 42 + (1)*v 48 + (2)*v 54 + (1)*v 60 + (1)*v 66 + (1)*v 72 + (1)*v 78 + (2)*v 84 + (2)*v 90 + (2)*v 96 + (1)*v 102 + (1)*v 108 + (2)*v 114 + (2)*v 120 + (2)*v 126 + (1)*v 132 + (1)*v 138 + (1)*v 144 + (1)*v 150 + (2)*v 156 + (1)*v 162 + (1)*v 168 + (2)*v 174 + (2)*v 180 + (1)*v 186 + (1)*v 198 + (2)*v 204,
    (1)*v 2 + (((-1)*a)/(x))*v 4 + ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107,
    (1)*v 5 + (((-1)*a)/(x))*v 10 + ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110,
    (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112,
    (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120,
    (1)*v 20 + (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125,
    (1)*v 30 + (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135,
    (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 + ((1)/(x^(2:ℕ)))*v 180,
    (1)*v 50 + (((-1)*a)/(x))*v 100 + (1)*v 155 + ((1)/(x^(2:ℕ)))*v 200,
    (1)*v 80 + ((1)/(x^(2:ℕ)))*v 110 + (((-1)*a)/(x))*v 160 + (1)*v 185,
    (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 + (((-1)*a)/(x))*v 174 + (1)*v 192,
    (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (((-1)*a)/(x))*v 190 + (1)*v 200,
    (1)*v 7 + (((-1)*b)/(y))*v 21 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147,
    (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150,
    (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (((-1)*b)/(y))*v 99 + (1)*v 103 + (1)*v 173]

def reduced104 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : ℂ :=
  (-5 + (-1)*y*b + (-1)*y^(2:ℕ))*v 24 + ((-2 + (-2)*w + (-4)*z + (-4)*y*b + (-6)*y^(2:ℕ) + (8)*x*a + (-2)*x*z*a + (4)*x*y*a*b + (-2)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ) + (2)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2)*x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-4)*x^(3:ℕ)*a + (2)*x^(3:ℕ)*y*a*b + (-2)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ) + (-2)*x^(4:ℕ)*a^(2:ℕ))/(w))*v 42 + (((-2)*w + (-2)*z + (-2)*y^(2:ℕ) + (4)*x*a + (2)*x*y*a*b + (-2)*x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y^(2:ℕ) + (-6)*x^(3:ℕ)*a + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ) + (-2)*x^(4:ℕ)*y*b + (2)*x^(4:ℕ)*y^(2:ℕ) + (2)*x^(5:ℕ)*a)/(w))*v 84 + (-4 + (-2)*z + (-1)*x^(2:ℕ))*v 192

/-- Exact original-row identity, with only monomial denominators. -/
theorem identity104 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients104 x y z w a b i*sources104 x y z w a b v i)=
      reduced104 x y z w a b v := by
  norm_num [coefficients104,sources104,reduced104,Fin.sum_univ_succ]
  field_simp [hx,hy,hz,hw]
  ring

/-- The exact sparse combination preserves analytic germs. -/
theorem analytic_reduced104 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources104 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced104 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 79) : AnalyticAt ℂ
      (fun t => coefficients104 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · change AnalyticAt ℂ (fun t => ((-1 + (-2)*(W t) + (-1)*(X t)*a)/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2 + (-2)*(X t)*a + (4)*(X t)^(3:ℕ)*a + (4)*(X t)^(4:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((8 + (2)*(W t) + (4)*(Z t) + (-2)*(Z t)*(W t) + (4)*(X t)*a + (X t)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(4:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-3)*(X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)*(Y t)^(4:ℕ)*a)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((4)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-2)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((4)*(Y t)^(2:ℕ) + (-2)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-4)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((Y t)^(2:ℕ) + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(2:ℕ) + (2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(4:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*b)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2 + (-4)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (-2)*(X t)*a + (-2)*(X t)*(Z t)*a + (2)*(X t)*(Y t)*a*b + (-4)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-4)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(Y t)*a*b + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(4:ℕ)*a^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(W t) + (-3)*(Z t) + (-4)*(Y t)*b + (-4)*(Y t)^(2:ℕ) + (6)*(X t)*a + (-2)*(X t)*(Z t)*a + (4)*(X t)*(Y t)*a*b + (-4)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(Y t)*a*b + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ) + (2)*(X t)^(3:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(Y t)^(2:ℕ) + (-2)*(Y t)^(2:ℕ)*(Z t))/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-3 + (-1)*(Z t) + (2)*(X t)*a + (2)*(X t)*(Y t)*a*b + (2)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((1 + (-2)*(X t)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ))/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1 + (-1)*(Z t) + (-2)*(Y t)^(2:ℕ) + (-4)*(X t)*a + (2)*(X t)*(Y t)*a*b + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(Y t)^(2:ℕ))/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((2 + (W t) + (Z t) + (4)*(Y t)*b + (2)*(Y t)^(2:ℕ) + (-6)*(X t)*a + (2)*(X t)*(Z t)*a + (-2)*(X t)*(Y t)*a*b + (2)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (6)*(X t)^(3:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ)*a^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2)*(Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-3 + (-1)*(Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((3)*(Y t)^(2:ℕ) + (Y t)^(3:ℕ)*b + (Y t)^(4:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-2)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a)/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(4:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(Y t)^(2:ℕ) + (-2)*(X t)*(Y t)^(2:ℕ)*a + (4)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((1 + (-1)*(Z t) + (-2)*(Y t)^(2:ℕ) + (-2)*(X t)*a + (2)*(X t)*(Y t)*a*b + (-2)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(2:ℕ)*(Y t)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-2)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((X t)^(2:ℕ)*(Y t)*b)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (2)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-3 + (-1)*(Z t) + (2)*(X t)*a + (2)*(X t)*(Y t)*a*b + (2)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)*(Y t)^(2:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((2 + (W t) + (Z t) + (4)*(Y t)*b + (2)*(Y t)^(2:ℕ) + (-6)*(X t)*a + (2)*(X t)*(Z t)*a + (-2)*(X t)*(Y t)*a*b + (2)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (6)*(X t)^(3:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-1 + (-2)*(W t) + (-1)*(X t)*a)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(Y t)^(2:ℕ) + (-2)*(X t)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(Y t)^(2:ℕ) + (Y t)^(2:ℕ)*(Z t))/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(Y t)^(2:ℕ) + (-2)*(X t)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((1 + (-2)*(W t) + (-1)*(Z t) + (-2)*(Y t)^(2:ℕ) + (4)*(X t)*a + (2)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-2)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((2 + (2)*(Y t)^(2:ℕ) + (-2)*(X t)*(Y t)*a*b + (2)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-2)*(X t)^(4:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(Y t)^(2:ℕ) + (2)*(X t)*(Y t)^(2:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(4:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-4)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(3:ℕ)*(Y t)*a*b + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(4:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-4)*(X t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1)*(X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-4)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((X t)^(2:ℕ)*(Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients104 (X t) (Y t) (Z t) (W t) a b i*
      sources104 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,(hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,(hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity104 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms identity104
#print axioms analytic_reduced104

theorem analytic_reduced13 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources13 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced13 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 85) : AnalyticAt ℂ
      (fun t => coefficients13 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow13Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow13Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients13 (X t) (Y t) (Z t) (W t) a b i*
      sources13 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity13 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced13

theorem analytic_reduced14 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources14 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced14 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 85) : AnalyticAt ℂ
      (fun t => coefficients14 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow14Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow14Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients14 (X t) (Y t) (Z t) (W t) a b i*
      sources14 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity14 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced14

def coefficients150 (x y z w a b : ℂ) : Fin 25 → ℂ :=
  ![((-1)*x^(2:ℕ)),
    ((w)/(z)),
    (x*a),
    ((x^(2:ℕ))/(y^(2:ℕ))),
    (((2)*w + (-1)*y*w*b + (-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z)),
    ((2 + (-1)*y*b + (-1)*y^(2:ℕ) + x*a + (-1)*x^(2:ℕ))/(y^(2:ℕ))),
    ((x^(2:ℕ)*w)/(y^(2:ℕ)*z)),
    ((w + (-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z)),
    ((1 + (-1)*x*a + (-1)*x^(2:ℕ))/(y^(2:ℕ))),
    ((w)/(y^(2:ℕ)*z)),
    ((1 + (-1)*x*a + (-1)*x^(2:ℕ))/(y^(2:ℕ))),
    ((y*w*b + y^(2:ℕ)*w + (-1)*x*w*a)/(y^(2:ℕ)*z)),
    ((w + (-1)*x*w*a + (-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z)),
    (1 + (-1)*x^(2:ℕ)),
    ((w + (-1)*x*w*a + (-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z)),
    (1),
    ((y*b + y^(2:ℕ) + (-1)*x*a)/(y^(2:ℕ))),
    ((w)/(z)),
    ((-2 + (-1)*y^(2:ℕ) + x*a + x^(2:ℕ))/(y^(2:ℕ))),
    (((-1)*w + x^(2:ℕ)*w)/(y^(2:ℕ)*z)),
    (-1),
    (x^(2:ℕ)),
    (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z)),
    (((-1)*w)/(z)),
    (1)]

def sources150 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Fin 25 → ℂ :=
  ![(1)*v 7 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30,
    (1)*v 10 + ((z)/(y^(2:ℕ)*w))*v 84,
    (1)*v 14 + ((w)/(y^(2:ℕ)*z))*v 120,
    (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150,
    (1)*v 30 + ((z)/(w))*v 168,
    (1)*v 42 + ((w)/(z))*v 180,
    (1)*v 45 + ((y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182,
    (1)*v 60 + ((x^(2:ℕ)*z)/(w))*v 189,
    (1)*v 84 + ((x^(2:ℕ)*w)/(z))*v 195,
    (1)*v 90 + ((y^(2:ℕ)*z)/(w))*v 196,
    (1)*v 126 + ((y^(2:ℕ)*w)/(z))*v 200,
    (1)*v 180 + ((x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203,
    (1)*v 90 + ((-1)*y^(2:ℕ))*v 200,
    (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189,
    (1)*v 120 + ((-1)*x^(2:ℕ))*v 195,
    (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98,
    (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203,
    ((z)/(w))*v 56 + (1)*v 80 + ((z)/(w))*v 126 + (1)*v 150,
    (1)*v 42 + (1)*v 84 + (1)*v 126 + (1)*v 168,
    (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180,
    (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196,
    (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112,
    (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 + ((1)/(x^(2:ℕ)))*v 180,
    (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150,
    (1)*v 14 + (((-1)*b)/(y))*v 42 + (1)*v 84 + ((1)/(y^(2:ℕ)))*v 126 + (1)*v 154]

def reduced150 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : ℂ :=
  (((-2)*y*b + (-2)*y^(2:ℕ) + (2)*x*a)/(y^(2:ℕ)))*v 42

/-- Exact original-row identity, with only monomial denominators. -/
theorem identity150 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients150 x y z w a b i*sources150 x y z w a b v i)=
      reduced150 x y z w a b v := by
  norm_num [coefficients150,sources150,reduced150,Fin.sum_univ_succ]
  field_simp [hx,hy,hz,hw]
  ring

/-- The exact sparse combination preserves analytic germs. -/
theorem analytic_reduced150 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources150 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced150 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 25) : AnalyticAt ℂ
      (fun t => coefficients150 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · change AnalyticAt ℂ (fun t => ((-1)*(X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((X t)*a)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ))/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(W t) + (-1)*(Y t)*(W t)*b + (-1)*(X t)^(2:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((2 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (X t)*a + (-1)*(X t)^(2:ℕ))/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t) + (-1)*(X t)^(2:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((1 + (-1)*(X t)*a + (-1)*(X t)^(2:ℕ))/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((1 + (-1)*(X t)*a + (-1)*(X t)^(2:ℕ))/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((Y t)*(W t)*b + (Y t)^(2:ℕ)*(W t) + (-1)*(X t)*(W t)*a)/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t) + (-1)*(X t)*(W t)*a + (-1)*(X t)^(2:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1 + (-1)*(X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t) + (-1)*(X t)*(W t)*a + (-1)*(X t)^(2:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((Y t)*b + (Y t)^(2:ℕ) + (-1)*(X t)*a)/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2 + (-1)*(Y t)^(2:ℕ) + (X t)*a + (X t)^(2:ℕ))/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(W t) + (X t)^(2:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients150 (X t) (Y t) (Z t) (W t) a b i*
      sources150 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,(hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,(hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity150 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms identity150
#print axioms analytic_reduced150

def coefficients159 (x y z w a b : ℂ) : Fin 20 → ℂ :=
  ![(x^(2:ℕ)),
    ((-1)*x*a),
    ((x^(2:ℕ)*w + x^(4:ℕ)*w)/(y^(2:ℕ)*z)),
    (((-1)*x^(2:ℕ))/(y^(2:ℕ))),
    (((-2)*w + (-1)*x*w*a + (-1)*x^(3:ℕ)*w*a)/(y^(2:ℕ)*z)),
    ((-3 + y^(2:ℕ) + (-1)*x*a + (-1)*x^(2:ℕ) + (-1)*x^(3:ℕ)*a)/(y^(2:ℕ))),
    ((x^(2:ℕ)*w)/(y^(2:ℕ)*z)),
    ((-1 + x*a + x^(2:ℕ) + x^(4:ℕ))/(y^(2:ℕ))),
    ((-1)/(y^(2:ℕ))),
    (((2)*w + (-1)*y^(2:ℕ)*w + x*w*a + x^(2:ℕ)*w + x^(3:ℕ)*w*a)/(y^(2:ℕ)*z)),
    (((-1)*w)/(y^(2:ℕ)*z)),
    (x^(2:ℕ)),
    (((-1)*w + x*w*a + x^(2:ℕ)*w + x^(4:ℕ)*w)/(y^(2:ℕ)*z)),
    (-1),
    ((2 + (-1)*y^(2:ℕ) + x*a + x^(2:ℕ) + x^(3:ℕ)*a)/(y^(2:ℕ))),
    (((-1)*x^(2:ℕ))/(y^(2:ℕ))),
    ((w)/(y^(2:ℕ)*z)),
    ((-1)*x^(2:ℕ)),
    (((-1)*x^(2:ℕ)*w + (-1)*x^(4:ℕ)*w)/(y^(2:ℕ)*z)),
    (1)]

def sources159 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Fin 20 → ℂ :=
  ![(1)*v 7 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30,
    (1)*v 14 + ((w)/(y^(2:ℕ)*z))*v 120,
    (1)*v 15 + ((z)/(x^(2:ℕ)*w))*v 126,
    (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150,
    (1)*v 30 + ((z)/(w))*v 168,
    (1)*v 42 + ((w)/(z))*v 180,
    (1)*v 60 + ((x^(2:ℕ)*z)/(w))*v 189,
    (1)*v 84 + ((x^(2:ℕ)*w)/(z))*v 195,
    (1)*v 126 + ((y^(2:ℕ)*w)/(z))*v 200,
    (1)*v 180 + ((x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203,
    (1)*v 90 + ((-1)*y^(2:ℕ))*v 200,
    (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189,
    (1)*v 120 + ((-1)*x^(2:ℕ))*v 195,
    (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98,
    (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203,
    (1)*v 42 + (1)*v 84 + (1)*v 126 + (1)*v 168,
    (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180,
    (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112,
    (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120,
    (1)*v 28 + ((1)/(y^(2:ℕ)))*v 42 + (((-1)*b)/(y))*v 84 + (1)*v 98 + (1)*v 168]

def reduced159 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : ℂ :=
  ((-2 + y^(2:ℕ) + (-1)*x*a + (-2)*x^(2:ℕ) + (-1)*x^(3:ℕ)*a)/(y^(2:ℕ)))*v 42 + ((-1 + (-1)*y*b + x*a + x^(4:ℕ))/(y^(2:ℕ)))*v 84

/-- Exact original-row identity, with only monomial denominators. -/
theorem identity159 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients159 x y z w a b i*sources159 x y z w a b v i)=
      reduced159 x y z w a b v := by
  norm_num [coefficients159,sources159,reduced159,Fin.sum_univ_succ]
  field_simp [hx,hy,hz,hw]
  ring

/-- The exact sparse combination preserves analytic germs. -/
theorem analytic_reduced159 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources159 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced159 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 20) : AnalyticAt ℂ
      (fun t => coefficients159 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · change AnalyticAt ℂ (fun t => ((X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1)*(X t)*a)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(W t) + (X t)^(4:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ))/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(W t) + (-1)*(X t)*(W t)*a + (-1)*(X t)^(3:ℕ)*(W t)*a)/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-3 + (Y t)^(2:ℕ) + (-1)*(X t)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1 + (X t)*a + (X t)^(2:ℕ) + (X t)^(4:ℕ))/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1)/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(W t) + (-1)*(Y t)^(2:ℕ)*(W t) + (X t)*(W t)*a + (X t)^(2:ℕ)*(W t) + (X t)^(3:ℕ)*(W t)*a)/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(W t) + (X t)*(W t)*a + (X t)^(2:ℕ)*(W t) + (X t)^(4:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((2 + (-1)*(Y t)^(2:ℕ) + (X t)*a + (X t)^(2:ℕ) + (X t)^(3:ℕ)*a)/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ))/((Y t)^(2:ℕ)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1)*(X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(W t))/((Y t)^(2:ℕ)*(Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients159 (X t) (Y t) (Z t) (W t) a b i*
      sources159 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,(hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,(hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity159 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms identity159
#print axioms analytic_reduced159

theorem analytic_reduced163 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources163 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced163 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 94) : AnalyticAt ℂ
      (fun t => coefficients163 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow163Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight85_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight86_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight87_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight88_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight89_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight90_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight91_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight92_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow163Weight93_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients163 (X t) (Y t) (Z t) (W t) a b i*
      sources163 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity163 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced163

theorem analytic_reduced164 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources164 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced164 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 86) : AnalyticAt ℂ
      (fun t => coefficients164 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow164Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow164Weight85_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients164 (X t) (Y t) (Z t) (W t) a b i*
      sources164 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity164 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced164

theorem analytic_reduced16 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources16 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced16 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 93) : AnalyticAt ℂ
      (fun t => coefficients16 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow16Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight85_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight86_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight87_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight88_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight89_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight90_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight91_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow16Weight92_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients16 (X t) (Y t) (Z t) (W t) a b i*
      sources16 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity16 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced16

theorem analytic_reduced19 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources19 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced19 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 93) : AnalyticAt ℂ
      (fun t => coefficients19 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow19Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight85_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight86_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight87_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight88_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight89_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight90_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight91_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow19Weight92_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients19 (X t) (Y t) (Z t) (W t) a b i*
      sources19 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity19 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced19

theorem analytic_reduced21 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources21 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced21 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 93) : AnalyticAt ℂ
      (fun t => coefficients21 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow21Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight85_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight86_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight87_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight88_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight89_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight90_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight91_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow21Weight92_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients21 (X t) (Y t) (Z t) (W t) a b i*
      sources21 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity21 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced21

theorem analytic_reduced26 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources26 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced26 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 93) : AnalyticAt ℂ
      (fun t => coefficients26 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow26Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight85_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight86_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight87_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight88_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight89_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight90_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight91_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow26Weight92_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients26 (X t) (Y t) (Z t) (W t) a b i*
      sources26 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity26 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced26

theorem analytic_reduced3 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources3 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced3 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 75) : AnalyticAt ℂ
      (fun t => coefficients3 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow3Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow3Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients3 (X t) (Y t) (Z t) (W t) a b i*
      sources3 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity3 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced3

def coefficients45 (x y z w a b : ℂ) : Fin 26 → ℂ :=
  ![((1)/(z)),
    ((-1 + (-1)*z)/(z)),
    ((y^(2:ℕ)*w)/(z)),
    (((-1)*x^(2:ℕ)*w + x^(4:ℕ)*w)/(z)),
    (x^(2:ℕ)),
    ((w + (-1)*y*w*b + x*w*a + (-1)*x^(2:ℕ)*w + (-1)*x^(3:ℕ)*w*a)/(z)),
    (2 + (-1)*y*b + (-1)*y^(2:ℕ) + (2)*x*a + (-2)*x^(2:ℕ) + (-1)*x^(3:ℕ)*a),
    ((x^(2:ℕ)*w)/(z)),
    ((-1)*y^(2:ℕ)),
    (1 + (-2)*x^(2:ℕ) + x^(4:ℕ)),
    (2 + (-1)*x*a + (-1)*x^(2:ℕ)),
    ((y*w*b + y^(2:ℕ)*w + (-2)*x*w*a + x^(2:ℕ)*w + x^(3:ℕ)*w*a)/(z)),
    (w),
    (((2)*w + (-1)*x*w*a + (-1)*x^(2:ℕ)*w)/(z)),
    ((w + (-2)*x^(2:ℕ)*w + x^(4:ℕ)*w)/(z)),
    (y^(2:ℕ)),
    (y*b + y^(2:ℕ) + (-2)*x*a + x^(2:ℕ) + x^(3:ℕ)*a),
    (y^(2:ℕ)),
    ((y^(2:ℕ)*w)/(z)),
    (-2 + (-1)*y^(2:ℕ) + x*a),
    ((-1)*y^(2:ℕ)),
    (((-1)*w + x^(2:ℕ)*w)/(z)),
    (1),
    ((x^(2:ℕ)*w + (-1)*x^(4:ℕ)*w)/(z)),
    (((-1)*x^(2:ℕ)*w)/(z)),
    (((-1)*y^(2:ℕ)*w)/(z))]

def sources45 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Fin 26 → ℂ :=
  ![(1)*v 0 + (x^(2:ℕ)*z*w)*v 207,
    (1)*v 0,
    (1)*v 10 + ((z)/(y^(2:ℕ)*w))*v 84,
    (1)*v 15 + ((z)/(x^(2:ℕ)*w))*v 126,
    (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150,
    (1)*v 30 + ((z)/(w))*v 168,
    (1)*v 42 + ((w)/(z))*v 180,
    (1)*v 45 + ((y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182,
    (1)*v 70 + ((z*w)/(y^(2:ℕ)))*v 192,
    (1)*v 84 + ((x^(2:ℕ)*w)/(z))*v 195,
    (1)*v 126 + ((y^(2:ℕ)*w)/(z))*v 200,
    (1)*v 180 + ((x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203,
    (1)*v 108 + ((-1)*x^(2:ℕ))*v 207,
    (1)*v 90 + ((-1)*y^(2:ℕ))*v 200,
    (1)*v 120 + ((-1)*x^(2:ℕ))*v 195,
    (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98,
    (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203,
    (1)*v 70 + (1)*v 140,
    ((z)/(w))*v 56 + (1)*v 80 + ((z)/(w))*v 126 + (1)*v 150,
    (1)*v 42 + (1)*v 84 + (1)*v 126 + (1)*v 168,
    ((w)/(y^(2:ℕ)))*v 24 + (1)*v 56 + ((w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + ((w)/(y^(2:ℕ)))*v 108 + (1)*v 140 + ((w)/(y^(2:ℕ)))*v 150 + (1)*v 182,
    (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180,
    (1)*v 0 + (w)*v 24 + (1)*v 42 + (w)*v 66 + (1)*v 126 + (w)*v 150 + (1)*v 168 + (w)*v 192,
    (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120,
    (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 + ((1)/(x^(2:ℕ)))*v 180,
    (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150]

def reduced45 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : ℂ :=
  (1 + (-1)*y*b + (-2)*y^(2:ℕ) + (3)*x*a + (-2)*x^(2:ℕ) + (-1)*x^(3:ℕ)*a)*v 42 + ((-1)*y^(2:ℕ) + x*a + (-2)*x^(2:ℕ) + x^(4:ℕ))*v 84 + (w + (-1)*z*w)*v 192

/-- Exact original-row identity, with only monomial denominators. -/
theorem identity45 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients45 x y z w a b i*sources45 x y z w a b v i)=
      reduced45 x y z w a b v := by
  norm_num [coefficients45,sources45,reduced45,Fin.sum_univ_succ]
  field_simp [hx,hy,hz,hw]
  ring

/-- The exact sparse combination preserves analytic germs. -/
theorem analytic_reduced45 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources45 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced45 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 26) : AnalyticAt ℂ
      (fun t => coefficients45 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · change AnalyticAt ℂ (fun t => ((1)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1 + (-1)*(Z t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((Y t)^(2:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ)*(W t) + (X t)^(4:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t) + (-1)*(Y t)*(W t)*b + (X t)*(W t)*a + (-1)*(X t)^(2:ℕ)*(W t) + (-1)*(X t)^(3:ℕ)*(W t)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (2 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (2)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1)*(Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1 + (-2)*(X t)^(2:ℕ) + (X t)^(4:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (2 + (-1)*(X t)*a + (-1)*(X t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((Y t)*(W t)*b + (Y t)^(2:ℕ)*(W t) + (-2)*(X t)*(W t)*a + (X t)^(2:ℕ)*(W t) + (X t)^(3:ℕ)*(W t)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((W t))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(W t) + (-1)*(X t)*(W t)*a + (-1)*(X t)^(2:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((W t) + (-2)*(X t)^(2:ℕ)*(W t) + (X t)^(4:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((Y t)*b + (Y t)^(2:ℕ) + (-2)*(X t)*a + (X t)^(2:ℕ) + (X t)^(3:ℕ)*a)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((Y t)^(2:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-2 + (-1)*(Y t)^(2:ℕ) + (X t)*a)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1)*(Y t)^(2:ℕ))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(W t) + (X t)^(2:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(Y t)^(2:ℕ)*(W t))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients45 (X t) (Y t) (Z t) (W t) a b i*
      sources45 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,(hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,(hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity45 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms identity45
#print axioms analytic_reduced45

def coefficients53 (x y z w a b : ℂ) : Fin 51 → ℂ :=
  ![((-1 + (-1)*w)/(z*w)),
    (((-1)*x*a + (-2)*x^(2:ℕ) + (2)*x^(3:ℕ)*a + (2)*x^(4:ℕ))/(w)),
    ((1 + w)/(z*w)),
    (((-2)*x^(2:ℕ)*y^(2:ℕ) + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (2)*x^(4:ℕ)*y^(2:ℕ))/(z)),
    ((x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(4:ℕ)*y^(2:ℕ))/(w)),
    ((x*y^(2:ℕ)*a + x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2)*x^(3:ℕ)*y^(2:ℕ)*a)/(z)),
    (((-1)*x*y^(2:ℕ)*a + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ))/(w)),
    ((x^(2:ℕ) + x^(2:ℕ)*y*b + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ)*y*b + x^(4:ℕ)*y^(2:ℕ) + x^(5:ℕ)*a)/(z)),
    (((-1)*y^(2:ℕ) + x*y^(2:ℕ)*a + x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-2)*x^(2:ℕ) + (-1)*x^(2:ℕ)*y*b + x^(3:ℕ)*y*a*b + x^(4:ℕ) + x^(4:ℕ)*y*b)/(w)),
    ((-2 + (-1)*y*b + (-1)*x*a + (-1)*x*y^(2:ℕ)*a + (2)*x^(2:ℕ) + x^(2:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1)*x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ)*a^(2:ℕ))/(z)),
    ((x^(2:ℕ)*y^(2:ℕ))/(z)),
    ((-5 + (-2)*y*b + y^(2:ℕ) + x*a + x*y*a*b + (-1)*x*y^(2:ℕ)*a + (4)*x^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1)*x^(3:ℕ)*a + x^(3:ℕ)*y*a*b + (-1)*x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ)*a^(2:ℕ))/(w)),
    (((-1)*x^(3:ℕ)*a)/(z)),
    ((-1 + x^(2:ℕ) + x^(3:ℕ)*a)/(z)),
    (((-1)*y^(2:ℕ))/(z)),
    ((-2 + (-1)*y*b + x*a + x*y*a*b + (2)*x^(2:ℕ) + x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*y*b + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ)*y*b + x^(4:ℕ)*y^(2:ℕ) + x^(5:ℕ)*a)/(w)),
    (((-1)*x*a)/(z)),
    ((-2 + (-1)*y*b + x*y*a*b + (-1)*x*y^(2:ℕ)*a + x^(2:ℕ) + x^(2:ℕ)*y*b + (-1)*x^(2:ℕ)*y^(2:ℕ))/(w)),
    ((3 + y*b + (-1)*y^(2:ℕ) + (-1)*x*a + (-3)*x^(2:ℕ) + (-1)*x^(2:ℕ)*y*a^(2:ℕ)*b + x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*a + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*a^(2:ℕ))/(z)),
    (((-1)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ)*y^(2:ℕ) + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (2)*x^(4:ℕ)*y^(2:ℕ))/(z)),
    ((-2 + (-1)*y*b + x*a + x*y*a*b + (-1)*x*y^(2:ℕ)*a + (2)*x^(2:ℕ) + x^(2:ℕ)*y*b + (-1)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-1)*x*y^(2:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a)/(w)),
    (1),
    ((-2 + (-1)*y*b + x*a + x*y*a*b + (2)*x^(2:ℕ) + x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*y*b + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ)*y*b + x^(4:ℕ)*y^(2:ℕ) + x^(5:ℕ)*a)/(z)),
    (((-1)*y^(2:ℕ) + (-1)*x*y^(2:ℕ)*a)/(w)),
    ((y^(2:ℕ))/(z)),
    ((3 + y*b + (-1)*y^(2:ℕ) + (-1)*x*a + (-3)*x^(2:ℕ) + (-1)*x^(2:ℕ)*y*a^(2:ℕ)*b + x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*a + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*a^(2:ℕ))/(w)),
    (-1 + (-1)*w),
    (((-1)*x*y^(2:ℕ)*a)/(z)),
    ((x^(2:ℕ)*y^(2:ℕ))/(z)),
    ((x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ)*y^(2:ℕ))/(w)),
    (((-1)*x*y^(2:ℕ)*a)/(z)),
    (((-1)*x*y^(2:ℕ)*a)/(z)),
    ((1 + x*y^(2:ℕ)*a + (-1)*x^(2:ℕ) + (-1)*x^(3:ℕ)*a)/(w)),
    ((2 + y*b + (-1)*x*y*a*b + x*y^(2:ℕ)*a + (-1)*x^(2:ℕ) + (-1)*x^(2:ℕ)*y*b + x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-1)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    ((x^(2:ℕ) + (-1)*x^(3:ℕ)*a + (-1)*x^(4:ℕ))/(w)),
    (1),
    ((x*y^(2:ℕ)*a)/(w)),
    (((-1)*y^(2:ℕ) + x*y^(2:ℕ)*a)/(z)),
    (((2)*x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(3:ℕ)*y^(2:ℕ)*a + (-2)*x^(4:ℕ)*y^(2:ℕ))/(z)),
    (((-1)*x^(3:ℕ)*y^(2:ℕ)*a)/(w)),
    (((-1)*x^(2:ℕ) + (-1)*x^(2:ℕ)*y*b + x^(3:ℕ)*y*a*b + (-1)*x^(3:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y*b + (-1)*x^(4:ℕ)*y^(2:ℕ) + (-1)*x^(5:ℕ)*a)/(z)),
    ((x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-1)*x^(2:ℕ)*y^(2:ℕ))/(z)),
    ((x^(2:ℕ)*y^(2:ℕ))/(z)),
    ((x^(2:ℕ)*y^(2:ℕ))/(z)),
    ((x^(2:ℕ)*y^(2:ℕ))/(z)),
    (((-1)*x^(2:ℕ)*y^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y^(2:ℕ))/(w)),
    (((-1)*x^(2:ℕ)*y^(2:ℕ))/(z))]

def sources53 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Fin 51 → ℂ :=
  ![(1)*v 0 + (z*w)*v 204,
    (1)*v 42 + ((x^(2:ℕ)*y^(2:ℕ)*w)/(z))*v 205,
    (1)*v 0,
    (1)*v 5 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168,
    (1)*v 7 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30,
    (1)*v 10 + ((z)/(y^(2:ℕ)*w))*v 84,
    (1)*v 14 + ((w)/(y^(2:ℕ)*z))*v 120,
    (1)*v 15 + ((z)/(x^(2:ℕ)*w))*v 126,
    (1)*v 20 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147,
    (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150,
    (1)*v 30 + ((z)/(w))*v 168,
    (1)*v 35 + ((z*w)/(x^(2:ℕ)*y^(2:ℕ)))*v 174,
    (1)*v 42 + ((w)/(z))*v 180,
    (1)*v 45 + ((y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182,
    (1)*v 60 + ((x^(2:ℕ)*z)/(w))*v 189,
    (1)*v 70 + ((z*w)/(y^(2:ℕ)))*v 192,
    (1)*v 84 + ((x^(2:ℕ)*w)/(z))*v 195,
    (1)*v 90 + ((y^(2:ℕ)*z)/(w))*v 196,
    (1)*v 126 + ((y^(2:ℕ)*w)/(z))*v 200,
    (1)*v 180 + ((x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203,
    (1)*v 110 + ((-1)*x^(2:ℕ))*v 205,
    (1)*v 90 + ((-1)*y^(2:ℕ))*v 200,
    (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189,
    (1)*v 114 + (-1)*v 192,
    (1)*v 120 + ((-1)*x^(2:ℕ))*v 195,
    (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98,
    ((-1)/(y^(2:ℕ)))*v 30 + (1)*v 100,
    (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203,
    (1)*v 174 + (-1)*v 204,
    (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170,
    (1)*v 65 + ((z)/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + ((z)/(x^(2:ℕ)*w))*v 168,
    ((w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + ((w)/(x^(2:ℕ)*z))*v 120 + (1)*v 147,
    ((z)/(w))*v 56 + (1)*v 80 + ((z)/(w))*v 126 + (1)*v 150,
    (1)*v 60 + ((z)/(w))*v 84 + (1)*v 130 + ((z)/(w))*v 154,
    (1)*v 42 + (1)*v 84 + (1)*v 126 + (1)*v 168,
    (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180,
    ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 24 + (1)*v 35 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 84 + (1)*v 95 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 204,
    (1)*v 21 + (1)*v 63 + (1)*v 147 + (1)*v 189,
    ((y^(2:ℕ))/(z))*v 10 + (1)*v 24 + ((y^(2:ℕ))/(z))*v 40 + (1)*v 54 + ((y^(2:ℕ))/(z))*v 70 + (1)*v 84 + ((y^(2:ℕ))/(z))*v 130 + (1)*v 144 + ((y^(2:ℕ))/(z))*v 160 + (1)*v 174 + ((y^(2:ℕ))/(z))*v 190 + (1)*v 204,
    (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196,
    (1)*v 10 + (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200,
    (1)*v 5 + (((-1)*a)/(x))*v 10 + ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110,
    (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112,
    (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120,
    (1)*v 20 + (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125,
    (1)*v 30 + (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135,
    (1)*v 50 + (((-1)*a)/(x))*v 100 + (1)*v 155 + ((1)/(x^(2:ℕ)))*v 200,
    (1)*v 80 + ((1)/(x^(2:ℕ)))*v 110 + (((-1)*a)/(x))*v 160 + (1)*v 185,
    (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (((-1)*a)/(x))*v 190 + (1)*v 200,
    (1)*v 7 + (((-1)*b)/(y))*v 21 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147,
    (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150]

def reduced53 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : ℂ :=
  ((-4 + (-2)*y*b + y^(2:ℕ) + x*y*a*b + x^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1)*x^(3:ℕ)*y^(2:ℕ)*a + (2)*x^(4:ℕ) + (-1)*x^(4:ℕ)*a^(2:ℕ))/(w))*v 42 + ((-1 + (-1)*y*b + (2)*x*a + x*y*a*b + (2)*x^(2:ℕ) + (-1)*x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*y*b + (-3)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ)*y*b + x^(4:ℕ)*y^(2:ℕ) + x^(5:ℕ)*a)/(w))*v 84 + (-1 + (-1)*w)*v 192

/-- Exact original-row identity, with only monomial denominators. -/
theorem identity53 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (v : Fin 210 → ℂ) :
    (∑ i, coefficients53 x y z w a b i*sources53 x y z w a b v i)=
      reduced53 x y z w a b v := by
  norm_num [coefficients53,sources53,reduced53,Fin.sum_univ_succ]
  field_simp [hx,hy,hz,hw]
  ring

/-- The exact sparse combination preserves analytic germs. -/
theorem analytic_reduced53 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources53 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced53 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 51) : AnalyticAt ℂ
      (fun t => coefficients53 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · change AnalyticAt ℂ (fun t => ((-1 + (-1)*(W t))/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(3:ℕ)*a + (2)*(X t)^(4:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((1 + (W t))/((Z t)*(W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(5:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(Y t)^(2:ℕ) + (X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-2)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (X t)^(3:ℕ)*(Y t)*a*b + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Y t)*b)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2 + (-1)*(Y t)*b + (-1)*(X t)*a + (-1)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*a^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-5 + (-2)*(Y t)*b + (Y t)^(2:ℕ) + (X t)*a + (X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (4)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(3:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-1 + (X t)^(2:ℕ) + (X t)^(3:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2 + (-1)*(Y t)*b + (X t)*a + (X t)*(Y t)*a*b + (2)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(5:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2 + (-1)*(Y t)*b + (X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((3 + (Y t)*b + (-1)*(Y t)^(2:ℕ) + (-1)*(X t)*a + (-3)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ)*a^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2 + (-1)*(Y t)*b + (X t)*a + (X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (2)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)*(Y t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((-2 + (-1)*(Y t)*b + (X t)*a + (X t)*(Y t)*a*b + (2)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(5:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(Y t)^(2:ℕ) + (-1)*(X t)*(Y t)^(2:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((3 + (Y t)*b + (-1)*(Y t)^(2:ℕ) + (-1)*(X t)*a + (-3)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (-1 + (-1)*(W t))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((1 + (X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => ((2 + (Y t)*b + (-1)*(X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(4:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (1)) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)*(Y t)^(2:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(Y t)^(2:ℕ) + (X t)*(Y t)^(2:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a)/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ)*(Y t)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a)/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ)*(Y t)^(2:ℕ))/((W t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
    · change AnalyticAt ℂ (fun t => (((-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ))/((Z t)))) s
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients53 (X t) (Y t) (Z t) (W t) a b i*
      sources53 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,(hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,(hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity53 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms identity53
#print axioms analytic_reduced53

theorem analytic_reduced9 (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ)
    (h : ∀ i, HasAnalyticGerm (fun t => sources9 (X t) (Y t) (Z t) (W t) a b (G t) i) s) :
    HasAnalyticGerm (fun t => reduced9 (X t) (Y t) (Z t) (W t) a b (G t)) s := by
  have hc (i : Fin 95) : AnalyticAt ℂ
      (fun t => coefficients9 (X t) (Y t) (Z t) (W t) a b i) s := by
    fin_cases i
    · exact closedRow9Weight0_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight1_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight2_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight3_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight4_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight5_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight6_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight7_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight8_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight9_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight10_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight11_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight12_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight13_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight14_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight15_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight16_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight17_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight18_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight19_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight20_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight21_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight22_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight23_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight24_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight25_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight26_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight27_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight28_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight29_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight30_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight31_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight32_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight33_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight34_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight35_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight36_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight37_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight38_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight39_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight40_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight41_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight42_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight43_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight44_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight45_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight46_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight47_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight48_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight49_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight50_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight51_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight52_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight53_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight54_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight55_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight56_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight57_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight58_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight59_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight60_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight61_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight62_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight63_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight64_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight65_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight66_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight67_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight68_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight69_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight70_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight71_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight72_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight73_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight74_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight75_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight76_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight77_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight78_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight79_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight80_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight81_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight82_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight83_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight84_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight85_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight86_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight87_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight88_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight89_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight90_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight91_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight92_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight93_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
    · exact closedRow9Weight94_analytic X Y Z W a b s hx hy hz hw hx0 hy0 hz0 hw0
  have he := HasAnalyticGerm.sum
    (fun i t => coefficients9 (X t) (Y t) (Z t) (W t) a b i*
      sources9 (X t) (Y t) (Z t) (W t) a b (G t) i) s
    (fun i => (h i).mul_analytic (hc i))
  apply he.congr
  filter_upwards [(hx.continuousAt.eventually_ne hx0).filter_mono nhdsWithin_le_nhds,
    (hy.continuousAt.eventually_ne hy0).filter_mono nhdsWithin_le_nhds,
    (hz.continuousAt.eventually_ne hz0).filter_mono nhdsWithin_le_nhds,
    (hw.continuousAt.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with t hxt hyt hzt hwt
  exact identity9 (X t) (Y t) (Z t) (W t) a b hxt hyt hzt hwt (G t)

#print axioms analytic_reduced9

end QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
end
end
