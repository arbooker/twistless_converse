module
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Tactic
public import QuantitativeArithmeticSmallLevelNineteenGenericJetIndexWeightsCaseIndexSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet109
theorem weights_analytic0 (X Y Z : ℂ→ℂ) (a b s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s) (hZ : AnalyticAt ℂ Z s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (ha : a≠0) (i : Fin 103) :
    AnalyticAt ℂ (fun t => weights0 (X t) (Y t) (Z t) a b i) s := by
  fin_cases i
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ) + (-36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(5:ℕ) + (-576:ℂ)*(X t)^(2:ℕ)*a + (-576:ℂ)*(X t)*a^(2:ℕ) + (-576:ℂ)*(X t) + (-1152:ℂ)*a)/((32:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (3:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-9:ℂ)*(X t)^(4:ℕ) + (-2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (6:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-18:ℂ)*(X t)^(3:ℕ)*a + (-4:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (24:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(2:ℕ) + (24:ℂ)*(X t)*(Y t)*a*b + (48:ℂ)*(Y t)*b)/((2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ) + (-36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(5:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (144:ℂ)*(X t)^(3:ℕ) + (-32:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (-288:ℂ)*(X t)^(2:ℕ)*a + (-64:ℂ)*(X t)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t)*a^(2:ℕ) + (-1152:ℂ)*a)/((32:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (2:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-12:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (54:ℂ)*(X t)^(6:ℕ) + (-12:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-180:ℂ)*(X t)^(5:ℕ)*a + (8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (24:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-96:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (144:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (48:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1008:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-192:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-576:ℂ)*(X t)^(2:ℕ) + (-1728:ℂ)*(X t)*a + (1152:ℂ))/((4:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (-36:ℂ)*(X t)*a + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((72:ℂ)*(X t)^(2:ℕ) + (144:ℂ)*(X t)*a + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(3:ℕ)*a + (18:ℂ)*(X t)^(2:ℕ) + (-36:ℂ)*(X t)*a^(3:ℕ) + (72:ℂ)*(X t)*a + (-72:ℂ)*a^(2:ℕ) + (72:ℂ))/((4:ℂ)*(X t)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ)*a + (-18:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (72:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ) + (-432:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-576:ℂ)*(X t)^(2:ℕ) + (-576:ℂ)*(X t)*a + (1152:ℂ))/((4:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(3:ℕ)*a + (-18:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-18:ℂ)*(X t)^(2:ℕ) + (-72:ℂ)*(X t)*a + (-72:ℂ))/((4:ℂ)*(X t)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(2:ℕ)*(Y t) + (3:ℂ)*(X t)^(2:ℕ)*b + (-2:ℂ)*(X t)*(Y t)*a + (6:ℂ)*(X t)*a*b + (-4:ℂ)*(Y t) + (12:ℂ)*b)/((2:ℂ)*(X t)*(Y t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(7:ℕ) + (18:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(6:ℕ)*a + (-12:ℂ)*(X t)^(5:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(5:ℕ) + (-24:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(4:ℕ)*a + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(3:ℕ) + (288:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-1440:ℂ)*(X t)^(2:ℕ)*a + (-64:ℂ)*(X t)*(Y t)^(2:ℕ) + (-192:ℂ)*(X t)*(Y t)*b + (-1152:ℂ)*(X t) + (-2304:ℂ)*a)/((8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(7:ℕ) + (-4:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(5:ℕ) + (16:ℂ)*(X t)^(3:ℕ) + (-32:ℂ)*(X t)^(2:ℕ)*a + (-64:ℂ)*(X t)*a^(2:ℕ) + (-128:ℂ)*a)/((8:ℂ)*(X t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(5:ℕ)*a + (2:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (4:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ) + (-16:ℂ)*(X t)*a + (-32:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(2:ℕ) + (-2:ℂ)*(X t)*a + (-4:ℂ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(4:ℕ) + (36:ℂ)*(X t)^(3:ℕ)*a + (36:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(2:ℕ) + (-72:ℂ)*(X t)*a + (-288:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (-36:ℂ)*(X t)*a + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(2:ℕ) + (18:ℂ)*(X t)*a + (36:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (-2:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ) + (-8:ℂ)*(X t)*a + (-16:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(4:ℕ) + (-4:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(2:ℕ) + (16:ℂ))/((8:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(4:ℕ) + (18:ℂ)*(X t)^(3:ℕ)*a + (72:ℂ)*(X t)^(2:ℕ) + (72:ℂ)*(X t)*a + (144:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(5:ℕ)*a + (2:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (4:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ) + (-16:ℂ)*(X t)*a + (-32:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(3:ℕ)*a + (2:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*(X t)^(2:ℕ) + (-8:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (-36:ℂ)*(X t)*a + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(3:ℕ) + (4:ℂ)*(X t)*a^(2:ℕ) + (-4:ℂ)*(X t) + (8:ℂ)*a)/((8:ℂ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*(X t)^(2:ℕ) + (-4:ℂ)*(X t)*a + (-8:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(7:ℕ) + (-4:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(5:ℕ) + (16:ℂ)*(X t)^(3:ℕ) + (-32:ℂ)*(X t)^(2:ℕ)*a + (-64:ℂ)*(X t)*a^(2:ℕ) + (-128:ℂ)*a)/((8:ℂ)*(X t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (-12:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ) + (-24:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-96:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-432:ℂ)*(X t)^(4:ℕ) + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1728:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-192:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-1152:ℂ)*(X t)^(2:ℕ) + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ)*a + (-18:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(6:ℕ) + (8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(2:ℕ) + (-576:ℂ)*(X t)*a + (1152:ℂ))/((4:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(3:ℕ) + (4:ℂ)*(X t)*a^(2:ℕ) + (-4:ℂ)*(X t) + (8:ℂ)*a)/((8:ℂ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(3:ℕ)*a + (18:ℂ)*(X t)^(2:ℕ) + (-36:ℂ)*(X t)*a^(3:ℕ) + (72:ℂ)*(X t)*a + (-72:ℂ)*a^(2:ℕ) + (72:ℂ))/((4:ℂ)*(X t)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((2:ℂ)*(X t)^(2:ℕ) + (4:ℂ)*(X t)*a + (8:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((72:ℂ)*(X t)^(2:ℕ) + (144:ℂ)*(X t)*a + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(8:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a + (36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(6:ℕ) + (-24:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(5:ℕ)*a + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (48:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(4:ℕ) + (-32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (576:ℂ)*(X t)^(3:ℕ)*a + (192:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (1152:ℂ)*(X t)*a + (-2304:ℂ))/((32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-171:ℂ)*(X t)^(10:ℕ) + (-684:ℂ)*(X t)^(8:ℕ) + (1368:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-2736:ℂ)*(X t)^(7:ℕ)*a + (304:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-912:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-2736:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (5472:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-16416:ℂ)*(X t)^(5:ℕ)*a + (1216:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (3648:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-7296:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (32832:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-21888:ℂ)*(X t)^(4:ℕ) + (14592:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (21888:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-65664:ℂ)*(X t)^(3:ℕ)*a + (14592:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-14592:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-43776:ℂ)*(X t)^(2:ℕ) + (29184:ℂ)*(X t)*(Y t)*a*b + (-87552:ℂ)*(X t)*a + (175104:ℂ))/((1152:ℂ)*(X t)^(3:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(2:ℕ) + (-18:ℂ)*(X t)*a + (-36:ℂ))/((2:ℂ)*(X t)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(2:ℕ) + (18:ℂ)*(X t)*a^(3:ℕ) + (-18:ℂ)*(X t)*a + (36:ℂ)*a^(2:ℕ) + (-36:ℂ))/((2:ℂ)*(X t)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-171:ℂ)*(X t)^(10:ℕ) + (-684:ℂ)*(X t)^(8:ℕ) + (1368:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-2736:ℂ)*(X t)^(7:ℕ)*a + (304:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-912:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-2736:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (5472:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-16416:ℂ)*(X t)^(5:ℕ)*a + (1216:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (3648:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-7296:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (32832:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-21888:ℂ)*(X t)^(4:ℕ) + (14592:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (21888:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-65664:ℂ)*(X t)^(3:ℕ)*a + (14592:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-14592:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-43776:ℂ)*(X t)^(2:ℕ) + (29184:ℂ)*(X t)*(Y t)*a*b + (-87552:ℂ)*(X t)*a + (175104:ℂ))/((1152:ℂ)*(X t)^(3:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((171:ℂ)*(X t)^(10:ℕ) + (684:ℂ)*(X t)^(8:ℕ) + (-1368:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (2736:ℂ)*(X t)^(7:ℕ)*a + (-304:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (912:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (2736:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-5472:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (16416:ℂ)*(X t)^(5:ℕ)*a + (-1216:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-3648:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (7296:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-32832:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (21888:ℂ)*(X t)^(4:ℕ) + (-14592:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-21888:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (65664:ℂ)*(X t)^(3:ℕ)*a + (-14592:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (14592:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (43776:ℂ)*(X t)^(2:ℕ) + (-29184:ℂ)*(X t)*(Y t)*a*b + (87552:ℂ)*(X t)*a + (-175104:ℂ))/((1152:ℂ)*(X t)^(3:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-171:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (171:ℂ)*(X t)^(8:ℕ) + (342:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-342:ℂ)*(X t)^(7:ℕ)*a + (38:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-228:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-684:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (684:ℂ)*(X t)^(6:ℕ) + (-228:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-4104:ℂ)*(X t)^(5:ℕ)*a + (152:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-152:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (456:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1824:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (2736:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-5472:ℂ)*(X t)^(4:ℕ) + (-304:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (912:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (5472:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-21888:ℂ)*(X t)^(3:ℕ)*a + (-1216:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-3648:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-16416:ℂ)*(X t)^(2:ℕ) + (-32832:ℂ)*(X t)*a + (21888:ℂ))/((36:ℂ)*(X t)^(5:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((171:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-171:ℂ)*(X t)^(8:ℕ) + (-342:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (342:ℂ)*(X t)^(7:ℕ)*a + (-38:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (228:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (684:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-684:ℂ)*(X t)^(6:ℕ) + (228:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (4104:ℂ)*(X t)^(5:ℕ)*a + (-152:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (152:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-456:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (1824:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-2736:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (4104:ℂ)*(X t)^(4:ℕ) + (304:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-912:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-5472:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (19152:ℂ)*(X t)^(3:ℕ)*a + (1216:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (3648:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (10944:ℂ)*(X t)^(2:ℕ) + (32832:ℂ)*(X t)*a + (-21888:ℂ))/((36:ℂ)*(X t)^(5:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(2:ℕ) + (-2:ℂ)*(X t)*a + (-4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (-2:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ) + (-8:ℂ)*(X t)*a + (-16:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((19:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (38:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-684:ℂ)*(X t)^(2:ℕ) + (-152:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (-1368:ℂ)*(X t)*a + (-304:ℂ)*(Y t)^(2:ℕ) + (-2736:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(3:ℕ) + (-4:ℂ)*(X t)*a^(2:ℕ) + (4:ℂ)*(X t) + (-8:ℂ)*a)/((2:ℂ)*(X t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(3:ℕ) + (4:ℂ)*(X t)*a^(2:ℕ) + (-4:ℂ)*(X t) + (8:ℂ)*a)/((2:ℂ)*(X t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((8:ℂ)*(X t)^(2:ℕ) + (16:ℂ)*(X t)*a + (32:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(3:ℕ) + (9:ℂ)*(X t)^(8:ℕ)*a + (18:ℂ)*(X t)^(7:ℕ)*a^(4:ℕ) + (-36:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(7:ℕ) + (8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (24:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (-24:ℂ)*(X t)^(5:ℕ)*(Y t)*b + (-216:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(5:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (48:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(3:ℕ)*b + (-48:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(4:ℕ)*a^(3:ℕ) + (-432:ℂ)*(X t)^(4:ℕ)*a + (32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (192:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)*b + (288:ℂ)*(X t)^(3:ℕ)*a^(4:ℕ) + (-576:ℂ)*(X t)^(3:ℕ) + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (192:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (576:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-1728:ℂ)*(X t)^(2:ℕ)*a + (-128:ℂ)*(X t)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1152:ℂ)*(X t)*a^(2:ℕ) + (-2304:ℂ)*(X t) + (-256:ℂ)*(Y t)^(2:ℕ)*a + (-2304:ℂ)*a)/((16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (1:ℂ)*(X t)^(5:ℕ) + (-2:ℂ)*(X t)^(4:ℕ)*a^(3:ℕ) + (2:ℂ)*(X t)^(4:ℕ)*a + (-4:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (4:ℂ)*(X t)^(3:ℕ) + (8:ℂ)*(X t)^(2:ℕ)*a + (16:ℂ)*(X t)*a^(2:ℕ) + (32:ℂ)*a)/((8:ℂ)*(X t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*(X t)^(2:ℕ) + (-4:ℂ)*(X t)*a + (-8:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (-2:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ) + (-8:ℂ)*(X t)*a + (-16:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ) + (24:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-144:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-48:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-576:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-192:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(2:ℕ) + (36:ℂ)*(X t)*a + (72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(10:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(10:ℕ) + (-18:ℂ)*(X t)^(9:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(9:ℕ)*a + (-24:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (72:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (72:ℂ)*(X t)^(7:ℕ)*a + (-16:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-48:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (48:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-432:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (432:ℂ)*(X t)^(6:ℕ) + (-32:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-96:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (288:ℂ)*(X t)^(5:ℕ)*a + (64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (192:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (1152:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-576:ℂ)*(X t)^(4:ℕ) + (384:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (1152:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-2304:ℂ)*(X t)^(3:ℕ)*a + (-4608:ℂ)*(X t)^(2:ℕ) + (-4608:ℂ)*(X t)*a + (9216:ℂ))/((32:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(2:ℕ) + (-18:ℂ)*(X t)*a + (-36:ℂ))/((2:ℂ)*(X t)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (-2:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ) + (-8:ℂ)*(X t)*a + (-16:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(3:ℕ)*a + (6:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (18:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (72:ℂ)*(X t)*a + (24:ℂ)*(Y t)*b + (72:ℂ))/((4:ℂ)*(X t)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-36:ℂ)*(X t)^(7:ℕ)*a + (4:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-12:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-72:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-216:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-48:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (432:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-432:ℂ)*(X t)^(4:ℕ) + (-32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (192:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-576:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-576:ℂ)*(X t)^(2:ℕ) + (-128:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(3:ℕ)*a + (2:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*(X t)^(2:ℕ) + (-8:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (-2:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ) + (-8:ℂ)*(X t)*a + (-16:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ)*a + (-18:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(6:ℕ) + (8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(2:ℕ) + (-576:ℂ)*(X t)*a + (1152:ℂ))/((16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(6:ℕ) + (18:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-36:ℂ)*(X t)^(5:ℕ)*a + (4:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (8:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (24:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-216:ℂ)*(X t)^(3:ℕ)*a + (16:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (48:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(2:ℕ) + (32:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (192:ℂ)*(X t)*(Y t)*a*b + (288:ℂ)*(X t)*a^(3:ℕ) + (192:ℂ)*(Y t)*b + (576:ℂ)*a^(2:ℕ) + (576:ℂ))/((8:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(4:ℕ) + (2:ℂ)*(X t)^(3:ℕ)*a + (8:ℂ)*(X t)^(2:ℕ) + (8:ℂ)*(X t)*a + (16:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(4:ℕ) + (-18:ℂ)*(X t)^(3:ℕ)*a + (-72:ℂ)*(X t)^(2:ℕ) + (-72:ℂ)*(X t)*a + (-144:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(5:ℕ) + (-2:ℂ)*(X t)^(4:ℕ)*a + (-8:ℂ)*(X t)^(3:ℕ) + (16:ℂ)*(X t)*a^(2:ℕ) + (-16:ℂ)*(X t) + (32:ℂ)*a)/((2:ℂ)*(X t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*(X t)^(2:ℕ) + (-4:ℂ)*(X t)*a + (-8:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (3:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (9:ℂ)*(X t)^(4:ℕ) + (-2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (6:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (18:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (12:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (36:ℂ)*(X t)^(2:ℕ) + (-8:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (-16:ℂ)*(Y t)^(2:ℕ))/((2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (4:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-12:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ) + (-24:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-144:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-96:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ) + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-864:ℂ)*(X t)^(3:ℕ)*a + (-192:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-576:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2304:ℂ)*(X t)*a + (2304:ℂ))/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*(X t)^(3:ℕ) + (2:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-2:ℂ)*(X t)^(2:ℕ)*a + (4:ℂ)*(X t)*a^(2:ℕ) + (-4:ℂ)*(X t))/((8:ℂ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-2:ℂ)*(X t)^(5:ℕ)*a + (2:ℂ)*(X t)^(4:ℕ)*a^(4:ℕ) + (-4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (4:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-8:ℂ)*(X t)^(3:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ) + (-16:ℂ)*(X t)*a + (-32:ℂ))/((4:ℂ)*(X t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(2:ℕ) + (-2:ℂ)*(X t)*a + (-4:ℂ))/((2:ℂ)*(X t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (2:ℂ)*(X t)*a + (4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ)*a + (-18:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(6:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-432:ℂ)*(X t)^(3:ℕ)*a + (-32:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(2:ℕ) + (-576:ℂ)*(X t)*a + (1152:ℂ))/((16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(8:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a + (36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(6:ℕ) + (144:ℂ)*(X t)^(5:ℕ)*a + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(4:ℕ) + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (864:ℂ)*(X t)^(3:ℕ)*a + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (576:ℂ)*(X t)^(2:ℕ) + (1152:ℂ)*(X t)*a + (-2304:ℂ))/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(6:ℕ) + (18:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-36:ℂ)*(X t)^(5:ℕ)*a + (4:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (8:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (24:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-216:ℂ)*(X t)^(3:ℕ)*a + (16:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (48:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(2:ℕ) + (32:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (192:ℂ)*(X t)*(Y t)*a*b + (288:ℂ)*(X t)*a^(3:ℕ) + (-288:ℂ)*(X t)*a + (192:ℂ)*(Y t)*b + (576:ℂ)*a^(2:ℕ))/((8:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)

#print axioms weights_analytic0
end QuantitativeArithmeticSmallLevelNineteenGenericJet109
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet115
theorem weights_analytic0 (X Y Z : ℂ→ℂ) (a b s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s) (hZ : AnalyticAt ℂ Z s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (ha : a≠0) (i : Fin 103) :
    AnalyticAt ℂ (fun t => weights0 (X t) (Y t) (Z t) a b i) s := by
  fin_cases i
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(7:ℕ) + (54:ℂ)*(X t)^(6:ℕ)*(Y t)*a*b + (162:ℂ)*(X t)^(6:ℕ)*a + (-108:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (-648:ℂ)*(X t)^(5:ℕ) + (216:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (648:ℂ)*(X t)^(4:ℕ)*a + (-864:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (2592:ℂ)*(X t)^(2:ℕ)*a + (-1728:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (5184:ℂ)*(X t) + (10368:ℂ)*a)/((8:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-54:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (162:ℂ)*(X t)^(4:ℕ) + (-12:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (36:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-108:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (72:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (648:ℂ)*(X t)^(2:ℕ) + (144:ℂ)*(X t)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-864:ℂ)*(Y t)*b)/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(7:ℕ) + (54:ℂ)*(X t)^(6:ℕ)*(Y t)*a*b + (162:ℂ)*(X t)^(6:ℕ)*a + (-108:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (-648:ℂ)*(X t)^(5:ℕ) + (216:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (648:ℂ)*(X t)^(4:ℕ)*a + (144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (-1296:ℂ)*(X t)^(3:ℕ) + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*a*b + (2592:ℂ)*(X t)^(2:ℕ)*a + (576:ℂ)*(X t)*(Y t)^(2:ℕ) + (-1728:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (10368:ℂ)*a)/((8:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (108:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-162:ℂ)*(X t)^(6:ℕ) + (12:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a*b + (-72:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (36:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (648:ℂ)*(X t)^(5:ℕ)*a + (-24:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (72:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-72:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (864:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-1296:ℂ)*(X t)^(4:ℕ) + (-288:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2592:ℂ)*(X t)^(3:ℕ)*a + (1728:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-1728:ℂ)*(X t)*(Y t)*a*b + (10368:ℂ))/((1:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((648:ℂ)*(X t)^(2:ℕ) + (-432:ℂ)*(X t)*(Y t)*a*b + (2592:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2592:ℂ)*(X t)^(2:ℕ) + (1728:ℂ)*(X t)*(Y t)*a*b + (-10368:ℂ))/((1:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (81:ℂ)*(X t)^(8:ℕ) + (162:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(7:ℕ)*a + (108:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-216:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (216:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-1944:ℂ)*(X t)^(5:ℕ)*a + (144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (3888:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-3888:ℂ)*(X t)^(4:ℕ) + (864:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (2592:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-7776:ℂ)*(X t)^(3:ℕ)*a + (-576:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5184:ℂ)*(X t)^(2:ℕ) + (-10368:ℂ)*(X t)*a + (20736:ℂ))/((2:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(7:ℕ)*a + (54:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (162:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(6:ℕ) + (-216:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-648:ℂ)*(X t)^(5:ℕ)*a + (-72:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (216:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (1296:ℂ)*(X t)^(4:ℕ) + (48:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-864:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (1296:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*b + (-288:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-864:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (2592:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1728:ℂ)*(X t)*(Y t)*a*b + (3456:ℂ)*(Y t)*b)/((1:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(3:ℕ)*a + (-54:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (162:ℂ)*(X t)^(2:ℕ) + (-108:ℂ)*(X t)*(Y t)*a*b + (324:ℂ)*(X t)*a + (648:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((27:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ)*b + (-27:ℂ)*(X t)^(8:ℕ)*b + (-54:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ)*b + (54:ℂ)*(X t)^(7:ℕ)*a*b + (108:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ)*b + (-108:ℂ)*(X t)^(6:ℕ)*b + (432:ℂ)*(X t)^(5:ℕ)*a*b + (-48:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b + (48:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*b + (144:ℂ)*(X t)^(4:ℕ)*(Y t) + (-864:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ)*b + (432:ℂ)*(X t)^(4:ℕ)*b + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b + (-864:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ)*b + (2592:ℂ)*(X t)^(3:ℕ)*a*b + (192:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*b + (576:ℂ)*(X t)^(2:ℕ)*(Y t) + (3456:ℂ)*(X t)*a*b + (-6912:ℂ)*b)/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((54:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (648:ℂ)*(X t)^(5:ℕ)*a + (-432:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (432:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (2592:ℂ)*(X t)^(3:ℕ)*a + (864:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (2592:ℂ)*(X t)^(2:ℕ) + (-1728:ℂ)*(X t)*(Y t)*a*b + (10368:ℂ))/((1:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ) + (6:ℂ)*(X t)^(6:ℕ)*(Y t)*a*b + (18:ℂ)*(X t)^(6:ℕ)*a + (-12:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (-72:ℂ)*(X t)^(5:ℕ) + (24:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (72:ℂ)*(X t)^(4:ℕ)*a + (-144:ℂ)*(X t)^(3:ℕ) + (288:ℂ)*(X t)^(2:ℕ)*a + (-192:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (1152:ℂ)*a)/((2:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(7:ℕ) + (-18:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(6:ℕ)*a + (36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(5:ℕ) + (72:ℂ)*(X t)^(4:ℕ)*a + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(3:ℕ) + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (576:ℂ)*(X t)^(2:ℕ)*a + (64:ℂ)*(X t)*(Y t)^(2:ℕ) + (1152:ℂ)*(X t) + (-384:ℂ)*(Y t)*a*b + (1152:ℂ)*a)/((2:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(2:ℕ) + (-6:ℂ)*(X t)*(Y t)*a*b + (36:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-162:ℂ)*(X t)^(4:ℕ) + (108:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-324:ℂ)*(X t)^(3:ℕ)*a + (216:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (648:ℂ)*(X t)^(2:ℕ) + (-864:ℂ)*(X t)*(Y t)*a*b + (-1296:ℂ)*(X t)*a + (5184:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((648:ℂ)*(X t)^(2:ℕ) + (-432:ℂ)*(X t)*(Y t)*a*b + (2592:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-324:ℂ)*(X t)^(2:ℕ) + (216:ℂ)*(X t)*(Y t)*a*b + (-1296:ℂ))/((1:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(4:ℕ) + (-12:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(4:ℕ) + (6:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (18:ℂ)*(X t)^(3:ℕ)*a + (-12:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-72:ℂ)*(X t)^(2:ℕ) + (24:ℂ)*(X t)*(Y t)*a*b + (72:ℂ)*(X t)*a + (-144:ℂ))/((2:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-162:ℂ)*(X t)^(4:ℕ) + (108:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-1296:ℂ)*(X t)^(2:ℕ) + (432:ℂ)*(X t)*(Y t)*a*b + (-2592:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(7:ℕ) + (-18:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(6:ℕ)*a + (36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(5:ℕ) + (72:ℂ)*(X t)^(4:ℕ)*a + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(3:ℕ) + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (576:ℂ)*(X t)^(2:ℕ)*a + (64:ℂ)*(X t)*(Y t)^(2:ℕ) + (1152:ℂ)*(X t) + (-384:ℂ)*(Y t)*a*b + (1152:ℂ)*a)/((2:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-36:ℂ)*(X t)^(3:ℕ)*a + (24:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (72:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (-144:ℂ)*(X t)*a + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((648:ℂ)*(X t)^(2:ℕ) + (-432:ℂ)*(X t)*(Y t)*a*b + (2592:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(3:ℕ) + (-6:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-18:ℂ)*(X t)^(2:ℕ)*a + (12:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (36:ℂ)*(X t) + (-72:ℂ)*a)/((2:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((72:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ) + (6:ℂ)*(X t)^(6:ℕ)*(Y t)*a*b + (18:ℂ)*(X t)^(6:ℕ)*a + (-12:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (-72:ℂ)*(X t)^(5:ℕ) + (24:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (72:ℂ)*(X t)^(4:ℕ)*a + (-144:ℂ)*(X t)^(3:ℕ) + (288:ℂ)*(X t)^(2:ℕ)*a + (-192:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (1152:ℂ)*a)/((2:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((54:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (648:ℂ)*(X t)^(3:ℕ)*a + (-432:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (432:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (648:ℂ)*(X t)^(2:ℕ) + (-144:ℂ)*(X t)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-432:ℂ)*(X t)*(Y t)*a*b + (2592:ℂ)*(X t)*a + (864:ℂ)*(Y t)*b + (2592:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(7:ℕ)*a + (54:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (162:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-108:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-324:ℂ)*(X t)^(5:ℕ)*a + (-72:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-432:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (2592:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*b + (-288:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-864:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (2592:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2592:ℂ)*(X t)^(2:ℕ) + (-1728:ℂ)*(X t)*(Y t)*a*b + (3456:ℂ)*(Y t)*b)/((1:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ) + (-144:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(4:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-864:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t)^(2:ℕ) + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(3:ℕ) + (-6:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-18:ℂ)*(X t)^(2:ℕ)*a + (12:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (36:ℂ)*(X t) + (-72:ℂ)*a)/((2:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (81:ℂ)*(X t)^(8:ℕ) + (162:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(7:ℕ)*a + (108:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-216:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (216:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-1944:ℂ)*(X t)^(5:ℕ)*a + (144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (3888:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-3888:ℂ)*(X t)^(4:ℕ) + (864:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (2592:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-7776:ℂ)*(X t)^(3:ℕ)*a + (-576:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5184:ℂ)*(X t)^(2:ℕ) + (-10368:ℂ)*(X t)*a + (20736:ℂ))/((2:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(7:ℕ) + (18:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(6:ℕ)*a + (-36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(5:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*a + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (288:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(3:ℕ) + (96:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-864:ℂ)*(X t)^(2:ℕ)*a + (-64:ℂ)*(X t)*(Y t)^(2:ℕ) + (-1152:ℂ)*(X t) + (384:ℂ)*(Y t)*a*b + (-1152:ℂ)*a)/((8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2592:ℂ)*(X t)^(2:ℕ) + (1728:ℂ)*(X t)*(Y t)*a*b + (-10368:ℂ))/((1:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-36:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-144:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (216:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (288:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (1296:ℂ)*(X t)^(4:ℕ) + (288:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (288:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-864:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(4:ℕ) + (-1728:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (5184:ℂ)*(X t)^(2:ℕ) + (-1152:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (2304:ℂ)*(Y t)^(2:ℕ))/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((513:ℂ)*(X t)^(10:ℕ) + (-342:ℂ)*(X t)^(9:ℕ)*(Y t)*a*b + (-1026:ℂ)*(X t)^(9:ℕ)*a + (684:ℂ)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (2052:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (2052:ℂ)*(X t)^(8:ℕ) + (-1368:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (-4104:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (4104:ℂ)*(X t)^(7:ℕ)*a + (-912:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-2736:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (2736:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (608:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a*b + (-1824:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (1824:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (5472:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-5472:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (49248:ℂ)*(X t)^(5:ℕ)*a + (-1216:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (21888:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-98496:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (65664:ℂ)*(X t)^(4:ℕ) + (2432:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (-7296:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (7296:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-65664:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-65664:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (196992:ℂ)*(X t)^(3:ℕ)*a + (14592:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (43776:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (131328:ℂ)*(X t)^(2:ℕ) + (-87552:ℂ)*(X t)*(Y t)*a*b + (262656:ℂ)*(X t)*a + (-525312:ℂ))/((96:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((162:ℂ)*(X t)^(2:ℕ) + (-108:ℂ)*(X t)*(Y t)*a*b + (648:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-162:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(2:ℕ) + (108:ℂ)*(X t)*(Y t)*a^(3:ℕ)*b + (-108:ℂ)*(X t)*(Y t)*a*b + (-648:ℂ)*a^(2:ℕ) + (648:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((513:ℂ)*(X t)^(10:ℕ) + (-342:ℂ)*(X t)^(9:ℕ)*(Y t)*a*b + (-1026:ℂ)*(X t)^(9:ℕ)*a + (684:ℂ)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (2052:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (2052:ℂ)*(X t)^(8:ℕ) + (-1368:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (-4104:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (4104:ℂ)*(X t)^(7:ℕ)*a + (-912:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-2736:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (2736:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (608:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a*b + (-1824:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (1824:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (5472:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-5472:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (49248:ℂ)*(X t)^(5:ℕ)*a + (-1216:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (21888:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-98496:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (65664:ℂ)*(X t)^(4:ℕ) + (2432:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (-7296:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (7296:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-65664:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-65664:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (196992:ℂ)*(X t)^(3:ℕ)*a + (14592:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (43776:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (131328:ℂ)*(X t)^(2:ℕ) + (-87552:ℂ)*(X t)*(Y t)*a*b + (262656:ℂ)*(X t)*a + (-525312:ℂ))/((96:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-513:ℂ)*(X t)^(10:ℕ) + (342:ℂ)*(X t)^(9:ℕ)*(Y t)*a*b + (1026:ℂ)*(X t)^(9:ℕ)*a + (-684:ℂ)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-2052:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-2052:ℂ)*(X t)^(8:ℕ) + (1368:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (4104:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-4104:ℂ)*(X t)^(7:ℕ)*a + (912:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (2736:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-2736:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-608:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a*b + (1824:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-1824:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-5472:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (5472:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-49248:ℂ)*(X t)^(5:ℕ)*a + (1216:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (-3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3648:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-21888:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (98496:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-65664:ℂ)*(X t)^(4:ℕ) + (-2432:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (7296:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-7296:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (65664:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (65664:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-196992:ℂ)*(X t)^(3:ℕ)*a + (-14592:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-43776:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-131328:ℂ)*(X t)^(2:ℕ) + (87552:ℂ)*(X t)*(Y t)*a*b + (-262656:ℂ)*(X t)*a + (525312:ℂ))/((96:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-114:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (684:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (76:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a*b + (-456:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (228:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-684:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (4104:ℂ)*(X t)^(5:ℕ)*a + (-152:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (456:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-456:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2736:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (5472:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-1824:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (912:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-2736:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (16416:ℂ)*(X t)^(3:ℕ)*a + (10944:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (16416:ℂ)*(X t)^(2:ℕ) + (-10944:ℂ)*(X t)*(Y t)*a*b + (65664:ℂ))/((3:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((114:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-684:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-76:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a*b + (456:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-228:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (684:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-4104:ℂ)*(X t)^(5:ℕ)*a + (152:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (-456:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (456:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2736:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-5472:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (4104:ℂ)*(X t)^(4:ℕ) + (1824:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-912:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-16416:ℂ)*(X t)^(3:ℕ)*a + (-10944:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (10944:ℂ)*(X t)*(Y t)*a*b + (-65664:ℂ))/((3:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(2:ℕ) + (-12:ℂ)*(X t)*(Y t)*a*b + (72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(4:ℕ) + (-12:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-342:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (228:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (12312:ℂ)*(X t)^(2:ℕ) + (-912:ℂ)*(X t)*(Y t)^(3:ℕ)*a*b + (-8208:ℂ)*(X t)*(Y t)*a*b + (5472:ℂ)*(Y t)^(2:ℕ) + (49248:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*(Z t)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(3:ℕ) + (12:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (36:ℂ)*(X t)^(2:ℕ)*a + (-24:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (-72:ℂ)*(X t) + (144:ℂ)*a)/((1:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(3:ℕ) + (-12:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-36:ℂ)*(X t)^(2:ℕ)*a + (24:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (72:ℂ)*(X t) + (-144:ℂ)*a)/((1:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(7:ℕ) + (18:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(6:ℕ)*a + (-36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(5:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*a + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (288:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(3:ℕ) + (96:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-864:ℂ)*(X t)^(2:ℕ)*a + (-64:ℂ)*(X t)*(Y t)^(2:ℕ) + (-1152:ℂ)*(X t) + (384:ℂ)*(Y t)*a*b + (-1152:ℂ)*a)/((2:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-9:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a + (-18:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (-162:ℂ)*(X t)^(7:ℕ) + (36:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-36:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a + (-324:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(6:ℕ)*a + (144:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-72:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (-216:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (216:ℂ)*(X t)^(5:ℕ)*(Y t)*b + (648:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-648:ℂ)*(X t)^(5:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)*a + (48:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a*b + (144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + (-288:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (288:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (1296:ℂ)*(X t)^(4:ℕ)*a + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (-288:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (576:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (864:ℂ)*(X t)^(3:ℕ)*(Y t)*b + (-5184:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (5184:ℂ)*(X t)^(3:ℕ) + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(4:ℕ)*a + (192:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*a*b + (1152:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (-1728:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-5184:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (10368:ℂ)*(X t)^(2:ℕ)*a + (-384:ℂ)*(X t)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (1152:ℂ)*(X t)*(Y t)^(2:ℕ)*a^(2:ℕ) + (20736:ℂ)*(X t) + (-6912:ℂ)*(Y t)*a*b + (20736:ℂ)*a)/((4:ℂ)*(X t)^(6:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(5:ℕ) + (-6:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(3:ℕ)*b + (6:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (36:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(3:ℕ) + (-72:ℂ)*(X t)^(2:ℕ)*a + (48:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (-288:ℂ)*a)/((2:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((72:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(4:ℕ) + (-12:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-27:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (18:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (54:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-162:ℂ)*(X t)^(2:ℕ) + (-36:ℂ)*(X t)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (216:ℂ)*(Y t)*b + (-648:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-648:ℂ)*(X t)^(2:ℕ) + (432:ℂ)*(X t)*(Y t)*a*b + (-2592:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ)*(Y t)*a^(2:ℕ) + (9:ℂ)*(X t)^(7:ℕ)*(Y t) + (18:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(3:ℕ) + (-18:ℂ)*(X t)^(6:ℕ)*(Y t)*a + (-36:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ) + (36:ℂ)*(X t)^(5:ℕ)*(Y t) + (-144:ℂ)*(X t)^(4:ℕ)*(Y t)*a + (216:ℂ)*(X t)^(4:ℕ)*a*b + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ) + (-144:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b^(2:ℕ) + (288:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ) + (-288:ℂ)*(X t)^(3:ℕ)*(Y t) + (-432:ℂ)*(X t)^(3:ℕ)*b + (96:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a*b + (288:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(3:ℕ) + (288:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b^(2:ℕ) + (-576:ℂ)*(X t)^(2:ℕ)*(Y t)*a + (864:ℂ)*(X t)^(2:ℕ)*a*b + (-64:ℂ)*(X t)*(Y t)^(3:ℕ) + (-192:ℂ)*(X t)*(Y t)^(2:ℕ)*a^(2:ℕ)*b + (-1152:ℂ)*(X t)*(Y t) + (-1728:ℂ)*(X t)*b + (384:ℂ)*(Y t)^(2:ℕ)*a*b)/((8:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(8:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a + (36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(6:ℕ) + (144:ℂ)*(X t)^(5:ℕ)*a + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(4:ℕ) + (-288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (864:ℂ)*(X t)^(3:ℕ)*a + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (1152:ℂ)*(X t)*a + (-2304:ℂ))/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (81:ℂ)*(X t)^(8:ℕ) + (162:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-162:ℂ)*(X t)^(7:ℕ)*a + (-324:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(6:ℕ) + (-1296:ℂ)*(X t)^(5:ℕ)*a + (144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2592:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1296:ℂ)*(X t)^(4:ℕ) + (2592:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-7776:ℂ)*(X t)^(3:ℕ)*a + (-576:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-10368:ℂ)*(X t)*a + (20736:ℂ))/((8:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(4:ℕ) + (-12:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(3:ℕ)*a + (54:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-54:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-162:ℂ)*(X t)^(2:ℕ) + (36:ℂ)*(X t)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (108:ℂ)*(X t)*(Y t)*a*b + (-324:ℂ)*(X t)*a + (-216:ℂ)*(Y t)*b + (-648:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(6:ℕ)*a + (-18:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (-54:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (54:ℂ)*(X t)^(5:ℕ)*(Y t)*b + (162:ℂ)*(X t)^(5:ℕ) + (12:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a*b + (-36:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (36:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (-216:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (-24:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (72:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (216:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b + (216:ℂ)*(X t)^(3:ℕ)*(Y t)*b + (648:ℂ)*(X t)^(3:ℕ) + (48:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*a*b + (288:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (-432:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-1296:ℂ)*(X t)^(2:ℕ)*a + (-96:ℂ)*(X t)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (-288:ℂ)*(X t)*(Y t)^(2:ℕ) + (576:ℂ)*(Y t)^(2:ℕ)*a)/((1:ℂ)*(X t)^(6:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(7:ℕ) + (-18:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(6:ℕ)*a + (36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(5:ℕ) + (144:ℂ)*(X t)^(4:ℕ)*a + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (-288:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(3:ℕ) + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (576:ℂ)*(X t)^(2:ℕ)*a + (64:ℂ)*(X t)*(Y t)^(2:ℕ) + (192:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (1152:ℂ)*(X t) + (-384:ℂ)*(Y t)*a*b)/((8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(4:ℕ) + (-12:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-36:ℂ)*(X t)^(2:ℕ) + (24:ℂ)*(X t)*(Y t)*a*b + (-144:ℂ))/((1:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(7:ℕ)*a + (54:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (162:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-108:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-324:ℂ)*(X t)^(5:ℕ)*a + (-72:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-432:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (2592:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*b + (-288:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-864:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (2592:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2592:ℂ)*(X t)^(2:ℕ) + (-1728:ℂ)*(X t)*(Y t)*a*b + (3456:ℂ)*(Y t)*b)/((4:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(10:ℕ)*a^(2:ℕ) + (81:ℂ)*(X t)^(10:ℕ) + (162:ℂ)*(X t)^(9:ℕ)*a^(3:ℕ) + (-162:ℂ)*(X t)^(9:ℕ)*a + (-324:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(8:ℕ) + (-648:ℂ)*(X t)^(7:ℕ)*a + (144:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (1296:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-2592:ℂ)*(X t)^(6:ℕ) + (96:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a*b + (864:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (2592:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-2592:ℂ)*(X t)^(5:ℕ)*a + (576:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1152:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1728:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-10368:ℂ)*(X t)^(4:ℕ) + (-1152:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3456:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-20736:ℂ)*(X t)^(3:ℕ)*a + (768:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*b + (6912:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-20736:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (20736:ℂ)*(X t)^(2:ℕ) + (13824:ℂ)*(X t)*(Y t)*a*b + (-27648:ℂ)*(Y t)*b)/((8:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(4:ℕ) + (12:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-144:ℂ)*(X t)^(2:ℕ) + (48:ℂ)*(X t)*(Y t)*a*b + (-288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((162:ℂ)*(X t)^(4:ℕ) + (-108:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (1296:ℂ)*(X t)^(2:ℕ) + (-432:ℂ)*(X t)*(Y t)*a*b + (2592:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (9:ℂ)*(X t)^(7:ℕ)*a + (18:ℂ)*(X t)^(6:ℕ)*a^(4:ℕ) + (-18:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (36:ℂ)*(X t)^(5:ℕ)*a + (-144:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(4:ℕ) + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-48:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-288:ℂ)*(X t)^(3:ℕ)*a + (96:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (288:ℂ)*(X t)^(2:ℕ)*a^(4:ℕ) + (-864:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (576:ℂ)*(X t)^(2:ℕ) + (-64:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (-192:ℂ)*(X t)*(Y t)*a*b + (-1152:ℂ)*(X t)*a + (384:ℂ)*(Y t)*a^(2:ℕ)*b + (-1152:ℂ)*a^(2:ℕ) + (1152:ℂ))/((4:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((72:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-54:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-162:ℂ)*(X t)^(4:ℕ) + (-12:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (36:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (108:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-216:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-648:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)^(3:ℕ)*a*b + (288:ℂ)*(Y t)^(2:ℕ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-81:ℂ)*(X t)^(7:ℕ)*a + (-162:ℂ)*(X t)^(6:ℕ)*a^(4:ℕ) + (162:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(5:ℕ)*a + (-72:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (216:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (1296:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (48:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (-144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (288:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-2592:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (2592:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (-576:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-864:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (1728:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-2592:ℂ)*(X t)^(2:ℕ)*a^(4:ℕ) + (7776:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2592:ℂ)*(X t)^(2:ℕ) + (192:ℂ)*(X t)*(Y t)^(3:ℕ)*a*b + (-576:ℂ)*(X t)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (1152:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (1728:ℂ)*(X t)*(Y t)*a*b + (10368:ℂ)*(X t)*a + (-1152:ℂ)*(Y t)^(2:ℕ) + (-3456:ℂ)*(Y t)*a^(2:ℕ)*b + (3456:ℂ)*(Y t)*b + (10368:ℂ)*a^(2:ℕ) + (-10368:ℂ))/((4:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(2:ℕ) + (6:ℂ)*(X t)*(Y t)*a*b + (-36:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(2:ℕ) + (6:ℂ)*(X t)*(Y t)*a^(3:ℕ)*b + (-6:ℂ)*(X t)*(Y t)*a*b + (-36:ℂ)*a^(2:ℕ) + (36:ℂ))/((2:ℂ)*(X t)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-18:ℂ)*(X t)^(2:ℕ) + (12:ℂ)*(X t)*(Y t)*a*b + (-72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(5:ℕ)*a + (6:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(4:ℕ)*b + (-12:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-36:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (72:ℂ)*(X t)^(3:ℕ)*a + (72:ℂ)*(X t)^(2:ℕ) + (-48:ℂ)*(X t)*(Y t)*a*b + (288:ℂ))/((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-36:ℂ)*(X t)^(2:ℕ) + (24:ℂ)*(X t)*(Y t)*a*b + (-144:ℂ))/((1:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((18:ℂ)*(X t)^(2:ℕ) + (-12:ℂ)*(X t)*(Y t)*a*b + (72:ℂ))/((1:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-36:ℂ)*(X t)^(2:ℕ) + (24:ℂ)*(X t)*(Y t)*a*b + (-144:ℂ))/((1:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(7:ℕ)*a + (54:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (162:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-108:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-324:ℂ)*(X t)^(5:ℕ)*a + (144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-432:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (2592:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*b + (-864:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (2592:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2592:ℂ)*(X t)^(2:ℕ) + (-1728:ℂ)*(X t)*(Y t)*a*b + (3456:ℂ)*(Y t)*b)/((4:ℂ)*(X t)^(5:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(7:ℕ)*a + (-18:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-54:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-162:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (12:ℂ)*(X t)^(5:ℕ)*(Y t)^(3:ℕ)*a*b + (648:ℂ)*(X t)^(5:ℕ)*a + (72:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-72:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-216:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-144:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1296:ℂ)*(X t)^(3:ℕ)*a + (96:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*b + (864:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-2592:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (2592:ℂ)*(X t)^(2:ℕ) + (1728:ℂ)*(X t)*(Y t)*a*b + (-3456:ℂ)*(Y t)*b)/((1:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a))) s
    fun_prop (disch := simp_all)

#print axioms weights_analytic0
end QuantitativeArithmeticSmallLevelNineteenGenericJet115
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet200
theorem weights_analytic2 (X Y Z : ℂ→ℂ) (a b s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s) (hZ : AnalyticAt ℂ Z s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (ha : a≠0) (i : Fin 53) :
    AnalyticAt ℂ (fun t => weights2 (X t) (Y t) (Z t) a b i) s := by
  fin_cases i
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(2:ℕ) + (-18:ℂ)*(X t)*a + (4:ℂ)*(Y t)^(2:ℕ) + (72:ℂ))/((9:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*(X t)*a + (4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*a)/((1:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((2:ℂ)*(Y t)^(2:ℕ)*a)/((9:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*a)/((1:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*(X t)*a + (8:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(2:ℕ) + (-4:ℂ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((19:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-38:ℂ)*(X t)*(Y t)^(2:ℕ)*a)/((36:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*a)/((1:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((19:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-38:ℂ)*(X t)*(Y t)^(2:ℕ)*a)/((36:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-19:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (38:ℂ)*(X t)*(Y t)^(2:ℕ)*a)/((36:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(2:ℕ) + (-18:ℂ)*(X t)*a + (4:ℂ)*(Y t)^(2:ℕ) + (72:ℂ))/((9:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-171:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (342:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (-76:ℂ)*(Y t)^(4:ℕ) + (-1368:ℂ)*(Y t)^(2:ℕ))/((81:ℂ)*(X t)^(2:ℕ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)*a)/((2:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)*(Y t)^(2:ℕ)*a)/((18:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (16:ℂ))/((4:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t) + (-2:ℂ)*a)/((1:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-4:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-6:ℂ)*(X t)*a + (-4:ℂ)*(Y t)*b)/((3:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(2:ℕ) + (4:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)*(Y t)^(2:ℕ)*a)/((18:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (1:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-4:ℂ)*(Y t)^(2:ℕ))/((9:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-6:ℂ)*(X t)*a + (-4:ℂ)*(Y t)*b)/((3:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)

#print axioms weights_analytic2
end QuantitativeArithmeticSmallLevelNineteenGenericJet200
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet201
theorem weights_analytic2 (X Y Z : ℂ→ℂ) (a b s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s) (hZ : AnalyticAt ℂ Z s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (ha : a≠0) (i : Fin 101) :
    AnalyticAt ℂ (fun t => weights2 (X t) (Y t) (Z t) a b i) s := by
  fin_cases i
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(8:ℕ) + (-4:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(6:ℕ) + (16:ℂ)*(X t)^(4:ℕ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(10:ℕ) + (18:ℂ)*(X t)^(9:ℕ)*a + (36:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-108:ℂ)*(X t)^(8:ℕ) + (-72:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (144:ℂ)*(X t)^(7:ℕ)*a + (16:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (144:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(6:ℕ) + (576:ℂ)*(X t)^(5:ℕ)*a + (-64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (128:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (576:ℂ)*(X t)^(4:ℕ) + (-1152:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (2304:ℂ)*(X t)^(3:ℕ)*a + (256:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2304:ℂ)*(X t)^(2:ℕ) + (4608:ℂ)*(X t)*a)/((16:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(10:ℕ) + (18:ℂ)*(X t)^(9:ℕ)*a + (36:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-108:ℂ)*(X t)^(8:ℕ) + (-72:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (144:ℂ)*(X t)^(7:ℕ)*a + (16:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (144:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-432:ℂ)*(X t)^(6:ℕ) + (576:ℂ)*(X t)^(5:ℕ)*a + (-64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (128:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t)^(4:ℕ) + (-1152:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (2304:ℂ)*(X t)^(3:ℕ)*a + (256:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (4608:ℂ)*(X t)*a)/((16:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-3:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (9:ℂ)*(X t)^(6:ℕ) + (-4:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (12:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-24:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(4:ℕ) + (16:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-48:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (144:ℂ)*(X t)^(2:ℕ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-4:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (12:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-12:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (36:ℂ)*(X t)^(6:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (48:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-96:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-144:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(4:ℕ) + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-192:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (576:ℂ)*(X t)^(2:ℕ))/((4:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(10:ℕ) + (-36:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (108:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (-648:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (648:ℂ)*(X t)^(8:ℕ) + (72:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-216:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (648:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (648:ℂ)*(X t)^(7:ℕ)*a + (-144:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (1296:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (864:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-1728:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-5184:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (5184:ℂ)*(X t)^(5:ℕ)*a + (64:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-64:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ) + (1728:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2304:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1728:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (5184:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (10368:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-10368:ℂ)*(X t)^(4:ℕ) + (384:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (1152:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2304:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (10368:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-10368:ℂ)*(X t)^(3:ℕ)*a + (-256:ℂ)*(X t)^(2:ℕ)*(Y t)^(4:ℕ) + (-4608:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (6912:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-20736:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (20736:ℂ)*(X t)^(2:ℕ) + (-4608:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (-41472:ℂ)*(X t)*a + (9216:ℂ)*(Y t)^(2:ℕ) + (165888:ℂ))/((36:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(6:ℕ) + (-144:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (144:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-864:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-144:ℂ)*(X t)^(4:ℕ) + (576:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1152:ℂ)*(X t)^(2:ℕ) + (-2304:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ)*a + (18:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-18:ℂ)*(X t)^(6:ℕ) + (36:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-72:ℂ)*(X t)^(5:ℕ)*a + (-72:ℂ)*(X t)^(4:ℕ)*a^(4:ℕ) + (216:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ) + (-144:ℂ)*(X t)^(3:ℕ)*a + (288:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(2:ℕ))/((2:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a + (18:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(7:ℕ) + (-72:ℂ)*(X t)^(6:ℕ)*a + (-8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (-72:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (216:ℂ)*(X t)^(5:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (144:ℂ)*(X t)^(4:ℕ)*a^(3:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*a + (32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-64:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (576:ℂ)*(X t)^(3:ℕ) + (-576:ℂ)*(X t)^(2:ℕ)*a + (-128:ℂ)*(X t)*(Y t)^(2:ℕ) + (384:ℂ)*(X t)*(Y t)*b + (2304:ℂ)*a)/((2:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(7:ℕ)*a + (18:ℂ)*(X t)^(6:ℕ) + (-36:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (72:ℂ)*(X t)^(5:ℕ)*a + (-72:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(4:ℕ) + (144:ℂ)*(X t)^(3:ℕ)*a + (288:ℂ)*(X t)^(2:ℕ))/((2:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((3:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a + (-12:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (36:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ) + (-144:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (144:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-48:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (144:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(4:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-288:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (192:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-576:ℂ)*(X t)^(2:ℕ) + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(9:ℕ) + (2:ℂ)*(X t)^(8:ℕ)*a + (4:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (-12:ℂ)*(X t)^(7:ℕ) + (-8:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(6:ℕ)*a + (16:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(5:ℕ) + (64:ℂ)*(X t)^(4:ℕ)*a + (-64:ℂ)*(X t)^(3:ℕ) + (-128:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (256:ℂ)*(X t)^(2:ℕ)*a + (512:ℂ)*a)/((4:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-4:ℂ)*(X t)^(4:ℕ) + (16:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-32:ℂ)*(X t)^(2:ℕ) + (-64:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(10:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(10:ℕ) + (-18:ℂ)*(X t)^(9:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(9:ℕ)*a + (36:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(8:ℕ) + (72:ℂ)*(X t)^(7:ℕ)*a + (-16:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-288:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(6:ℕ) + (-96:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(5:ℕ)*a + (64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (1152:ℂ)*(X t)^(4:ℕ) + (-2304:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (2304:ℂ)*(X t)^(2:ℕ) + (9216:ℂ))/((36:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(7:ℕ)*a + (-4:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (8:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(3:ℕ)*a)/((2:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(6:ℕ) + (-18:ℂ)*(X t)^(5:ℕ)*a + (36:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(4:ℕ) + (72:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-144:ℂ)*(X t)^(3:ℕ)*a + (-144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(2:ℕ) + (-288:ℂ)*(X t)*a + (576:ℂ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((12:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (36:ℂ)*(X t)^(4:ℕ) + (-48:ℂ)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (96:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(2:ℕ) + (192:ℂ)*(Y t)*b + (576:ℂ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(8:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a + (36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-72:ℂ)*(X t)^(6:ℕ) + (144:ℂ)*(X t)^(5:ℕ)*a + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (864:ℂ)*(X t)^(3:ℕ)*a + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (1152:ℂ)*(X t)*a + (-2304:ℂ))/((36:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*a^(3:ℕ) + (-9:ℂ)*(X t)^(8:ℕ)*a + (-18:ℂ)*(X t)^(7:ℕ)*a^(4:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (-72:ℂ)*(X t)^(6:ℕ)*a + (144:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (-144:ℂ)*(X t)^(4:ℕ)*a^(3:ℕ) + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(4:ℕ) + (864:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (1152:ℂ)*(X t)*a^(2:ℕ) + (-2304:ℂ)*a)/((2:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(3:ℕ) + (9:ℂ)*(X t)^(8:ℕ)*a + (18:ℂ)*(X t)^(7:ℕ)*a^(4:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(7:ℕ) + (-36:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (36:ℂ)*(X t)^(6:ℕ)*a + (-216:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (216:ℂ)*(X t)^(5:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (288:ℂ)*(X t)^(4:ℕ)*a^(3:ℕ) + (-288:ℂ)*(X t)^(4:ℕ)*a + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b + (288:ℂ)*(X t)^(3:ℕ)*a^(4:ℕ) + (-1152:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (864:ℂ)*(X t)^(3:ℕ) + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (-576:ℂ)*(X t)^(2:ℕ)*a + (-1152:ℂ)*(X t)*a^(2:ℕ) + (1152:ℂ)*(X t) + (2304:ℂ)*a)/((18:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(8:ℕ) + (2:ℂ)*(X t)^(7:ℕ)*a + (4:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-12:ℂ)*(X t)^(6:ℕ) + (-8:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(4:ℕ) + (32:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ) + (-144:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(4:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-864:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t)^(2:ℕ) + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((36:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*a^(3:ℕ) + (-9:ℂ)*(X t)^(8:ℕ)*a + (-18:ℂ)*(X t)^(7:ℕ)*a^(4:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (-18:ℂ)*(X t)^(7:ℕ) + (36:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (-36:ℂ)*(X t)^(6:ℕ)*a + (216:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-216:ℂ)*(X t)^(5:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (-288:ℂ)*(X t)^(4:ℕ)*a^(3:ℕ) + (288:ℂ)*(X t)^(4:ℕ)*a + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(4:ℕ) + (1152:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (-864:ℂ)*(X t)^(3:ℕ) + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (576:ℂ)*(X t)^(2:ℕ)*a + (1152:ℂ)*(X t)*a^(2:ℕ) + (-1152:ℂ)*(X t) + (-2304:ℂ)*a)/((2:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (-36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(6:ℕ) + (-144:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(4:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-864:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t)^(2:ℕ) + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((36:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(10:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(10:ℕ) + (-18:ℂ)*(X t)^(9:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(9:ℕ)*a + (36:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(8:ℕ) + (72:ℂ)*(X t)^(7:ℕ)*a + (-16:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-288:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(6:ℕ) + (-96:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(5:ℕ)*a + (64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (1152:ℂ)*(X t)^(4:ℕ) + (-2304:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (2304:ℂ)*(X t)^(2:ℕ) + (9216:ℂ))/((36:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*(X t)^(5:ℕ)*a + (8:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*a + (-32:ℂ)*(X t)*a)/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((36:ℂ)*(X t)^(4:ℕ) + (-144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(2:ℕ) + (576:ℂ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(8:ℕ) + (-2:ℂ)*(X t)^(7:ℕ)*a + (-4:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(6:ℕ) + (8:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-16:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ) + (-32:ℂ)*(X t)^(3:ℕ)*a)/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(9:ℕ) + (2:ℂ)*(X t)^(8:ℕ)*a + (4:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (-12:ℂ)*(X t)^(7:ℕ) + (-8:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(6:ℕ)*a + (16:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(5:ℕ) + (64:ℂ)*(X t)^(4:ℕ)*a + (-64:ℂ)*(X t)^(3:ℕ) + (-128:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (256:ℂ)*(X t)^(2:ℕ)*a + (512:ℂ)*a)/((4:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(10:ℕ) + (-72:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (108:ℂ)*(X t)^(8:ℕ) + (72:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (72:ℂ)*(X t)^(7:ℕ)*a + (48:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-144:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (432:ℂ)*(X t)^(6:ℕ) + (-576:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (576:ℂ)*(X t)^(5:ℕ)*a + (64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-192:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (384:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (576:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (384:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (1152:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1152:ℂ)*(X t)^(3:ℕ)*a + (-256:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (768:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-4608:ℂ)*(X t)*a + (9216:ℂ))/((4:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a + (18:ℂ)*(X t)^(7:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(6:ℕ)*a + (-8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (144:ℂ)*(X t)^(4:ℕ)*a + (32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-64:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(3:ℕ) + (-128:ℂ)*(X t)*(Y t)^(2:ℕ) + (384:ℂ)*(X t)*(Y t)*b + (-1152:ℂ)*(X t) + (2304:ℂ)*a)/((2:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(8:ℕ) + (-2:ℂ)*(X t)^(7:ℕ)*a + (-4:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(6:ℕ) + (8:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-16:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ) + (-32:ℂ)*(X t)^(3:ℕ)*a)/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ)*a + (18:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-18:ℂ)*(X t)^(6:ℕ) + (36:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-72:ℂ)*(X t)^(5:ℕ)*a + (-72:ℂ)*(X t)^(4:ℕ)*a^(4:ℕ) + (216:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ) + (-144:ℂ)*(X t)^(3:ℕ)*a + (288:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(2:ℕ))/((2:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-4:ℂ)*(X t)^(4:ℕ) + (16:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-32:ℂ)*(X t)^(2:ℕ) + (-64:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-144:ℂ)*(X t)^(4:ℕ) + (576:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1152:ℂ)*(X t)^(2:ℕ) + (-2304:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((3:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (2:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-6:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (18:ℂ)*(X t)^(6:ℕ) + (-12:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (24:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (24:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-48:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-72:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(4:ℕ) + (48:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (32:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (288:ℂ)*(X t)^(2:ℕ))/((2:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((171:ℂ)*(X t)^(12:ℕ) + (-342:ℂ)*(X t)^(11:ℕ)*a + (-684:ℂ)*(X t)^(10:ℕ)*a^(2:ℕ) + (2052:ℂ)*(X t)^(10:ℕ) + (1368:ℂ)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1368:ℂ)*(X t)^(9:ℕ)*a + (-304:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (912:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (-5472:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (8208:ℂ)*(X t)^(8:ℕ) + (608:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1824:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (-5472:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (5472:ℂ)*(X t)^(7:ℕ)*a + (1216:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3648:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-3648:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (10944:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (10944:ℂ)*(X t)^(6:ℕ)*a^(4:ℕ) + (-21888:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (10944:ℂ)*(X t)^(6:ℕ) + (-2432:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (4864:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (7296:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-21888:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (21888:ℂ)*(X t)^(5:ℕ)*a + (4864:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-14592:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-14592:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (43776:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-43776:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (9728:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (29184:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (-87552:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-19456:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (58368:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-116736:ℂ)*(X t)*(Y t)*a*b)/((576:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (9:ℂ)*(X t)^(6:ℕ) + (36:ℂ)*(X t)^(4:ℕ)*a^(4:ℕ) + (-108:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(4:ℕ) + (-144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(2:ℕ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((171:ℂ)*(X t)^(12:ℕ) + (-342:ℂ)*(X t)^(11:ℕ)*a + (-684:ℂ)*(X t)^(10:ℕ)*a^(2:ℕ) + (2052:ℂ)*(X t)^(10:ℕ) + (1368:ℂ)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1368:ℂ)*(X t)^(9:ℕ)*a + (-304:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (912:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (-5472:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (10944:ℂ)*(X t)^(8:ℕ) + (608:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1824:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (-5472:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (5472:ℂ)*(X t)^(7:ℕ)*a + (1216:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3648:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-3648:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (7296:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (10944:ℂ)*(X t)^(6:ℕ)*a^(4:ℕ) + (-32832:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (32832:ℂ)*(X t)^(6:ℕ) + (-2432:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (4864:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (7296:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-21888:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (21888:ℂ)*(X t)^(5:ℕ)*a + (4864:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-14592:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (14592:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-43776:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (43776:ℂ)*(X t)^(4:ℕ) + (9728:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (29184:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (-87552:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-19456:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-116736:ℂ)*(X t)*(Y t)*a*b)/((576:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-171:ℂ)*(X t)^(12:ℕ) + (342:ℂ)*(X t)^(11:ℕ)*a + (684:ℂ)*(X t)^(10:ℕ)*a^(2:ℕ) + (-2052:ℂ)*(X t)^(10:ℕ) + (-1368:ℂ)*(X t)^(9:ℕ)*a^(3:ℕ) + (1368:ℂ)*(X t)^(9:ℕ)*a + (304:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-912:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (5472:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-8208:ℂ)*(X t)^(8:ℕ) + (-608:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (1824:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (5472:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-5472:ℂ)*(X t)^(7:ℕ)*a + (-1216:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3648:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (3648:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-10944:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-10944:ℂ)*(X t)^(6:ℕ)*a^(4:ℕ) + (21888:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-10944:ℂ)*(X t)^(6:ℕ) + (2432:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-4864:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-7296:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (21888:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (-21888:ℂ)*(X t)^(5:ℕ)*a + (-4864:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (14592:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (14592:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-43776:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (43776:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-9728:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-29184:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (87552:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (19456:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-58368:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (116736:ℂ)*(X t)*(Y t)*a*b)/((576:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-57:ℂ)*(X t)^(8:ℕ) + (76:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (228:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-456:ℂ)*(X t)^(6:ℕ) + (-304:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (608:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-912:ℂ)*(X t)^(4:ℕ) + (1216:ℂ)*(X t)^(2:ℕ)*(Y t)*b)/((12:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (54:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (-81:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (162:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (162:ℂ)*(X t)^(7:ℕ)*a + (-36:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-216:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (648:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-324:ℂ)*(X t)^(6:ℕ) + (-72:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1296:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (1296:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ) + (432:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-576:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-864:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (2592:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (2592:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2592:ℂ)*(X t)^(4:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (288:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-576:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (864:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (2592:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-2592:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(4:ℕ) + (-1152:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (3456:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-5184:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (5184:ℂ)*(X t)^(2:ℕ) + (-1152:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (-10368:ℂ)*(X t)*a + (2304:ℂ)*(Y t)^(2:ℕ) + (41472:ℂ))/((9:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1539:ℂ)*(X t)^(9:ℕ)*a + (342:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2052:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (3078:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (3078:ℂ)*(X t)^(8:ℕ) + (-684:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (2052:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (-18468:ℂ)*(X t)^(7:ℕ)*a + (1368:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (8208:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-24624:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-12312:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (36936:ℂ)*(X t)^(6:ℕ) + (2736:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-8208:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (16416:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (49248:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-73872:ℂ)*(X t)^(5:ℕ)*a + (-608:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (608:ℂ)*(X t)^(4:ℕ)*(Y t)^(4:ℕ) + (-16416:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (21888:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (32832:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-98496:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-98496:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (147744:ℂ)*(X t)^(4:ℕ) + (-3648:ℂ)*(X t)^(3:ℕ)*(Y t)^(3:ℕ)*a*b + (-10944:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (21888:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-98496:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (98496:ℂ)*(X t)^(3:ℕ)*a + (2432:ℂ)*(X t)^(2:ℕ)*(Y t)^(4:ℕ) + (43776:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-131328:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (196992:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-196992:ℂ)*(X t)^(2:ℕ) + (43776:ℂ)*(X t)*(Y t)^(2:ℕ)*a + (393984:ℂ)*(X t)*a + (-87552:ℂ)*(Y t)^(2:ℕ) + (-1575936:ℂ))/((162:ℂ)*(X t)^(2:ℕ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(6:ℕ) + (-4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(4:ℕ) + (16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((76:ℂ)*(X t)^(4:ℕ) + (-304:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (608:ℂ)*(X t)^(2:ℕ) + (1216:ℂ))/((1:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((19:ℂ)*(X t)^(7:ℕ)*a + (-76:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (152:ℂ)*(X t)^(5:ℕ)*a + (152:ℂ)*(X t)^(4:ℕ) + (304:ℂ)*(X t)^(3:ℕ)*a + (-608:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (1216:ℂ)*(X t)^(2:ℕ) + (2432:ℂ))/((2:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(8:ℕ) + (4:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-12:ℂ)*(X t)^(6:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(4:ℕ) + (-64:ℂ)*(X t)^(2:ℕ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-19:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (38:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (76:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-152:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-152:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (304:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (1368:ℂ)*(X t)^(4:ℕ) + (-304:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (608:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5472:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (10944:ℂ)*(X t)^(2:ℕ) + (21888:ℂ))/((2:ℂ)*(Y t)^(2:ℕ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ) + (-3:ℂ)*(X t)^(7:ℕ)*(Y t)*a^(2:ℕ)*b + (-18:ℂ)*(X t)^(6:ℕ)*a + (4:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (12:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(4:ℕ)*b + (-24:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (72:ℂ)*(X t)^(4:ℕ)*a^(3:ℕ) + (-144:ℂ)*(X t)^(4:ℕ)*a + (-16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (-48:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(2:ℕ)*b + (-32:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (-288:ℂ)*(X t)^(2:ℕ)*a + (128:ℂ)*(Y t)^(2:ℕ)*a)/((1:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*(X t)^(8:ℕ) + (-4:ℂ)*(X t)^(6:ℕ)*a^(4:ℕ) + (12:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(6:ℕ) + (-8:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (32:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-64:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (128:ℂ)*(X t)^(2:ℕ) + (-128:ℂ)*(X t)*a + (256:ℂ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(10:ℕ) + (-72:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (108:ℂ)*(X t)^(8:ℕ) + (72:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-72:ℂ)*(X t)^(7:ℕ)*a + (-144:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (432:ℂ)*(X t)^(6:ℕ) + (-576:ℂ)*(X t)^(5:ℕ)*a + (64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (576:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (384:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (1152:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-3456:ℂ)*(X t)^(3:ℕ)*a + (-256:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-4608:ℂ)*(X t)*a + (9216:ℂ))/((36:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(8:ℕ) + (18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a + (-72:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(6:ℕ) + (-144:ℂ)*(X t)^(5:ℕ)*a + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (144:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(4:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-864:ℂ)*(X t)^(3:ℕ)*a + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1152:ℂ)*(X t)*a + (2304:ℂ))/((9:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-3:ℂ)*(X t)^(7:ℕ)*(Y t)*a*b + (-18:ℂ)*(X t)^(6:ℕ) + (12:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-24:ℂ)*(X t)^(5:ℕ)*(Y t)*a*b + (72:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ) + (-48:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(2:ℕ))/((2:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-36:ℂ)*(X t)^(4:ℕ) + (144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(2:ℕ) + (-576:ℂ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((3:ℂ)*(X t)^(8:ℕ)*(Y t)*a*b + (-12:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(3:ℕ)*b + (24:ℂ)*(X t)^(6:ℕ)*(Y t)*a*b + (-8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(4:ℕ)*a + (32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-64:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (1152:ℂ)*(X t)^(2:ℕ)*a + (-128:ℂ)*(X t)*(Y t)^(2:ℕ) + (2304:ℂ)*a)/((2:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(6:ℕ) + (-36:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(4:ℕ) + (144:ℂ)*(X t)^(2:ℕ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(7:ℕ) + (-4:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (12:ℂ)*(X t)^(5:ℕ) + (-8:ℂ)*(X t)^(4:ℕ)*a + (-16:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (48:ℂ)*(X t)^(3:ℕ) + (32:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-64:ℂ)*(X t)^(2:ℕ)*a + (64:ℂ)*(X t) + (-128:ℂ)*a)/((1:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(7:ℕ)*a + (-6:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-18:ℂ)*(X t)^(6:ℕ) + (36:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-72:ℂ)*(X t)^(5:ℕ)*a + (24:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-48:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (72:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-144:ℂ)*(X t)^(4:ℕ) + (-144:ℂ)*(X t)^(3:ℕ)*a + (-96:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(2:ℕ))/((2:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*a + (-2:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ) + (6:ℂ)*(X t)^(7:ℕ)*(Y t)*b + (18:ℂ)*(X t)^(7:ℕ) + (4:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a + (-12:ℂ)*(X t)^(6:ℕ)*(Y t)*a*b + (-36:ℂ)*(X t)^(6:ℕ)*a^(3:ℕ) + (72:ℂ)*(X t)^(6:ℕ)*a + (8:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-24:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (-24:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (48:ℂ)*(X t)^(5:ℕ)*(Y t)*b + (-72:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (144:ℂ)*(X t)^(5:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (48:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (48:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(3:ℕ)*b + (-96:ℂ)*(X t)^(4:ℕ)*(Y t)*a*b + (144:ℂ)*(X t)^(4:ℕ)*a + (32:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (96:ℂ)*(X t)^(3:ℕ)*(Y t)*b + (288:ℂ)*(X t)^(3:ℕ) + (-64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (192:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (-192:ℂ)*(X t)^(2:ℕ)*(Y t)*a*b + (-128:ℂ)*(X t)*(Y t)^(2:ℕ) + (256:ℂ)*(Y t)^(2:ℕ)*a)/((2:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (32:ℂ)*(X t)^(2:ℕ) + (64:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(6:ℕ) + (-4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (12:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (48:ℂ)*(X t)^(2:ℕ) + (64:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-9:ℂ)*(X t)^(8:ℕ) + (-18:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (36:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(6:ℕ) + (72:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-288:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(4:ℕ) + (-96:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-288:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (576:ℂ)*(X t)^(3:ℕ)*a + (64:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (576:ℂ)*(X t)^(2:ℕ) + (1152:ℂ)*(X t)*a + (-2304:ℂ))/((9:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(9:ℕ)*a + (18:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(7:ℕ)*a + (-8:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (16:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (144:ℂ)*(X t)^(5:ℕ)*a + (32:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (96:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(4:ℕ) + (-128:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (384:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-1152:ℂ)*(X t)^(2:ℕ) + (2304:ℂ)*(X t)*a)/((8:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((27:ℂ)*(X t)^(9:ℕ)*a + (-6:ℂ)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (18:ℂ)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-18:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (-54:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (216:ℂ)*(X t)^(7:ℕ)*a + (24:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (72:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-72:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-216:ℂ)*(X t)^(6:ℕ) + (-48:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (144:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-432:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (432:ℂ)*(X t)^(5:ℕ)*a + (-32:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (32:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*b + (-96:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (288:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (864:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-864:ℂ)*(X t)^(4:ℕ) + (-192:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-576:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (1152:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (1728:ℂ)*(X t)^(3:ℕ)*a + (128:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*b + (2304:ℂ)*(X t)*(Y t)*a*b + (-6912:ℂ)*(X t)*a + (-4608:ℂ)*(Y t)*b)/((6:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (9:ℂ)*(X t)^(6:ℕ) + (-4:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-36:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(4:ℕ) + (16:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (144:ℂ)*(X t)^(2:ℕ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(7:ℕ) + (-4:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(5:ℕ) + (-8:ℂ)*(X t)^(4:ℕ)*a + (16:ℂ)*(X t)^(3:ℕ) + (32:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-64:ℂ)*(X t)^(2:ℕ)*a + (-128:ℂ)*a)/((1:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(6:ℕ) + (-36:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(4:ℕ) + (144:ℂ)*(X t)^(2:ℕ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(6:ℕ)*(Y t) + (-3:ℂ)*(X t)^(6:ℕ)*b + (-4:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ) + (8:ℂ)*(X t)^(4:ℕ)*(Y t) + (12:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ)*b + (-24:ℂ)*(X t)^(4:ℕ)*b + (16:ℂ)*(X t)^(2:ℕ)*(Y t) + (-48:ℂ)*(X t)^(2:ℕ)*b)/((1:ℂ)*(Y t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(7:ℕ)*(Y t)^(2:ℕ) + (3:ℂ)*(X t)^(7:ℕ)*(Y t)*b + (-9:ℂ)*(X t)^(7:ℕ) + (2:ℂ)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a + (4:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-12:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (-12:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(2:ℕ)*b + (24:ℂ)*(X t)^(5:ℕ)*(Y t)*b + (36:ℂ)*(X t)^(5:ℕ)*a^(2:ℕ) + (-108:ℂ)*(X t)^(5:ℕ) + (-8:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a + (72:ℂ)*(X t)^(4:ℕ)*a + (16:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (48:ℂ)*(X t)^(3:ℕ)*(Y t)*b + (144:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (-432:ℂ)*(X t)^(3:ℕ) + (32:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a + (-288:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (576:ℂ)*(X t)^(2:ℕ)*a + (-64:ℂ)*(X t)*(Y t)^(2:ℕ) + (-576:ℂ)*(X t) + (1152:ℂ)*a)/((1:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(7:ℕ)*a + (4:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-8:ℂ)*(X t)^(5:ℕ)*a + (-16:ℂ)*(X t)^(3:ℕ)*a)/((2:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (1:ℂ)*(X t)^(8:ℕ) + (4:ℂ)*(X t)^(6:ℕ)*a^(4:ℕ) + (-12:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(6:ℕ) + (-16:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (16:ℂ)*(X t)^(4:ℕ))/((4:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(6:ℕ) + (4:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (2:ℂ)*(X t)^(7:ℕ)*a + (4:ℂ)*(X t)^(5:ℕ)*a^(5:ℕ) + (-16:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(5:ℕ)*a + (8:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (32:ℂ)*(X t)^(3:ℕ)*a + (-32:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (64:ℂ)*(X t)^(2:ℕ) + (128:ℂ))/((2:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(10:ℕ) + (72:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-108:ℂ)*(X t)^(8:ℕ) + (-72:ℂ)*(X t)^(7:ℕ)*a^(3:ℕ) + (144:ℂ)*(X t)^(6:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(6:ℕ) + (288:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (-64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (64:ℂ)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1152:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (1152:ℂ)*(X t)^(4:ℕ) + (-384:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (-1152:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (2304:ℂ)*(X t)^(3:ℕ)*a + (256:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2304:ℂ)*(X t)^(2:ℕ) + (4608:ℂ)*(X t)*a + (-9216:ℂ))/((36:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*(X t)^(5:ℕ)*a + (4:ℂ)*(X t)^(4:ℕ) + (8:ℂ)*(X t)^(3:ℕ)*a^(3:ℕ) + (-16:ℂ)*(X t)^(3:ℕ)*a + (-16:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (32:ℂ)*(X t)^(2:ℕ) + (-32:ℂ)*(X t)*a + (64:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(9:ℕ)*a + (18:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(7:ℕ)*a + (16:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (144:ℂ)*(X t)^(5:ℕ)*a + (96:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (-288:ℂ)*(X t)^(4:ℕ) + (384:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-1152:ℂ)*(X t)^(2:ℕ) + (2304:ℂ)*(X t)*a)/((8:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(10:ℕ)*(Y t)*b + (54:ℂ)*(X t)^(9:ℕ)*a + (72:ℂ)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-108:ℂ)*(X t)^(8:ℕ)*(Y t)*b + (-108:ℂ)*(X t)^(8:ℕ)*a^(2:ℕ) + (-72:ℂ)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (432:ℂ)*(X t)^(7:ℕ)*a + (144:ℂ)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-288:ℂ)*(X t)^(6:ℕ)*(Y t)*b + (-432:ℂ)*(X t)^(6:ℕ) + (-96:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (288:ℂ)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-864:ℂ)*(X t)^(5:ℕ)*a^(3:ℕ) + (864:ℂ)*(X t)^(5:ℕ)*a + (-64:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*a^(2:ℕ)*b + (64:ℂ)*(X t)^(4:ℕ)*(Y t)^(3:ℕ)*b + (-1152:ℂ)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (576:ℂ)*(X t)^(4:ℕ)*(Y t)*b + (1728:ℂ)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1728:ℂ)*(X t)^(4:ℕ) + (-384:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (-1152:ℂ)*(X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (2304:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (3456:ℂ)*(X t)^(3:ℕ)*a + (256:ℂ)*(X t)^(2:ℕ)*(Y t)^(3:ℕ)*b + (4608:ℂ)*(X t)*(Y t)*a*b + (-13824:ℂ)*(X t)*a + (-9216:ℂ)*(Y t)*b)/((12:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)

#print axioms weights_analytic2
end QuantitativeArithmeticSmallLevelNineteenGenericJet201
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet202
theorem weights_analytic2 (X Y Z : ℂ→ℂ) (a b s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s) (hZ : AnalyticAt ℂ Z s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (ha : a≠0) (i : Fin 43) :
    AnalyticAt ℂ (fun t => weights2 (X t) (Y t) (Z t) a b i) s := by
  fin_cases i
  · change AnalyticAt ℂ (fun t => (((-3:ℂ)*(X t)^(4:ℕ)*b + (12:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ)*b + (-24:ℂ)*(X t)^(2:ℕ)*b + (-48:ℂ)*b)/((1:ℂ)*(Y t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-48:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(2:ℕ) + (32:ℂ)*(X t)*(Y t)^(3:ℕ)*a*b + (288:ℂ)*(X t)*(Y t)*a*b + (-192:ℂ)*(Y t)^(2:ℕ) + (-1728:ℂ))/((3:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-144:ℂ)*(X t)^(2:ℕ) + (96:ℂ)*(X t)*(Y t)*a*b + (-576:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((36:ℂ)*(X t)^(4:ℕ) + (-144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(2:ℕ) + (576:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((48:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-288:ℂ)*(X t)*a + (192:ℂ)*(Y t)*b)/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-144:ℂ)*(X t)^(2:ℕ) + (96:ℂ)*(X t)*(Y t)*a*b + (-576:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(4:ℕ) + (-4:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(2:ℕ) + (16:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-8:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (48:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(2:ℕ) + (-192:ℂ))/((3:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((12:ℂ)*(X t)^(2:ℕ) + (-8:ℂ)*(X t)*(Y t)*a*b + (48:ℂ))/((3:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((72:ℂ)*(X t)^(2:ℕ)*a + (-48:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (288:ℂ)*a)/((1:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-24:ℂ)*(X t)^(2:ℕ)*a + (16:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (-96:ℂ)*a)/((3:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-12:ℂ)*(X t)^(2:ℕ) + (8:ℂ)*(X t)*(Y t)*a*b + (-48:ℂ))/((3:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((72:ℂ)*(X t)^(2:ℕ)*a + (-48:ℂ)*(X t)*(Y t)*a^(2:ℕ)*b + (288:ℂ)*a)/((1:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-12:ℂ)*(X t)^(2:ℕ) + (8:ℂ)*(X t)*(Y t)*a*b + (-48:ℂ))/((3:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-8:ℂ)*(X t)^(3:ℕ)*(Y t)*a*b + (48:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-48:ℂ)*(X t)^(2:ℕ) + (-192:ℂ))/((3:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(4:ℕ) + (-4:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(2:ℕ) + (16:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-144:ℂ)*(X t)^(2:ℕ) + (96:ℂ)*(X t)*(Y t)*a*b + (-576:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((48:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-288:ℂ)*(X t)*a + (192:ℂ)*(Y t)*b)/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((36:ℂ)*(X t)^(4:ℕ) + (-144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (288:ℂ)*(X t)^(2:ℕ) + (576:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(4:ℕ) + (-4:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(2:ℕ) + (16:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-19:ℂ)*(X t)^(4:ℕ) + (76:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-152:ℂ)*(X t)^(2:ℕ) + (-304:ℂ))/((1:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-19:ℂ)*(X t)^(4:ℕ) + (76:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-152:ℂ)*(X t)^(2:ℕ) + (-304:ℂ))/((1:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((19:ℂ)*(X t)^(4:ℕ) + (-76:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (152:ℂ)*(X t)^(2:ℕ) + (304:ℂ))/((1:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-48:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-432:ℂ)*(X t)^(2:ℕ) + (32:ℂ)*(X t)*(Y t)^(3:ℕ)*a*b + (288:ℂ)*(X t)*(Y t)*a*b + (-192:ℂ)*(Y t)^(2:ℕ) + (-1728:ℂ))/((3:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((912:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (8208:ℂ)*(X t)^(2:ℕ) + (-608:ℂ)*(X t)*(Y t)^(3:ℕ)*a*b + (-5472:ℂ)*(X t)*(Y t)*a*b + (3648:ℂ)*(Y t)^(2:ℕ) + (32832:ℂ))/((27:ℂ)*(X t)^(2:ℕ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-2:ℂ)*(X t)^(4:ℕ)*a + (8:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-16:ℂ)*(X t)^(2:ℕ)*a + (-32:ℂ)*a)/((1:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-48:ℂ)*(X t)^(2:ℕ) + (32:ℂ)*(X t)*(Y t)*a*b + (-192:ℂ))/((3:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-48:ℂ)*(X t)^(2:ℕ) + (32:ℂ)*(X t)*(Y t)*a*b + (-192:ℂ))/((3:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (4:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(2:ℕ) + (-16:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(5:ℕ)*(Y t)^(2:ℕ) + (-18:ℂ)*(X t)^(4:ℕ)*a + (-4:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(3:ℕ)*(Y t)^(2:ℕ) + (72:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (-144:ℂ)*(X t)^(2:ℕ)*a + (16:ℂ)*(X t)*(Y t)^(2:ℕ) + (-288:ℂ)*a)/((1:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((4:ℂ)*(X t)^(4:ℕ) + (-16:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (32:ℂ)*(X t)^(2:ℕ) + (64:ℂ))/((1:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((2:ℂ)*(X t)^(4:ℕ)*a + (-8:ℂ)*(X t)^(2:ℕ)*a^(3:ℕ) + (16:ℂ)*(X t)^(2:ℕ)*a + (32:ℂ)*a)/((1:ℂ)*(X t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-36:ℂ)*(X t)^(4:ℕ) + (144:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-288:ℂ)*(X t)^(2:ℕ) + (-576:ℂ))/((1:ℂ)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((48:ℂ)*(X t)^(2:ℕ) + (-32:ℂ)*(X t)*(Y t)*a*b + (192:ℂ))/((3:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((12:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-72:ℂ)*(X t)*a + (48:ℂ)*(Y t)*b)/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-32:ℂ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (288:ℂ)*a)/((1:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (4:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(2:ℕ) + (-16:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(4:ℕ) + (-36:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(2:ℕ) + (144:ℂ))/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1:ℂ)*(X t)^(4:ℕ) + (-4:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (8:ℂ)*(X t)^(2:ℕ) + (16:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((48:ℂ)*(X t)^(2:ℕ) + (-32:ℂ)*(X t)*(Y t)*a*b + (192:ℂ))/((3:ℂ)*(X t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1:ℂ)*(X t)^(4:ℕ) + (4:ℂ)*(X t)^(2:ℕ)*a^(2:ℕ) + (-8:ℂ)*(X t)^(2:ℕ) + (-16:ℂ))/((1:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((12:ℂ)*(X t)^(2:ℕ)*(Y t)*b + (-72:ℂ)*(X t)*a + (48:ℂ)*(Y t)*b)/((1:ℂ)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(5:ℕ) + (-36:ℂ)*(X t)^(3:ℕ)*a^(2:ℕ) + (72:ℂ)*(X t)^(3:ℕ) + (144:ℂ)*(X t) + (-32:ℂ)*(Y t)^(2:ℕ)*a*b^(2:ℕ) + (288:ℂ)*a)/((1:ℂ)*(X t)*(Y t)^(2:ℕ)))) s
    fun_prop (disch := simp_all)

#print axioms weights_analytic2
end QuantitativeArithmeticSmallLevelNineteenGenericJet202
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet39
theorem weights_analytic0 (X Y Z : ℂ→ℂ) (a b s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s) (hZ : AnalyticAt ℂ Z s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (ha : a≠0) (i : Fin 33) :
    AnalyticAt ℂ (fun t => weights0 (X t) (Y t) (Z t) a b i) s := by
  fin_cases i
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-486:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((16:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((243:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a*b + (729:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((8:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-243:ℂ)*(X t)^(11:ℕ)*(Y t)^(5:ℕ)*a*b + (-486:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-486:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (-162:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (-162:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-486:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((243:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a*b + (729:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((8:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (486:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-513:ℂ)*(X t)^(10:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (-1539:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((64:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-513:ℂ)*(X t)^(10:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (-1539:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((64:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((513:ℂ)*(X t)^(10:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (1539:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((64:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1539:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (-1026:ℂ)*(X t)^(8:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (6156:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((16:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1539:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (1026:ℂ)*(X t)^(8:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (-6156:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((16:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (162:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (729:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-486:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b + (-324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-972:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a + (-486:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (486:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (-1944:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (11664:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-486:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((243:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a*b + (729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (5832:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-1944:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-3888:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (1458:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-972:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (5832:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((243:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a*b + (729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (486:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-486:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-972:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a*b)/((32:ℂ)))) s
    fun_prop (disch := simp_all)

#print axioms weights_analytic0
end QuantitativeArithmeticSmallLevelNineteenGenericJet39
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet41
theorem weights_analytic0 (X Y Z : ℂ→ℂ) (a b s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s) (hZ : AnalyticAt ℂ Z s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (ha : a≠0) (i : Fin 34) :
    AnalyticAt ℂ (fun t => weights0 (X t) (Y t) (Z t) a b i) s := by
  fin_cases i
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a + (4374:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (5832:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ))/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ))/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (5832:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((512:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1539:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (-3078:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (6156:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((512:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1539:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (-3078:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (6156:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((512:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1539:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a + (3078:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-6156:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a)/((512:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1539:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (-3078:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (342:ℂ)*(X t)^(7:ℕ)*(Y t)^(8:ℕ)*a + (9234:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((64:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1539:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a + (3078:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-342:ℂ)*(X t)^(7:ℕ)*(Y t)^(8:ℕ)*a + (-9234:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((64:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (1458:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (5832:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((256:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a + (-1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((512:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-5832:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (11664:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((512:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-972:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a)/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a + (-1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-972:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)

#print axioms weights_analytic0
end QuantitativeArithmeticSmallLevelNineteenGenericJet41
end

section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace QuantitativeArithmeticSmallLevelNineteenGenericJet43
theorem weights_analytic0 (X Y Z : ℂ→ℂ) (a b s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s) (hZ : AnalyticAt ℂ Z s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (ha : a≠0) (i : Fin 48) :
    AnalyticAt ℂ (fun t => weights0 (X t) (Y t) (Z t) a b i) s := by
  fin_cases i
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(13:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-2916:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ))/((512:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(13:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (972:ℂ)*(X t)^(11:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (1944:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b + (3888:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((512:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (5832:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (648:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (3888:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (972:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b + (5832:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (1944:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (5832:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ))/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (648:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (5832:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (1296:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (3888:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (-324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ))/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(11:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (18:ℂ)*(X t)^(10:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a + (36:ℂ)*(X t)^(9:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-648:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a + (162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-2916:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ))/((32:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (-324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ))/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a + (162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (648:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (5832:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (1296:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (3888:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (5832:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a + (-162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-1458:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (972:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b + (2916:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (1944:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(13:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (729:ℂ)*(X t)^(13:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (972:ℂ)*(X t)^(11:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (-972:ℂ)*(X t)^(11:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (2916:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-5832:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-3888:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((512:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1539:ℂ)*(X t)^(15:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (3078:ℂ)*(X t)^(14:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (6156:ℂ)*(X t)^(13:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (12312:ℂ)*(X t)^(12:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-8208:ℂ)*(X t)^(11:ℕ)*(Y t)^(7:ℕ)*a^(4:ℕ)*b + (8208:ℂ)*(X t)^(11:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (-24624:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (49248:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (32832:ℂ)*(X t)^(9:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b)/((2048:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (1458:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (2916:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (5832:ℂ)*(X t)^(7:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ))/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1539:ℂ)*(X t)^(15:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (3078:ℂ)*(X t)^(14:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (6156:ℂ)*(X t)^(13:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (12312:ℂ)*(X t)^(12:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-8208:ℂ)*(X t)^(11:ℕ)*(Y t)^(7:ℕ)*a^(4:ℕ)*b + (8208:ℂ)*(X t)^(11:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (-24624:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (49248:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (32832:ℂ)*(X t)^(9:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b)/((2048:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1539:ℂ)*(X t)^(15:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-3078:ℂ)*(X t)^(14:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-6156:ℂ)*(X t)^(13:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (-12312:ℂ)*(X t)^(12:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (8208:ℂ)*(X t)^(11:ℕ)*(Y t)^(7:ℕ)*a^(4:ℕ)*b + (-8208:ℂ)*(X t)^(11:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (24624:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-49248:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-32832:ℂ)*(X t)^(9:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b)/((2048:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((1539:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (-1539:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (3078:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (342:ℂ)*(X t)^(9:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (-2052:ℂ)*(X t)^(9:ℕ)*(Y t)^(7:ℕ)*a^(4:ℕ)*b + (2052:ℂ)*(X t)^(9:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (-6156:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (684:ℂ)*(X t)^(8:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (12312:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (1368:ℂ)*(X t)^(7:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (8208:ℂ)*(X t)^(7:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b)/((64:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-1539:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (1539:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-3078:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-342:ℂ)*(X t)^(9:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (2052:ℂ)*(X t)^(9:ℕ)*(Y t)^(7:ℕ)*a^(4:ℕ)*b + (-2052:ℂ)*(X t)^(9:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b + (6156:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-684:ℂ)*(X t)^(8:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (-12312:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-1368:ℂ)*(X t)^(7:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (-8208:ℂ)*(X t)^(7:ℕ)*(Y t)^(7:ℕ)*a^(2:ℕ)*b)/((64:ℂ)*(Z t)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a + (162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (-162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(5:ℕ) + (-729:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-162:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-1458:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-972:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(5:ℕ)*b + (972:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b + (-2916:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (2916:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a + (-648:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-1944:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (1944:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (3888:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b + (11664:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a + (7776:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((256:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((9:ℂ)*(X t)^(12:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (18:ℂ)*(X t)^(11:ℕ)*(Y t)^(8:ℕ)*a^(4:ℕ) + (-162:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (36:ℂ)*(X t)^(10:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (-324:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-648:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((256:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a + (162:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a)/((64:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(13:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-729:ℂ)*(X t)^(13:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (1458:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-972:ℂ)*(X t)^(11:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (972:ℂ)*(X t)^(11:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (5832:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (3888:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((512:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(13:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (729:ℂ)*(X t)^(13:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (972:ℂ)*(X t)^(11:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (-972:ℂ)*(X t)^(11:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (2916:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-3888:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (-11664:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (23328:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (15552:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((512:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (3888:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-81:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a + (-162:ℂ)*(X t)^(7:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-324:ℂ)*(X t)^(6:ℕ)*(Y t)^(6:ℕ)*a)/((16:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-1458:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (972:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b + (-972:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a*b + (2916:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-3888:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a*b)/((256:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-1944:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((81:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ))/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (5832:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (3888:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(11:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (-18:ℂ)*(X t)^(10:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a + (-36:ℂ)*(X t)^(9:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (648:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(12:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (-18:ℂ)*(X t)^(11:ℕ)*(Y t)^(8:ℕ)*a^(4:ℕ) + (162:ℂ)*(X t)^(11:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (-36:ℂ)*(X t)^(10:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (324:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (648:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ))/((256:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-9:ℂ)*(X t)^(11:ℕ)*(Y t)^(8:ℕ)*a^(4:ℕ) + (9:ℂ)*(X t)^(11:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (-18:ℂ)*(X t)^(10:ℕ)*(Y t)^(8:ℕ)*a^(5:ℕ) + (18:ℂ)*(X t)^(10:ℕ)*(Y t)^(8:ℕ)*a^(3:ℕ) + (162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-162:ℂ)*(X t)^(10:ℕ)*(Y t)^(6:ℕ)*a + (-36:ℂ)*(X t)^(9:ℕ)*(Y t)^(8:ℕ)*a^(4:ℕ) + (36:ℂ)*(X t)^(9:ℕ)*(Y t)^(8:ℕ)*a^(2:ℕ) + (324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(4:ℕ) + (-324:ℂ)*(X t)^(9:ℕ)*(Y t)^(6:ℕ)*a^(2:ℕ) + (648:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a^(3:ℕ) + (-648:ℂ)*(X t)^(8:ℕ)*(Y t)^(6:ℕ)*a)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(12:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-1458:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (972:ℂ)*(X t)^(10:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b + (2916:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (1944:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((256:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-1458:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (2916:ℂ)*(X t)^(9:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (-5832:ℂ)*(X t)^(8:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-3888:ℂ)*(X t)^(7:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)
  · change AnalyticAt ℂ (fun t => (((729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(4:ℕ) + (-729:ℂ)*(X t)^(11:ℕ)*(Y t)^(4:ℕ)*a^(2:ℕ) + (2916:ℂ)*(X t)^(10:ℕ)*(Y t)^(4:ℕ)*a^(3:ℕ) + (-972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(4:ℕ)*b + (972:ℂ)*(X t)^(9:ℕ)*(Y t)^(5:ℕ)*a^(2:ℕ)*b + (-1944:ℂ)*(X t)^(8:ℕ)*(Y t)^(5:ℕ)*a^(3:ℕ)*b)/((128:ℂ)))) s
    fun_prop (disch := simp_all)

#print axioms weights_analytic0
end QuantitativeArithmeticSmallLevelNineteenGenericJet43
end
