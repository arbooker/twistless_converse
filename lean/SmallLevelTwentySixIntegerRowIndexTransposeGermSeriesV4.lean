module
public import SmallLevelIntegerLaurentGermTheoryV4
public import SmallLevelTwentySixIntegerRowIndexTransposeAllSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SmallLevelTwentySixIntegerRow87Transpose
open QuantitativeArithmeticIntegerSevenLaurentRows QuantitativeArithmeticAnalyticGerm

theorem output_germ (X Y Z W A B C : ℂ→ℂ) (s : ℂ) (v : ℂ→ℕ→ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : ∀ t,X t≠0) (hy : ∀ t,Y t≠0) (hz : ∀ t,Z t≠0) (hw : ∀ t,W t≠0)
    (hrows : ∀ i∈List.range 5,HasAnalyticGerm (fun t =>
      eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (inputs i)) s) :
    HasAnalyticGerm (fun t =>
      eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) outputData) s := by
  have hh := SmallLevelIntegerLaurentGerm.weighted_sum_germ X Y Z W A B C s
    (fun t i => eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (inputs i))
    weights (List.range 5) hX hY hZ hW hA hB hC (hx s) (hy s) (hz s) (hw s) hrows
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro t
  exact (output_eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t)
    (hx t) (hy t) (hz t) (hw t)).symm

#print axioms output_germ
end SmallLevelTwentySixIntegerRow87Transpose
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SmallLevelTwentySixIntegerRow89Transpose
open QuantitativeArithmeticIntegerSevenLaurentRows QuantitativeArithmeticAnalyticGerm

theorem output_germ (X Y Z W A B C : ℂ→ℂ) (s : ℂ) (v : ℂ→ℕ→ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : ∀ t,X t≠0) (hy : ∀ t,Y t≠0) (hz : ∀ t,Z t≠0) (hw : ∀ t,W t≠0)
    (hrows : ∀ i∈List.range 5,HasAnalyticGerm (fun t =>
      eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (inputs i)) s) :
    HasAnalyticGerm (fun t =>
      eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) outputData) s := by
  have hh := SmallLevelIntegerLaurentGerm.weighted_sum_germ X Y Z W A B C s
    (fun t i => eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (inputs i))
    weights (List.range 5) hX hY hZ hW hA hB hC (hx s) (hy s) (hz s) (hw s) hrows
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro t
  exact (output_eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t)
    (hx t) (hy t) (hz t) (hw t)).symm

#print axioms output_germ
end SmallLevelTwentySixIntegerRow89Transpose
end
