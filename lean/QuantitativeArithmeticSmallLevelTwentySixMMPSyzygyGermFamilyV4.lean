module
public import QuantitativeArithmeticAnalyticGermTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixMMPMultiplierAnalyticFamilyV4
public import SmallLevelTwentySixMMPPariTheoryV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace QuantitativeArithmeticSmallLevelTwentySixMMPSyzygyGerm6
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive
open QuantitativeArithmeticSmallLevelTwentySixMMPMultiplierAnalytic6
open SmallLevelTwentySixMMPPari

/-- Polynomial syzygies preserve analyticity of the actual row germs,
including at zeros of their multiplier q. No division by q is performed. -/
theorem constraint_germ (X Y Z W A B : ℂ → ℂ) (V : ℂ → ℕ → ℂ) (s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s)
    (hg : ∀ i : Fin 12, HasAnalyticGerm (fun z =>
      eval (X z) (Y z) (Z z) (W z) (A z) (B z) 1 (V z) (primitiveRows i)) s) :
    HasAnalyticGerm (fun z => constraint6 (X z) (Y z) (Z z) (W z) (A z) (B z) (V z)) s := by
  have h := (((((hg 6).mul_analytic (multiplier0_analytic X Y Z W A B s hX hY hZ hW hA hB)).sub
    ((hg 8).mul_analytic (multiplier2_analytic X Y Z W A B s hX hY hZ hW hA hB))).sub
    ((hg 9).mul_analytic (multiplier4_analytic X Y Z W A B s hX hY hZ hW hA hB))).sub
    ((hg 10).mul_analytic (multiplier6_analytic X Y Z W A B s hX hY hZ hW hA hB))).sub
    ((hg 11).mul_analytic (multiplier8_analytic X Y Z W A B s hX hY hZ hW hA hB))
  apply h.congr
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  linear_combination syzygy6 (X z) (Y z) (Z z) (W z) (A z) (B z) (V z)

#print axioms constraint_germ
end QuantitativeArithmeticSmallLevelTwentySixMMPSyzygyGerm6
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

namespace QuantitativeArithmeticSmallLevelTwentySixMMPSyzygyGerm7
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive
open QuantitativeArithmeticSmallLevelTwentySixMMPMultiplierAnalytic7
open SmallLevelTwentySixMMPPari

/-- Polynomial syzygies preserve analyticity of the actual row germs,
including at zeros of their multiplier q. No division by q is performed. -/
theorem constraint_germ (X Y Z W A B : ℂ → ℂ) (V : ℂ → ℕ → ℂ) (s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s)
    (hg : ∀ i : Fin 12, HasAnalyticGerm (fun z =>
      eval (X z) (Y z) (Z z) (W z) (A z) (B z) 1 (V z) (primitiveRows i)) s) :
    HasAnalyticGerm (fun z => constraint7 (X z) (Y z) (Z z) (W z) (A z) (B z) (V z)) s := by
  have h := (((((hg 7).mul_analytic (multiplier0_analytic X Y Z W A B s hX hY hZ hW hA hB)).sub
    ((hg 8).mul_analytic (multiplier2_analytic X Y Z W A B s hX hY hZ hW hA hB))).sub
    ((hg 9).mul_analytic (multiplier4_analytic X Y Z W A B s hX hY hZ hW hA hB))).sub
    ((hg 10).mul_analytic (multiplier6_analytic X Y Z W A B s hX hY hZ hW hA hB))).sub
    ((hg 11).mul_analytic (multiplier8_analytic X Y Z W A B s hX hY hZ hW hA hB))
  apply h.congr
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  linear_combination syzygy7 (X z) (Y z) (Z z) (W z) (A z) (B z) (V z)

#print axioms constraint_germ
end QuantitativeArithmeticSmallLevelTwentySixMMPSyzygyGerm7
end
