module
public import QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamilyTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages (primeRate primeRate_analytic primeRate_nonzero)

private theorem matrixHigher_analytic (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) (n : ℕ)
    (X Y Z W : ℂ → ℂ) (V : ℂ → ℕ → ℂ) (s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hX0 : X s≠0) (hY0 : Y s≠0) (hZ0 : Z s≠0) (hW0 : W s≠0)
    (hV : ∀ j, AnalyticAt ℂ (fun z => V z j) s) :
    AnalyticAt ℂ (fun z => matrixHigher r (X z) (Y z) (Z z) (W z) n (V z)) s := by
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  exact ((((((hX.zpow hX0 (n:=r.e₂)).mul (hY.zpow hY0 (n:=r.e₃))).mul
    (hZ.zpow hZ0 (n:=r.e₅))).mul (hW.zpow hW0 (n:=r.e₇))).mul
    analyticAt_const).div analyticAt_const hn).mul (hV r.right)

private theorem ramanujanHigher_analytic (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (ε : ℚ) (n : ℕ)
    (X Y Z W : ℂ → ℂ) (V : ℂ → ℕ → ℂ) (s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hX0 : X s≠0) (hY0 : Y s≠0) (hZ0 : Z s≠0) (hW0 : W s≠0)
    (hV : ∀ j, AnalyticAt ℂ (fun z => V z j) s) :
    AnalyticAt ℂ (fun z => ramanujanHigher r ε (X z) (Y z) (Z z) (W z) n (V z)) s := by
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsum : AnalyticAt ℂ (fun z => QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval r.q r.right (V z)) s := by
    apply Finset.analyticAt_fun_sum
    intro a ha
    exact hV (r.right a)
  exact (((analyticAt_const.mul ((((hX.zpow hX0 (n:=r.e₂)).mul
    (hY.zpow hY0 (n:=r.e₃))).mul (hZ.zpow hZ0 (n:=r.e₅))).mul
    (hW.zpow hW0 (n:=r.e₇)))).mul analyticAt_const).div analyticAt_const hn).mul hsum

theorem formalHigher_analytic (r : Source) (ε : ℚ) (n : ℕ)
    (X Y Z W : ℂ → ℂ) (V : ℂ → ℕ → ℂ) (s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hX0 : X s≠0) (hY0 : Y s≠0) (hZ0 : Z s≠0) (hW0 : W s≠0)
    (hV : ∀ j, AnalyticAt ℂ (fun z => V z j) s) :
    AnalyticAt ℂ (fun z => formalHigher r ε (X z) (Y z) (Z z) (W z) n (V z)) s := by
  cases r with
  | old u =>
    cases u with
    | matrix j => exact matrixHigher_analytic _ n X Y Z W V s hX hY hZ hW hX0 hY0 hZ0 hW0 hV
    | ramanujan j => exact ramanujanHigher_analytic _ ε n X Y Z W V s hX hY hZ hW hX0 hY0 hZ0 hW0 hV
    | hecke j hj => exact analyticAt_const
    | entire j => exact analyticAt_const
  | matrix u hu obs ho => exact matrixHigher_analytic u n X Y Z W V s hX hY hZ hW hX0 hY0 hZ0 hW0 hV
  | ramanujan u hu obs ho => exact ramanujanHigher_analytic u ε n X Y Z W V s hX hY hZ hW hX0 hY0 hZ0 hW0 hV
  | hecke u hu => exact analyticAt_const
  | entire p hp => exact analyticAt_const

theorem topVector_analytic (profile : ℕ → ℚ) (m j : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z => topVector profile (primeRate 2 m z) (primeRate 3 m z)
      (primeRate 5 m z) (primeRate 7 m z) j) s := by
  have hd := physical_denominator_analytic m 0 j s
  have hn := physical_denominator_nonzero m 0 j s
  simp only [Nat.cast_zero,sub_zero] at hd hn
  exact (((hd.inv hn).pow 2).mul analyticAt_const).mul analyticAt_const

theorem topScalar_analytic (r : Source) (ε : ℚ) (profile : ℕ → ℚ)
    (m d : ℕ) (s : ℂ) : AnalyticAt ℂ (topScalar r ε profile m d) s := by
  have h (p : ℝ) : AnalyticAt ℂ (fun z => primeRate p m (z-(d:ℂ))) s :=
    (primeRate_analytic p m _).comp (f:=fun z : ℂ => z-(d:ℂ))
      (analyticAt_id.sub analyticAt_const)
  exact formalHigher_analytic r ε d _ _ _ _ _ s (h 2) (h 3) (h 5) (h 7)
    (primeRate_nonzero _ _ _) (primeRate_nonzero _ _ _)
    (primeRate_nonzero _ _ _) (primeRate_nonzero _ _ _)
    (fun j => topVector_analytic profile m j s)

#print axioms formalHigher_analytic
#print axioms topScalar_analytic
end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
