module
public import SmallLevelLaurentGermOperationsV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelLaurentVariableGerm
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm

/-- The last three parameters occur only to natural powers and may vanish. -/
theorem monomial_analytic (X Y Z W A B C : ℂ→ℂ) (s : ℂ) (e : Exponent)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0) :
    AnalyticAt ℂ (fun t => monomial (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) e) s := by
  unfold monomial
  exact ((((((hX.zpow hx).mul (hY.zpow hy)).mul (hZ.zpow hz)).mul
    (hW.zpow hw)).mul (hA.pow _)).mul (hB.pow _)).mul (hC.pow _)

theorem eval_germ (X Y Z W A B C : ℂ→ℂ) (s : ℂ)
    (v : ℂ→ℕ→ℂ) (p : Poly)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0)
    (hv : ∀ i,HasAnalyticGerm (fun t => v t i) s) :
    HasAnalyticGerm (fun t => eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) p) s := by
  induction p with
  | nil => exact HasAnalyticGerm.of_analytic analyticAt_const
  | cons t p ih =>
    have hc : AnalyticAt ℂ (fun z => (t.1:ℂ)*
        monomial (X z) (Y z) (Z z) (W z) (A z) (B z) (C z) t.2.2) s :=
      analyticAt_const.mul (monomial_analytic X Y Z W A B C s t.2.2
        hX hY hZ hW hA hB hC hx hy hz hw)
    exact ((hv t.2.1).mul_analytic hc).add ih

/-- A polynomial lower-column syzygy acts on germs even where its
computation used a vanishing minor. Only the final polynomial identity
is required; no division by that minor enters the analytic statement. -/
theorem checked_combination_germ (X Y Z W A B C : ℂ→ℂ) (s : ℂ)
    (v : ℂ→ℕ→ℂ) (inputs : ℕ→Poly) (operation target : Poly)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : ∀ t,X t≠0) (hy : ∀ t,Y t≠0) (hz : ∀ t,Z t≠0) (hw : ∀ t,W t≠0)
    (hrows : ∀ i,HasAnalyticGerm
      (fun t => eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (inputs i)) s)
    (hcertificate : substituteCompute inputs operation=target) :
    HasAnalyticGerm (fun t => eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) target) s := by
  have hh := eval_germ X Y Z W A B C s
    (fun t i => eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (inputs i)) operation
    hX hY hZ hW hA hB hC (hx s) (hy s) (hz s) (hw s) hrows
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [←eval_substitute (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t)
    (hx t) (hy t) (hz t) (hw t) inputs operation,←substituteCompute_eq,hcertificate]

#print axioms checked_combination_germ
end SmallLevelLaurentVariableGerm
