module
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticAnalyticGermTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelLaurentGermOperations
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm Filter
open scoped Topology

/-- A Laurent linear combination preserves analytic germs when only the
four nonvanishing exponential parameters occur with negative powers. -/
theorem eval_germ (X Y Z W : ℂ→ℂ) (a b c s : ℂ)
    (v : ℂ→ℕ→ℂ) (p : Poly)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0)
    (hv : ∀ i,HasAnalyticGerm (fun t => v t i) s) :
    HasAnalyticGerm (fun t => eval (X t) (Y t) (Z t) (W t) a b c (v t) p) s := by
  induction p with
  | nil => exact HasAnalyticGerm.of_analytic analyticAt_const
  | cons t p ih =>
    have hc : AnalyticAt ℂ (fun z => (t.1 : ℂ) *
        monomial (X z) (Y z) (Z z) (W z) a b c t.2.2) s := analyticAt_const.mul
      (monomial_analytic X Y Z W a b c s t.2.2 hX hY hZ hW hx hy hz hw)
    exact ((hv t.2.1).mul_analytic hc).add ih

/-- A kernel-checked sparse row-operation identity transfers original germ
equations without dividing by a parameter-dependent polynomial minor. -/
theorem checked_combination_germ (X Y Z W : ℂ→ℂ) (a b c s : ℂ)
    (v : ℂ→ℕ→ℂ) (inputs : ℕ→Poly) (operation target : Poly)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hx : ∀ t,X t≠0) (hy : ∀ t,Y t≠0) (hz : ∀ t,Z t≠0) (hw : ∀ t,W t≠0)
    (hrows : ∀ i,HasAnalyticGerm
      (fun t => eval (X t) (Y t) (Z t) (W t) a b c (v t) (inputs i)) s)
    (hcertificate : substitute inputs operation=target) :
    HasAnalyticGerm (fun t => eval (X t) (Y t) (Z t) (W t) a b c (v t) target) s := by
  have hh := eval_germ X Y Z W a b c s
    (fun t i => eval (X t) (Y t) (Z t) (W t) a b c (v t) (inputs i)) operation
    hX hY hZ hW (hx s) (hy s) (hz s) (hw s) hrows
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [←eval_substitute (X t) (Y t) (Z t) (W t) a b c (v t)
    (hx t) (hy t) (hz t) (hw t) inputs operation,hcertificate]

#print axioms eval_germ
#print axioms checked_combination_germ
end SmallLevelLaurentGermOperations
