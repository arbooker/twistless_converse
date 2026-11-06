module

public import QuantitativeArithmeticIntegerSevenLaurentRowsTheoryV4
public import SmallLevelLaurentVariableGermV1

/-! Consolidated chapter: SmallLevelIntegerLaurentGerm. Original declarations and local scopes are retained. -/

/-! ## SmallLevelIntegerLaurentGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelIntegerLaurentGerm
open QuantitativeArithmeticAnalyticGerm

def toRat (p : QuantitativeArithmeticIntegerSevenLaurentRows.Poly) :
    QuantitativeArithmeticSevenLaurentRows.Poly :=
  p.map fun t => ((t.1:ℚ),t.2.1,t.2.2)

theorem eval_toRat (X Y Z W A B C : ℂ) (v : ℕ→ℂ)
    (p : QuantitativeArithmeticIntegerSevenLaurentRows.Poly) :
    QuantitativeArithmeticSevenLaurentRows.eval X Y Z W A B C v (toRat p)=
      QuantitativeArithmeticIntegerSevenLaurentRows.eval X Y Z W A B C v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [toRat,List.map_cons,QuantitativeArithmeticSevenLaurentRows.eval_cons,
      QuantitativeArithmeticIntegerSevenLaurentRows.eval_cons] at *
    rw [ih]
    norm_cast

/-- Clearing rational denominators permits integer arithmetic in the
finite checker, while retaining the same analytic-germ semantics. -/
theorem balanced_combination_germ (X Y Z W A B C : ℂ→ℂ) (s : ℂ)
    (v : ℂ→ℕ→ℂ) (inputs : ℕ→QuantitativeArithmeticIntegerSevenLaurentRows.Poly)
    (operation target : QuantitativeArithmeticIntegerSevenLaurentRows.Poly) (n : ℕ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : ∀ t,X t≠0) (hy : ∀ t,Y t≠0) (hz : ∀ t,Z t≠0) (hw : ∀ t,W t≠0)
    (hrows : ∀ i,HasAnalyticGerm (fun t =>
      QuantitativeArithmeticIntegerSevenLaurentRows.eval
        (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (inputs i)) s)
    (hcertificate : QuantitativeArithmeticIntegerSevenLaurentRows.substituteBalanced
      n inputs operation=target) :
    HasAnalyticGerm (fun t => QuantitativeArithmeticIntegerSevenLaurentRows.eval
      (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) target) s := by
  have hh := SmallLevelLaurentVariableGerm.eval_germ X Y Z W A B C s
    (fun t i => QuantitativeArithmeticIntegerSevenLaurentRows.eval
      (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (inputs i)) (toRat operation)
    hX hY hZ hW hA hB hC (hx s) (hy s) (hz s) (hw s) hrows
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [eval_toRat,←QuantitativeArithmeticIntegerSevenLaurentRows.eval_substituteBalanced
    (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t)
    (hx t) (hy t) (hz t) (hw t) n inputs operation,hcertificate]

#print axioms eval_toRat
#print axioms balanced_combination_germ
end SmallLevelIntegerLaurentGerm
end
end

/-! ## SmallLevelIntegerLaurentSourceGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelIntegerLaurentGerm
open QuantitativeArithmeticAnalyticGerm

/-- An exact denominator-clearing binding transfers an original rational
row germ to the integer row used by the finite certificate checker. -/
theorem scaled_source_germ (X Y Z W A B C : ℂ→ℂ) (s : ℂ) (v : ℂ→ℕ→ℂ)
    (p : QuantitativeArithmeticIntegerSevenLaurentRows.Poly)
    (q : QuantitativeArithmeticSevenLaurentRows.Poly) (r : ℚ)
    (hx : ∀ t,X t≠0) (hy : ∀ t,Y t≠0) (hz : ∀ t,Z t≠0) (hw : ∀ t,W t≠0)
    (hbinding : toRat p=QuantitativeArithmeticSevenLaurentRows.shift r (0,0,0,0,0,0,0) q)
    (hq : HasAnalyticGerm (fun t => QuantitativeArithmeticSevenLaurentRows.eval
      (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) q) s) :
    HasAnalyticGerm (fun t => QuantitativeArithmeticIntegerSevenLaurentRows.eval
      (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) p) s := by
  have hh := hq.mul_analytic (show AnalyticAt ℂ (fun _ : ℂ => (r:ℂ)) s from analyticAt_const)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [←eval_toRat,hbinding,QuantitativeArithmeticSevenLaurentRows.eval_shift
    (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) (hx t) (hy t) (hz t) (hw t)]
  simp [QuantitativeArithmeticSevenLaurentRows.monomial]

#print axioms scaled_source_germ
end SmallLevelIntegerLaurentGerm
end
end

/-! ## SmallLevelIntegerLaurentWeightedGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelIntegerLaurentGerm
open QuantitativeArithmeticIntegerSevenLaurentRows QuantitativeArithmeticAnalyticGerm

theorem eval_analytic (X Y Z W A B C : ℂ→ℂ) (s : ℂ)
    (v : ℂ→ℕ→ℂ) (p : Poly)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0)
    (hv : ∀ i,AnalyticAt ℂ (fun t => v t i) s) :
    AnalyticAt ℂ (fun t => eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (v t) p) s := by
  induction p with
  | nil => exact analyticAt_const
  | cons t p ih =>
    have hm := SmallLevelLaurentVariableGerm.monomial_analytic X Y Z W A B C s t.2.2
      hX hY hZ hW hA hB hC hx hy hz hw
    exact ((analyticAt_const.mul hm).mul (hv t.2.1)).add ih

/-- A finite polynomial-weighted combination of analytic germs remains
analytic. Its coefficients may vanish; no pivot denominator is introduced. -/
theorem weighted_sum_germ (X Y Z W A B C : ℂ→ℂ) (s : ℂ)
    (rows : ℂ→ℕ→ℂ) (weights : ℕ→Poly) (indices : List ℕ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0)
    (hrows : ∀ i∈indices,HasAnalyticGerm (fun t => rows t i) s) :
    HasAnalyticGerm (fun t => (indices.map fun i =>
      eval (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) (fun _ => 1) (weights i)*
        rows t i).sum) s := by
  induction indices with
  | nil => exact HasAnalyticGerm.of_analytic analyticAt_const
  | cons i indices ih =>
    have hi := hrows i (by simp)
    have ht := ih (fun j hj => hrows j (by simp [hj]))
    exact (hi.mul_analytic (eval_analytic X Y Z W A B C s (fun _ _ => 1)
      (weights i) hX hY hZ hW hA hB hC hx hy hz hw (fun _ => analyticAt_const))).add ht

#print axioms eval_analytic
#print axioms weighted_sum_germ
end SmallLevelIntegerLaurentGerm
end
end
