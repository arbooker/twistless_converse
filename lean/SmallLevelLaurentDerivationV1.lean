module
public import SmallLevelLaurentGermOperationsV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelLaurentDerivation
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm

def binaryRows (p q : Poly) (i : ℕ) : Poly := if i=0 then p else q

/-- A certificate built from initial rows by exact binary Laurent row
operations. There is no division by a polynomial or analytic minor. -/
inductive Derived (sources : ℕ→Poly) (initial : ℕ) : Poly→Prop where
  | source (i : ℕ) (hi : i < initial) : Derived sources initial (sources i)
  | zero : Derived sources initial []
  | combine (p q operation out : Poly)
      (hp : Derived sources initial p) (hq : Derived sources initial q)
      (certificate : substituteCompute (binaryRows p q) operation=out) :
      Derived sources initial out

/-- Kernel-checked arithmetic certificates act on the analytic germs of
the actual input functions, including arbitrary lower-layer pole orders. -/
theorem Derived.germ {sources : ℕ→Poly} {initial : ℕ} {p : Poly}
    (h : Derived sources initial p)
    (X Y Z W : ℂ→ℂ) (a b c s : ℂ) (v : ℂ→ℕ→ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hx : ∀ t,X t≠0) (hy : ∀ t,Y t≠0) (hz : ∀ t,Z t≠0) (hw : ∀ t,W t≠0)
    (hstart : ∀ i, i < initial → HasAnalyticGerm
      (fun z => eval (X z) (Y z) (Z z) (W z) a b c (v z) (sources i)) s) :
    HasAnalyticGerm (fun z => eval (X z) (Y z) (Z z) (W z) a b c (v z) p) s := by
  induction h with
  | source i hi => exact hstart i hi
  | zero => exact HasAnalyticGerm.of_analytic analyticAt_const
  | combine p q operation out hp hq hc ihp ihq =>
    apply SmallLevelLaurentGermOperations.checked_combination_germ
      X Y Z W a b c s v (binaryRows p q) operation out hX hY hZ hW hx hy hz hw
    · intro i
      by_cases hi : i=0
      · simpa [binaryRows,hi] using ihp
      · simpa [binaryRows,hi] using ihq
    · rw [←substituteCompute_eq]
      exact hc

#print axioms Derived.germ
end SmallLevelLaurentDerivation
