module
public import QuantitativeArithmeticTriangularMeromorphicReconstructionTheoryV4
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTriangularMeromorphicReconstruction
open Complex Matrix

/-- Only the pivots actually used by the finite recursion must be nonzero. -/
theorem solve_analytic (rhs lead : ℂ → ℕ → ℂ) (lower : ℂ → ℕ → ℕ → ℂ)
    (x : ℂ) (D : ℕ) (hrhs : ∀ n, AnalyticAt ℂ (fun z => rhs z n) x)
    (hlead : ∀ n, AnalyticAt ℂ (fun z => lead z n) x)
    (hlower : ∀ n j, AnalyticAt ℂ (fun z => lower z n j) x)
    (hne : ∀ n, n<D → lead x n≠0) (n : ℕ) (hn : n<D) :
    AnalyticAt ℂ (fun z => solve (rhs z) (lead z) (lower z) n) x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he : (fun z => solve (rhs z) (lead z) (lower z) n)=
        (fun z => (rhs z n-∑ j : Fin n, lower z n j.val*
          solve (rhs z) (lead z) (lower z) j.val)/lead z n) := by
      funext z
      exact solve.eq_1 _ _ _ _
    rw [he]
    apply AnalyticAt.div _ (hlead n) (hne n hn)
    apply (hrhs n).sub
    apply Finset.analyticAt_fun_sum
    intro j _
    exact (hlower n j.val).mul (ih j.val j.isLt (lt_trans j.isLt hn))

theorem reconstruction_analytic {D R : ℕ} (b : ℂ → ℕ → Fin R → ℂ)
    (lead : ℂ → ℕ → ℂ) (lower : ℂ → ℕ → ℕ → ℂ) (x : ℂ)
    (hb : ∀ n j, AnalyticAt ℂ (fun z => b z n j) x)
    (hlead : ∀ n, AnalyticAt ℂ (fun z => lead z n) x)
    (hlower : ∀ n j, AnalyticAt ℂ (fun z => lower z n j) x)
    (hne : ∀ n, n<D → lead x n≠0) (i : Fin D) (j : Fin R) :
    AnalyticAt ℂ (fun z => reconstructionMatrix (b z) (lead z) (lower z) i j) x :=
  solve_analytic (fun z n => b z n j) lead lower x D (fun n => hb n j)
    hlead hlower hne i.val i.isLt
#print axioms solve_analytic
#print axioms reconstruction_analytic
end QuantitativeArithmeticTriangularMeromorphicReconstruction

namespace QuantitativeArithmeticSevenLaurentRows

theorem coefficient_analytic (X Y Z W : ℂ → ℂ) (a b c s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0) (p : Poly) (j : ℕ) :
    AnalyticAt ℂ (fun t => coefficient (X t) (Y t) (Z t) (W t) a b c p j) s := by
  simp_rw [coefficient_project]
  exact eval_analytic X Y Z W a b c s (fun _ _ => 1) (coordinatePolynomial p j)
    hX hY hZ hW hx hy hz hw (fun _ => analyticAt_const)
#print axioms coefficient_analytic
end QuantitativeArithmeticSevenLaurentRows
