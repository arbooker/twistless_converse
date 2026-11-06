module

public import QuantitativeArithmeticMeromorphicObservableContinuationV1
public import QuantitativeArithmeticVerticalBoundedTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticTriangularMeromorphicReconstruction. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticTriangularMeromorphicReconstructionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTriangularMeromorphicReconstruction
open Complex Matrix

/-- Forward substitution retains the short triangular certificate instead
of expanding a global inverse. Total division is harmless outside the
half-plane where the pivot nonvanishing is proved. -/
def solve (rhs lead : ℕ → ℂ) (lower : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  (rhs n-∑ j : Fin n, lower n j.val*solve rhs lead lower j.val)/lead n
termination_by n

theorem solve_correct (rhs lead v : ℕ → ℂ) (lower : ℕ → ℕ → ℂ) (D : ℕ)
    (hlead : ∀ n, n<D → lead n≠0)
    (hrow : ∀ n, n<D → lead n*v n=rhs n-∑ j : Fin n, lower n j.val*v j.val)
    (n : ℕ) (hn : n<D) : solve rhs lead lower n=v n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [solve]
    have hs : (∑ j : Fin n, lower n j.val*solve rhs lead lower j.val)=
        ∑ j : Fin n, lower n j.val*v j.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j.val j.isLt (lt_trans j.isLt hn)]
    rw [hs,← hrow n hn]
    exact mul_div_cancel_left₀ _ (hlead n hn)

theorem solve_add (rhs rhs' lead : ℕ → ℂ) (lower : ℕ → ℕ → ℂ) (n : ℕ) :
    solve (rhs+rhs') lead lower n=solve rhs lead lower n+solve rhs' lead lower n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [solve.eq_1 (rhs+rhs') lead lower n,solve.eq_1 rhs lead lower n,solve.eq_1 rhs' lead lower n]
    have hs : (∑ j : Fin n, lower n j.val*solve (rhs+rhs') lead lower j.val)=
        (∑ j : Fin n, lower n j.val*solve rhs lead lower j.val)+
          ∑ j : Fin n, lower n j.val*solve rhs' lead lower j.val := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j.val j.isLt,mul_add]
    rw [hs]
    simp only [Pi.add_apply]
    ring

theorem solve_smul (rhs lead : ℕ → ℂ) (lower : ℕ → ℕ → ℂ) (c : ℂ) (n : ℕ) :
    solve (c • rhs) lead lower n=c*solve rhs lead lower n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [solve.eq_1 (c • rhs) lead lower n,solve.eq_1 rhs lead lower n]
    have hs : (∑ j : Fin n, lower n j.val*solve (c • rhs) lead lower j.val)=
        c*∑ j : Fin n, lower n j.val*solve rhs lead lower j.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j.val j.isLt]
      ring
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

theorem solve_meromorphic (rhs lead : ℂ → ℕ → ℂ) (lower : ℂ → ℕ → ℕ → ℂ)
    (x : ℂ) (hrhs : ∀ n, MeromorphicAt (fun z => rhs z n) x)
    (hlead : ∀ n, MeromorphicAt (fun z => lead z n) x)
    (hlower : ∀ n j, MeromorphicAt (fun z => lower z n j) x) (n : ℕ) :
    MeromorphicAt (fun z => solve (rhs z) (lead z) (lower z) n) x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he : (fun z => solve (rhs z) (lead z) (lower z) n)=
        (fun z => (rhs z n-∑ j : Fin n, lower z n j.val*
          solve (rhs z) (lead z) (lower z) j.val)/lead z n) := by
      funext z
      exact solve.eq_1 _ _ _ _
    rw [he]
    apply MeromorphicAt.div _ (hlead n)
    apply (hrhs n).sub
    apply MeromorphicAt.fun_sum
    intro j _
    exact (hlower n j.val).mul (ih j.val j.isLt)
#print axioms solve_correct
#print axioms solve_add
#print axioms solve_smul
#print axioms solve_meromorphic
end QuantitativeArithmeticTriangularMeromorphicReconstruction
end
end

/-! ## QuantitativeArithmeticTriangularReconstructionMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTriangularMeromorphicReconstruction
open Complex Matrix

def solveLinear (lead : ℕ → ℂ) (lower : ℕ → ℕ → ℂ) (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] ℂ where
  toFun rhs := solve rhs lead lower n
  map_add' rhs rhs' := solve_add rhs rhs' lead lower n
  map_smul' c rhs := solve_smul rhs lead lower c n

theorem solve_finite_rhs {I : Type*} [Fintype I]
    (b : ℕ → I → ℂ) (v : I → ℂ) (lead : ℕ → ℂ) (lower : ℕ → ℕ → ℂ) (n : ℕ) :
    solve (fun k => ∑ j, b k j*v j) lead lower n=
      ∑ j, solve (fun k => b k j) lead lower n*v j := by
  have he : (fun k => ∑ j, b k j*v j)=∑ j, v j • (fun k => b k j) := by
    funext k
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  change solveLinear lead lower n (fun k => ∑ j, b k j*v j)=_
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  exact mul_comm _ _

def reconstructionMatrix {D R : ℕ} (b : ℕ → Fin R → ℂ)
    (lead : ℕ → ℂ) (lower : ℕ → ℕ → ℂ) : Matrix (Fin D) (Fin R) ℂ :=
  fun i j => solve (fun n => b n j) lead lower i.val

theorem reconstruction_action {D R : ℕ} (b : ℕ → Fin R → ℂ)
    (lead : ℕ → ℂ) (lower : ℕ → ℕ → ℂ) (v : Fin R → ℂ) (i : Fin D) :
    (reconstructionMatrix b lead lower *ᵥ v) i=
      solve (fun n => ∑ j, b n j*v j) lead lower i.val :=
  (solve_finite_rhs b v lead lower i.val).symm

/-- Meromorphy of every entry follows by the finite recursion, without
expanding the polynomial/rational expression of any entry. -/
theorem reconstruction_meromorphic {D R : ℕ} (b : ℂ → ℕ → Fin R → ℂ)
    (lead : ℂ → ℕ → ℂ) (lower : ℂ → ℕ → ℕ → ℂ) (x : ℂ)
    (hb : ∀ n j, MeromorphicAt (fun z => b z n j) x)
    (hlead : ∀ n, MeromorphicAt (fun z => lead z n) x)
    (hlower : ∀ n j, MeromorphicAt (fun z => lower z n j) x)
    (i : Fin D) (j : Fin R) :
    MeromorphicAt (fun z => reconstructionMatrix (b z) (lead z) (lower z) i j) x :=
  solve_meromorphic (fun z n => b z n j) lead lower x (fun n => hb n j) hlead hlower i.val

#print axioms solve_finite_rhs
#print axioms reconstruction_action
#print axioms reconstruction_meromorphic
end QuantitativeArithmeticTriangularMeromorphicReconstruction
end
end

/-! ## QuantitativeArithmeticTriangularClearedReconstructionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticTriangularMeromorphicReconstruction
open QuantitativeArithmeticVerticalBounded

theorem solve_cleared (D : ℂ → ℂ) (hD : Bounded D)
    (rhs lead : ℂ → ℕ → ℂ) (lower : ℂ → ℕ → ℕ → ℂ) (d : ℕ)
    (hrhs : ∀ n, Cleared D (fun z => rhs z n))
    (hlead : ∀ n,n<d → Cleared D (fun z => (lead z n)⁻¹))
    (hlower : ∀ n j,Cleared D (fun z => lower z n j)) (n : ℕ) (hn : n<d) :
    Cleared D (fun z => solve (rhs z) (lead z) (lower z) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he : (fun z => solve (rhs z) (lead z) (lower z) n)=
        (fun z => (rhs z n-∑ j : Fin n, lower z n j.val*
          solve (rhs z) (lead z) (lower z) j.val)/lead z n) := by
      funext z
      exact solve.eq_1 _ _ _ _
    rw [he]
    apply Cleared.div _ (hlead n hn)
    apply Cleared.sub hD (hrhs n)
    apply Cleared.sum hD
    intro j _
    exact (hlower n j.val).mul (ih j.val j.isLt (j.isLt.trans hn))

theorem reconstruction_cleared {d r : ℕ} (D : ℂ → ℂ) (hD : Bounded D)
    (b : ℂ → ℕ → Fin r → ℂ) (lead : ℂ → ℕ → ℂ) (lower : ℂ → ℕ → ℕ → ℂ)
    (hb : ∀ n j,Cleared D (fun z => b z n j))
    (hlead : ∀ n,n<d → Cleared D (fun z => (lead z n)⁻¹))
    (hlower : ∀ n j,Cleared D (fun z => lower z n j)) (i : Fin d) (j : Fin r) :
    Cleared D (fun z => reconstructionMatrix (b z) (lead z) (lower z) i j) :=
  solve_cleared D hD (fun z n => b z n j) lead lower d (fun n => hb n j) hlead hlower i.val i.isLt
#print axioms solve_cleared
#print axioms reconstruction_cleared
end QuantitativeArithmeticTriangularMeromorphicReconstruction
end
end
