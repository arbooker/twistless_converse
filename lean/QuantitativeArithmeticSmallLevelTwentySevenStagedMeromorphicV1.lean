module
public import QuantitativeArithmeticSmallLevelTwentySevenStagedReconstructionV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticTriangularMeromorphicReconstruction Matrix

/-- All entries of the actual staged reconstruction matrix are meromorphic.
The finite recursion is used directly; no large rational inverse is expanded. -/
theorem staged_left_meromorphic (x y z w a b c : ℂ → ℂ) (s : ℂ)
    (hx : MeromorphicAt x s) (hy : MeromorphicAt y s) (hz : MeromorphicAt z s)
    (hw : MeromorphicAt w s) (ha : MeromorphicAt a s) (hb : MeromorphicAt b s)
    (hc : MeromorphicAt c s) (i : Fin 321) (j : Fin 550) :
    MeromorphicAt (fun t => stagedLeftMatrix (x t) (y t) (z t) (w t) (a t) (b t) (c t) i j) s := by
  have hcoef (p : Poly) (k : ℕ) := coefficient_meromorphic x y z w a b c s hx hy hz hw ha hb hc p k
  have hlead (n : ℕ) : MeromorphicAt (fun t => stageLead (x t) (y t) (z t) (w t) (a t) (b t) (c t) n) s :=
    hcoef (certificate n) (550+n)
  have hlower (n k : ℕ) : MeromorphicAt (fun t => stageLower (x t) (y t) (z t) (w t) (a t) (b t) (c t) n k) s :=
    hcoef (certificate n) (550+k)
  have hrhs (n : ℕ) (k : Fin 550) :
      MeromorphicAt (fun t => stageRhsMatrix (x t) (y t) (z t) (w t) (a t) (b t) (c t) n k) s := by
    by_cases hn : n=k.val
    · simpa only [stageRhsMatrix,ite_eq_left hn,stageSource] using (hcoef (certificate n) n).fun_neg
    · simpa only [stageRhsMatrix,ite_eq_right hn] using (MeromorphicAt.const (0:ℂ) s)
  change MeromorphicAt (fun t => ∑ k : Fin 550,
    outputFactor (x t) (y t) (z t) (w t) (a t) (b t) (c t) i k*
      reconstructionMatrix (stageRhsMatrix (x t) (y t) (z t) (w t) (a t) (b t) (c t))
        (stageLead (x t) (y t) (z t) (w t) (a t) (b t) (c t))
        (stageLower (x t) (y t) (z t) (w t) (a t) (b t) (c t)) k j) s
  apply MeromorphicAt.fun_sum
  intro k _
  apply MeromorphicAt.mul
  · exact (hcoef (certificate (550+i.val)) (550+k.val)).neg.div (hlead (550+i.val))
  · exact reconstruction_meromorphic _ _ _ s hrhs hlead hlower k j
#print axioms staged_left_meromorphic
end QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
