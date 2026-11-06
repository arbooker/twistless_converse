module
public import QuantitativeArithmeticCompact26SourceCompilerVerificationV1
set_option autoImplicit false
@[expose] public noncomputable section

/-! UNVERIFIED alternate provider. Replace the old SourceMatchAll import;
coimporting both providers would duplicate the original theorem names. -/
namespace SmallLevelTwentySixGermDAG
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticCompact26SourceCompiler

/-- Original source-matching interface, with identical hypotheses. -/
theorem source_rows_match (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : ℕ→ℂ)
    (n : Fin 3) (i : Fin 397) :
    eval X Y Z W a b 1 v (sourceRows (n.val*397+i.val)) =
      replayJetRow n.val X Y Z W a b v i :=
  (eval_polynomial_eq_sourceRow n i X Y Z W a b 1 v).symm.trans
    (eval_polynomial n.val i X Y Z W a b hX hY hZ hW v)

theorem source_rows_match_layer0 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : ℕ→ℂ) (i : Fin 397) :
    eval X Y Z W a b 1 v (sourceRows (0*397+i.val)) =
      replayJetRow 0 X Y Z W a b v i :=
  source_rows_match X Y Z W a b hX hY hZ hW v 0 i

theorem source_rows_match_layer1 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : ℕ→ℂ) (i : Fin 397) :
    eval X Y Z W a b 1 v (sourceRows (1*397+i.val)) =
      replayJetRow 1 X Y Z W a b v i :=
  source_rows_match X Y Z W a b hX hY hZ hW v 1 i

theorem source_rows_match_layer2 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : ℕ→ℂ) (i : Fin 397) :
    eval X Y Z W a b 1 v (sourceRows (2*397+i.val)) =
      replayJetRow 2 X Y Z W a b v i :=
  source_rows_match X Y Z W a b hX hY hZ hW v 2 i

#print axioms source_rows_match
#print axioms source_rows_match_layer0
#print axioms source_rows_match_layer1
#print axioms source_rows_match_layer2
end SmallLevelTwentySixGermDAG
