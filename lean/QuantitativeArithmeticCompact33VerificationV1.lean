module
public meta import QuantitativeArithmeticCompactCommandsV1
public import QuantitativeArithmeticFiniteBlockCheckV1

public import QuantitativeArithmeticCompact33CompilerV1
public import QuantitativeArithmeticSmallLevelThirtyThreeLaurentDataV1

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section

namespace QuantitativeArithmeticCompact33

open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent

/-- The Decidable instance is synthesized once for symbolic arguments,
not by reducing a 775-row concrete proposition during instance search. -/
def polyEq (p q : Poly) : Bool := decide (p=q)

theorem polyEq_true {p q : Poly} (h : polyEq p q=true) : p=q := by
  simpa only [polyEq,decide_eq_true_eq] using h

def rowVerified (i : Fin 775) : Bool :=
  polyEq (normalizeLaurent (compile (sourceKind i))) (sourceRows i)

def allRowsVerified : Bool := (List.finRange 775).all rowVerified

/- Consecutive blocks limit temporary kernel reduction memory. All checks
remain in this single source module and use the same generic soundness lemma. -/
compact_certificate private theorem block0 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 0 32 = true := by decide +kernel
compact_certificate private theorem block1 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 32 32 = true := by decide +kernel
compact_certificate private theorem block2 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 64 32 = true := by decide +kernel
compact_certificate private theorem block3 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 96 32 = true := by decide +kernel
compact_certificate private theorem block4 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 128 32 = true := by decide +kernel
compact_certificate private theorem block5 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 160 32 = true := by decide +kernel
compact_certificate private theorem block6 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 192 32 = true := by decide +kernel
compact_certificate private theorem block7 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 224 32 = true := by decide +kernel
compact_certificate private theorem block8 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 256 32 = true := by decide +kernel
compact_certificate private theorem block9 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 288 32 = true := by decide +kernel
compact_certificate private theorem block10 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 320 32 = true := by decide +kernel
compact_certificate private theorem block11 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 352 32 = true := by decide +kernel
compact_certificate private theorem block12 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 384 32 = true := by decide +kernel
compact_certificate private theorem block13 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 416 32 = true := by decide +kernel
compact_certificate private theorem block14 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 448 32 = true := by decide +kernel
compact_certificate private theorem block15 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 480 32 = true := by decide +kernel
compact_certificate private theorem block16 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 512 32 = true := by decide +kernel
compact_certificate private theorem block17 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 544 32 = true := by decide +kernel
compact_certificate private theorem block18 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 576 32 = true := by decide +kernel
compact_certificate private theorem block19 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 608 32 = true := by decide +kernel
compact_certificate private theorem block20 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 640 32 = true := by decide +kernel
compact_certificate private theorem block21 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 672 32 = true := by decide +kernel
compact_certificate private theorem block22 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 704 32 = true := by decide +kernel
compact_certificate private theorem block23 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 736 32 = true := by decide +kernel
compact_certificate private theorem block24 :
    QuantitativeArithmeticFiniteBlockCheck.window rowVerified 768 32 = true := by decide +kernel

private theorem rowVerified_true (i : Fin 775) : rowVerified i = true := by
  apply QuantitativeArithmeticFiniteBlockCheck.blocks_sound (count := 25)
    (width := 32) (by decide) (by decide) ?_ i
  intro b
  fin_cases b
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24

theorem allRowsVerified_true : allRowsVerified=true := by
  exact List.all_eq_true.mpr (fun i _ => rowVerified_true i)

theorem compiled_eq_source (i : Fin 775) :
    normalizeLaurent (compile (sourceKind i))=sourceRows i := by
  apply polyEq_true
  exact (List.all_eq_true.mp allRowsVerified_true) i (List.mem_finRange i)

#print axioms allRowsVerified_true
#print axioms compiled_eq_source

end QuantitativeArithmeticCompact33
