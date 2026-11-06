module
public meta import QuantitativeArithmeticCompactCommandsV1
public import QuantitativeArithmeticFiniteBlockCheckV1
public import QuantitativeArithmeticCompact26SourceCompilerTheoryV4
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

/-! UNVERIFIED draft. The only concrete arithmetic obligation compares all
1191 symbolic rows against the unchanged original sourceRows data. -/
namespace QuantitativeArithmeticCompact26SourceCompiler
open QuantitativeArithmeticSevenLaurentRows

/-- Instantiate equality's decision procedure before supplying large data. -/
def polyEq (p q : Poly) : Bool := decide (p = q)

theorem polyEq_true {p q : Poly} (h : polyEq p q = true) : p = q :=
  of_decide_eq_true h

def rowVerified (n : Fin 3) (i : Fin 397) : Bool :=
  polyEq (collectCoefficients (polynomial n.val i))
    (collectCoefficients (SmallLevelTwentySixGermDAG.sourceRows (n.val*397+i.val)))

def layerVerified (n : Fin 3) : Bool :=
  (List.finRange 397).all (rowVerified n)

def allRowsVerified : Bool := (List.finRange 3).all layerVerified

def flatRowVerified (i : Fin 1191) : Bool :=
  rowVerified ⟨i.val / 397,by omega⟩ ⟨i.val % 397,by omega⟩

/- Consecutive blocks limit temporary kernel reduction memory. All checks
remain in this single source module and use the same generic soundness lemma. -/
compact_certificate private theorem block0 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 0 32 = true := by decide +kernel
compact_certificate private theorem block1 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 32 32 = true := by decide +kernel
compact_certificate private theorem block2 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 64 32 = true := by decide +kernel
compact_certificate private theorem block3 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 96 32 = true := by decide +kernel
compact_certificate private theorem block4 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 128 32 = true := by decide +kernel
compact_certificate private theorem block5 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 160 32 = true := by decide +kernel
compact_certificate private theorem block6 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 192 32 = true := by decide +kernel
compact_certificate private theorem block7 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 224 32 = true := by decide +kernel
compact_certificate private theorem block8 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 256 32 = true := by decide +kernel
compact_certificate private theorem block9 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 288 32 = true := by decide +kernel
compact_certificate private theorem block10 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 320 32 = true := by decide +kernel
compact_certificate private theorem block11 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 352 32 = true := by decide +kernel
compact_certificate private theorem block12 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 384 32 = true := by decide +kernel
compact_certificate private theorem block13 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 416 32 = true := by decide +kernel
compact_certificate private theorem block14 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 448 32 = true := by decide +kernel
compact_certificate private theorem block15 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 480 32 = true := by decide +kernel
compact_certificate private theorem block16 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 512 32 = true := by decide +kernel
compact_certificate private theorem block17 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 544 32 = true := by decide +kernel
compact_certificate private theorem block18 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 576 32 = true := by decide +kernel
compact_certificate private theorem block19 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 608 32 = true := by decide +kernel
compact_certificate private theorem block20 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 640 32 = true := by decide +kernel
compact_certificate private theorem block21 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 672 32 = true := by decide +kernel
compact_certificate private theorem block22 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 704 32 = true := by decide +kernel
compact_certificate private theorem block23 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 736 32 = true := by decide +kernel
compact_certificate private theorem block24 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 768 32 = true := by decide +kernel
compact_certificate private theorem block25 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 800 32 = true := by decide +kernel
compact_certificate private theorem block26 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 832 32 = true := by decide +kernel
compact_certificate private theorem block27 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 864 32 = true := by decide +kernel
compact_certificate private theorem block28 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 896 32 = true := by decide +kernel
compact_certificate private theorem block29 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 928 32 = true := by decide +kernel
compact_certificate private theorem block30 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 960 32 = true := by decide +kernel
compact_certificate private theorem block31 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 992 32 = true := by decide +kernel
compact_certificate private theorem block32 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 1024 32 = true := by decide +kernel
compact_certificate private theorem block33 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 1056 32 = true := by decide +kernel
compact_certificate private theorem block34 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 1088 32 = true := by decide +kernel
compact_certificate private theorem block35 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 1120 32 = true := by decide +kernel
compact_certificate private theorem block36 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 1152 32 = true := by decide +kernel
compact_certificate private theorem block37 :
    QuantitativeArithmeticFiniteBlockCheck.window flatRowVerified 1184 32 = true := by decide +kernel

private theorem rowVerified_true (i : Fin 1191) : flatRowVerified i = true := by
  apply QuantitativeArithmeticFiniteBlockCheck.blocks_sound («count» := 38)
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
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37

theorem allRowsVerified_true : allRowsVerified = true := by
  apply List.all_eq_true.mpr
  intro n _
  apply List.all_eq_true.mpr
  intro i _
  have hh := rowVerified_true ⟨n.val*397+i.val,by omega⟩
  have hd : (n.val*397+i.val)/397 = n.val := by omega
  have hm : (n.val*397+i.val)%397 = i.val := by omega
  simpa only [flatRowVerified,hd,hm] using hh

theorem compiled_eq_source (n : Fin 3) (i : Fin 397) :
    collectCoefficients (polynomial n.val i) =
      collectCoefficients (SmallLevelTwentySixGermDAG.sourceRows (n.val*397+i.val)) := by
  apply polyEq_true
  have hn : layerVerified n = true :=
    (List.all_eq_true.mp allRowsVerified_true) n (List.mem_finRange n)
  exact (List.all_eq_true.mp hn) i (List.mem_finRange i)

theorem eval_polynomial_eq_sourceRow (n : Fin 3) (i : Fin 397)
    (X Y Z W a b c : ℂ) (v : ℕ → ℂ) :
    eval X Y Z W a b c v (polynomial n.val i) =
      eval X Y Z W a b c v
        (SmallLevelTwentySixGermDAG.sourceRows (n.val*397+i.val)) :=
  eval_eq_of_collectCoefficients_eq X Y Z W a b c v _ _ (compiled_eq_source n i)

#print axioms allRowsVerified_true
#print axioms eval_polynomial_eq_sourceRow
end QuantitativeArithmeticCompact26SourceCompiler
