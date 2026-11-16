module
public import QuantitativeArithmeticCompactGermProgramFinalMiddleStagesV1
public meta import SmallLevelLaurentProgramStateDataV1
public import SmallLevelLaurentProgramCompositionV1
public meta import SmallLevelCertificateBatchCommandV1
public meta import QuantitativeArithmeticLaurentProgramDataV4
public import QuantitativeArithmeticLaurentProgramTheoryV4
public import SmallLevelTwentySixGermDAGSourceRowsV1
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
/-! The program is the certificate data. Intermediate outputs are regenerated
at elaboration and checked by each original block equation below. Final raw-row
identifications remain independent kernel checks in the consuming module. -/
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace SmallLevelTwentySixGermDAG
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation
open QuantitativeArithmeticLaurentProgram
certificate_batch {

def compactBlock029Stage06Code : List Instruction := [
⟨109, 96, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨111, 97, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨113, 98, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨116, 99, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨142, 100, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨50, 101, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨50, 102, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨50, 103, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨33, 104, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨33, 105, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨33, 106, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨111, 107, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨68, 108, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨26, 109, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨144, 110, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨158, 111, [((-1),0,(0,0,0,0,0,0,0))]⟩
]

def compactBlock029Stage06State : List Poly := program_state% (compactBlock029Stage05State) (compactBlock029Stage06Code)

private theorem compactBlock029Stage06_checked : run compactBlock029Stage05State compactBlock029Stage06Code = compactBlock029Stage06State := by
  decide +kernel

def compactBlock029Stage07Code : List Instruction := [
⟨161, 112, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨158, 113, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨160, 114, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨99, 115, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨99, 116, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨38, 117, [((-1),0,(0,0,0,0,0,0,0))]⟩
]

def compactBlock029Stage07State : List Poly := program_state% (compactBlock029Stage06State) (compactBlock029Stage07Code)

private theorem compactBlock029Stage07_checked : run compactBlock029Stage06State compactBlock029Stage07Code = compactBlock029Stage07State := by
  decide +kernel

theorem compactBlock029_certificate : outputs compactBlock029Inputs compactBlock029Program compactBlock029Indices = compactBlock029Results := by
  apply outputs_of_run_result (last := compactBlock029Stage07State)
  · change run compactBlock029Inputs ((compactBlock029Prefix06Code ++ compactBlock029Stage06Code) ++ compactBlock029Stage07Code) = _
    exact run_append_of_results (run_append_of_results compactBlock029Prefix06_checked compactBlock029Stage06_checked) compactBlock029Stage07_checked
  · decide +kernel

theorem compactBlock029_derived : ∀ p ∈ compactBlock029Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock029_inputs compactBlock029Program compactBlock029Indices compactBlock029_certificate

#print axioms compactBlock029_derived

}
end SmallLevelTwentySixGermDAG
end
