module
public import QuantitativeArithmeticCompactGermProgramFinalInitialStagesV1
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

def compactBlock029Stage03Code : List Instruction := [
⟨29, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨14, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨29, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨12, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨26, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/81),1,(0,2,0,-2,0,0,0))]⟩,
⟨90, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨5, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨32, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨32, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨53, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨53, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨49, 59, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨26, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨6, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨40, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
⟨6, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/13689),1,(-2,2,1,-2,0,0,0))]⟩
]

def compactBlock029Stage03State : List Poly := program_state% (compactBlock029Stage02State) (compactBlock029Stage03Code)

private theorem compactBlock029Stage03_checked : run compactBlock029Stage02State compactBlock029Stage03Code = compactBlock029Stage03State := by
  decide +kernel

def compactBlock029Stage04Code : List Instruction := [
⟨89, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨7, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨98, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨8, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨50, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
⟨7, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨7, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨15, 10, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨8, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨8, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨8, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨8, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨8, 15, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨64, 77, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨111, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨127, 107, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩
]

def compactBlock029Stage04State : List Poly := program_state% (compactBlock029Stage03State) (compactBlock029Stage04Code)

private theorem compactBlock029Stage04_checked : run compactBlock029Stage03State compactBlock029Stage04Code = compactBlock029Stage04State := by
  decide +kernel

def compactBlock029Stage05Code : List Instruction := [
⟨116, 123, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨67, 81, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨120, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨99, 83, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨89, 84, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨87, 85, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨87, 86, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨90, 87, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨73, 88, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨19, 89, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨97, 90, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨99, 91, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨101, 92, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨105, 93, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨104, 94, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨106, 95, [((-1),0,(0,0,0,0,0,0,0))]⟩
]

def compactBlock029Stage05State : List Poly := program_state% (compactBlock029Stage04State) (compactBlock029Stage05Code)

private theorem compactBlock029Stage05_checked : run compactBlock029Stage04State compactBlock029Stage05Code = compactBlock029Stage05State := by
  decide +kernel

def compactBlock029Prefix06Code : List Instruction := (((compactBlock029Prefix03Code ++ compactBlock029Stage03Code) ++ compactBlock029Stage04Code) ++ compactBlock029Stage05Code)

theorem compactBlock029Prefix06_checked : run compactBlock029Inputs compactBlock029Prefix06Code = compactBlock029Stage05State := by
  exact run_append_of_results (run_append_of_results (run_append_of_results (compactBlock029Prefix03_checked) compactBlock029Stage03_checked) compactBlock029Stage04_checked) compactBlock029Stage05_checked

#print axioms compactBlock029Prefix06_checked

}
end SmallLevelTwentySixGermDAG
end
