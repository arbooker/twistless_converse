module
public import QuantitativeArithmeticCompactGermProgramPenultimateBlocksV1
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

def compactBlock029Inputs : List Poly := [node1191, node5956, node5960, node6018, node6120, node6124, node7103, node7201, node7202, node7210, node7295, node7296, node7297, node7298, node7313, node7318, node7321, node7322, node7328, node7331, node7344, node7371, node7378, node7379, node7382, node7384, node7387, node7388, node7389, node7394, node7395, node7397, node7398, node7401, node7403, node7405, node7408, node7410, node7412, node7413, node7414, node7420, node7432, node7434, node7436, node7442, node7444, node7446, node7447, node7448, node7449, node7450, node7453, node7454, node7455, node7460, node7463, node7464, node7465, node7466, node7467, node7468, node7470, node7471, node7472, node7473, node7475, node7476, node7478, node7479]

theorem compactBlock029_inputs : ∀ p ∈ compactBlock029Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node1191, node5956, node5960, node6018, node6120, node6124, node7103, node7201, node7202, node7210, node7295, node7296, node7297, node7298, node7313, node7318, node7321, node7322, node7328, node7331, node7344, node7371, node7378, node7379, node7382, node7384, node7387, node7388, node7389, node7394, node7395, node7397, node7398, node7401, node7403, node7405, node7408, node7410, node7412, node7413, node7414, node7420, node7432, node7434, node7436, node7442, node7444, node7446, node7447, node7448, node7449, node7450, node7453, node7454, node7455, node7460, node7463, node7464, node7465, node7466, node7467, node7468, node7470, node7471, node7472, node7473, node7475, node7476, node7478, node7479], Derived sourceRows 1191 p
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock028_derived 57)
  exact nil_derived _ _

def compactBlock029Program : List Instruction := [
  ⟨62, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨64, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨34, 71, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨43, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨46, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨30, 6, [((-169/40000),0,(3,0,-1,2,0,0,0))]⟩,
  ⟨76, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨69, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 2, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨7, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨34, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨77, 5, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨42, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨49, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨81, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨83, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨11, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨62, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨40, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨75, 11, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨10, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨44, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨11, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨80, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨82, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨84, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨57, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨87, 19, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨69, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨90, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨11, 31, [((81/625),0,(0,-2,0,2,0,0,0))]⟩,
  ⟨83, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨25, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨33, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨3, 36, [((-625/676),0,(1,0,1,-2,0,0,0))]⟩,
  ⟨43, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-676/625),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨58, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨14, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨67, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨93, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨60, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨96, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨63, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨99, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨96, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨16, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
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
  ((-10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
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
  (1,1,(0,0,0,0,0,0,0))]⟩,
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
  ⟨106, 95, [((-1),0,(0,0,0,0,0,0,0))]⟩,
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
  ⟨158, 111, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 112, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨158, 113, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨160, 114, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨99, 115, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨99, 116, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨38, 117, [((-1),0,(0,0,0,0,0,0,0))]⟩
]

















































































































def compactBlock029Indices : List ℕ := [91, 90, 89, 88, 82, 77, 76, 75, 74, 73, 72, 71, 70, 64, 49, 44, 43, 42, 41, 38, 37, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock029Results : List Poly :=
  program_results% (compactBlock029Inputs) (compactBlock029Program) (compactBlock029Indices)

def node7511 : Poly := rowAt compactBlock029Results 0
def node7512 : Poly := rowAt compactBlock029Results 1
def node7513 : Poly := rowAt compactBlock029Results 2
def node7514 : Poly := rowAt compactBlock029Results 3
def node7521 : Poly := rowAt compactBlock029Results 4
def node7527 : Poly := rowAt compactBlock029Results 5
def node7528 : Poly := rowAt compactBlock029Results 6
def node7529 : Poly := rowAt compactBlock029Results 7
def node7530 : Poly := rowAt compactBlock029Results 8
def node7531 : Poly := rowAt compactBlock029Results 9
def node7532 : Poly := rowAt compactBlock029Results 10
def node7535 : Poly := rowAt compactBlock029Results 11
def node7536 : Poly := rowAt compactBlock029Results 12
def node7543 : Poly := rowAt compactBlock029Results 13
def node7561 : Poly := rowAt compactBlock029Results 14
def node7568 : Poly := rowAt compactBlock029Results 15
def node7569 : Poly := rowAt compactBlock029Results 16
def node7570 : Poly := rowAt compactBlock029Results 17
def node7571 : Poly := rowAt compactBlock029Results 18
def node7574 : Poly := rowAt compactBlock029Results 19
def node7575 : Poly := rowAt compactBlock029Results 20
def node7578 : Poly := rowAt compactBlock029Results 21
def node7579 : Poly := rowAt compactBlock029Results 22
def node7580 : Poly := rowAt compactBlock029Results 23
def node7581 : Poly := rowAt compactBlock029Results 24
def node7582 : Poly := rowAt compactBlock029Results 25
def node7583 : Poly := rowAt compactBlock029Results 26
def node7584 : Poly := rowAt compactBlock029Results 27
def node7585 : Poly := rowAt compactBlock029Results 28
def node7586 : Poly := rowAt compactBlock029Results 29
def node7587 : Poly := rowAt compactBlock029Results 30
def node7588 : Poly := rowAt compactBlock029Results 31
def node7589 : Poly := rowAt compactBlock029Results 32
def node7590 : Poly := rowAt compactBlock029Results 33
def node7591 : Poly := rowAt compactBlock029Results 34
def node7592 : Poly := rowAt compactBlock029Results 35
def node7593 : Poly := rowAt compactBlock029Results 36
def node7594 : Poly := rowAt compactBlock029Results 37
def node7595 : Poly := rowAt compactBlock029Results 38
def node7596 : Poly := rowAt compactBlock029Results 39
def node7597 : Poly := rowAt compactBlock029Results 40
def node7598 : Poly := rowAt compactBlock029Results 41
def node7599 : Poly := rowAt compactBlock029Results 42
def node7600 : Poly := rowAt compactBlock029Results 43
def node7601 : Poly := rowAt compactBlock029Results 44
def node7602 : Poly := rowAt compactBlock029Results 45
def node7603 : Poly := rowAt compactBlock029Results 46
def node7604 : Poly := rowAt compactBlock029Results 47
def node7605 : Poly := rowAt compactBlock029Results 48
def node7606 : Poly := rowAt compactBlock029Results 49
def node7607 : Poly := rowAt compactBlock029Results 50
def node7608 : Poly := rowAt compactBlock029Results 51
def node7609 : Poly := rowAt compactBlock029Results 52
def node7610 : Poly := rowAt compactBlock029Results 53
def node7611 : Poly := rowAt compactBlock029Results 54
def node7612 : Poly := rowAt compactBlock029Results 55

def compactBlock029Stage00Code : List Instruction := [
⟨62, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨64, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨66, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
⟨34, 71, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨43, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨46, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
⟨30, 6, [((-169/40000),0,(3,0,-1,2,0,0,0))]⟩,
⟨76, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨69, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨7, 2, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨7, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
⟨34, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
⟨77, 5, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨42, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨49, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨81, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩
]

def compactBlock029Stage00State : List Poly := program_state% (compactBlock029Inputs) (compactBlock029Stage00Code)

private theorem compactBlock029Stage00_checked : run compactBlock029Inputs compactBlock029Stage00Code = compactBlock029Stage00State := by
  decide +kernel

def compactBlock029Stage01Code : List Instruction := [
⟨83, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
⟨11, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
⟨62, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨40, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
⟨75, 11, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨10, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨44, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨11, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨80, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨82, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
⟨84, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨57, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨87, 19, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨69, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨90, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨11, 31, [((81/625),0,(0,-2,0,2,0,0,0))]⟩
]

def compactBlock029Stage01State : List Poly := program_state% (compactBlock029Stage00State) (compactBlock029Stage01Code)

private theorem compactBlock029Stage01_checked : run compactBlock029Stage00State compactBlock029Stage01Code = compactBlock029Stage01State := by
  decide +kernel

def compactBlock029Stage02Code : List Instruction := [
⟨83, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨25, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨33, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨61, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨3, 36, [((-625/676),0,(1,0,1,-2,0,0,0))]⟩,
⟨43, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-676/625),1,(-1,0,-1,2,0,0,0))]⟩,
⟨58, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
⟨14, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨67, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨93, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨60, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
⟨96, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
⟨63, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨99, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨96, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨16, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]

def compactBlock029Stage02State : List Poly := program_state% (compactBlock029Stage01State) (compactBlock029Stage02Code)

private theorem compactBlock029Stage02_checked : run compactBlock029Stage01State compactBlock029Stage02Code = compactBlock029Stage02State := by
  decide +kernel

def compactBlock029Prefix03Code : List Instruction := ((compactBlock029Stage00Code ++ compactBlock029Stage01Code) ++ compactBlock029Stage02Code)

theorem compactBlock029Prefix03_checked : run compactBlock029Inputs compactBlock029Prefix03Code = compactBlock029Stage02State := by
  exact run_append_of_results (run_append_of_results (compactBlock029Stage00_checked) compactBlock029Stage01_checked) compactBlock029Stage02_checked

#print axioms compactBlock029Prefix03_checked

}
end SmallLevelTwentySixGermDAG
end
