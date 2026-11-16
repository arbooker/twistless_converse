module
public import QuantitativeArithmeticCompactGermProgramLateBlocksV1
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

def compactBlock025Inputs : List Poly := [node0967, node0998, node1111, node1133, node1173, node1191, node5485, node5616, node5795, node5862, node5899, node5900, node5913, node5962, node6021, node6022, node6081, node6163, node6174, node6249, node6250, node6251, node6252, node6268, node6284, node6346, node6402, node6416, node6457, node6473, node6497, node6515, node6521, node6524, node6537, node6538, node6542, node6561, node6566, node6572, node6578, node6581, node6607, node6608, node6609, node6616, node6618, node6627, node6636, node6642, node6647, node6650, node6653, node6656, node6665, node6679, node6686, node6687, node6692, node6696, node6703, node6706, node6708, node6711, node6712, node6720, node6722, node6723, node6726, node6736, node6737, node6740, node6742, node6746, node6747, node6748, node6753, node6757, node6762, node6763, node6764, node6767, node6773, node6778, node6779, node6780, node6781, node6786, node6788, node6793, node6794, node6796, node6797, node6800, node6803, node6804]

theorem compactBlock025_inputs : ∀ p ∈ compactBlock025Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0967, node0998, node1111, node1133, node1173, node1191, node5485, node5616, node5795, node5862, node5899, node5900, node5913, node5962, node6021, node6022, node6081, node6163, node6174, node6249, node6250, node6251, node6252, node6268, node6284, node6346, node6402, node6416, node6457, node6473, node6497, node6515, node6521, node6524, node6537, node6538, node6542, node6561, node6566, node6572, node6578, node6581, node6607, node6608, node6609, node6616, node6618, node6627, node6636, node6642, node6647, node6650, node6653, node6656, node6665, node6679, node6686, node6687, node6692, node6696, node6703, node6706, node6708, node6711, node6712, node6720, node6722, node6723, node6726, node6736, node6737, node6740, node6742, node6746, node6747, node6748, node6753, node6757, node6762, node6763, node6764, node6767, node6773, node6778, node6779, node6780, node6781, node6786, node6788, node6793, node6794, node6796, node6797, node6800, node6803, node6804], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 967 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 998 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1111 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1133 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1173 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 65)
  exact nil_derived _ _

def compactBlock025Program : List Instruction := [
  ⟨32, 92, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨92, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((219024/625),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨68, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 8, [((-625/324),0,(1,2,0,-2,0,0,0))]⟩,
  ⟨85, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨15, 10, [((-81/4),0,(1,-2,0,0,0,0,0))]⟩,
  ⟨15, 0, [(1,0,(0,0,0,0,0,0,0)),
  (2500,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨54, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨70, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨40, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨17, 16, [((-324),0,(-1,-2,0,0,0,0,0))]⟩,
  ⟨52, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨99, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨84, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨81, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨111, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨46, 23, [((625/169),0,(0,0,1,-2,0,0,0))]⟩,
  ⟨57, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 1, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨67, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨33, 27, [((-10000),0,(-2,0,0,-2,0,0,0))]⟩,
  ⟨100, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨5, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 74, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨0, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 33, [((10816/50625),0,(-3,2,-1,2,0,0,0))]⟩,
  ⟨56, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨119, 2, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨104, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨56, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨88, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨15, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 43, [((40000/13689),0,(-3,2,1,-2,0,0,0))]⟩,
  ⟨56, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨21, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨119, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨134, 52, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨43, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨101, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨54, 52, [((-50625),0,(0,-2,0,-2,0,0,0))]⟩,
  ⟨23, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨89, 55, [((-169/81),0,(0,2,-1,0,0,0,0))]⟩,
  ⟨85, 0, [(1,0,(0,0,0,0,0,0,0)),
  (324,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨95, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 2, [(1,0,(0,0,0,0,0,0,0)),
  (324,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨90, 3, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨144, 4, [(1,0,(0,0,0,0,0,0,0)),
  (64,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨149, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨106, 6, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨119, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨116, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨145, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((81/169),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨147, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-8),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨22, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨50, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  ((81/169),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨140, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000),1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨48, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-22500/169),1,(-1,-1,1,-2,1,0,0))]⟩,
  ⟨162, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨118, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-5184),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨32, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-360000/169),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨128, 19, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨142, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨132, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((202500/169),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨137, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨103, 23, [(1,0,(0,0,0,0,0,0,0)),
  (36,1,(-1,-1,0,0,1,0,0))]⟩,
  ⟨155, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/169),1,(0,-2,1,-2,0,0,0)),
  ((81/169),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨120, 81, [((-169/16),0,(2,0,-1,0,0,0,0))]⟩,
  ⟨108, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((1/4),1,(1,0,0,0,0,0,0))]⟩,
  ⟨134, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1/4),1,(1,0,0,0,0,0,0))]⟩,
  ⟨162, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨67, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨21, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1/4),1,(1,0,0,0,0,0,0))]⟩,
  ⟨21, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-162),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨21, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨21, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨163, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨69, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨78, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨23, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨74, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨163, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/4),1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨142, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨25, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨118, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨148, 17, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨24, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨80, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨142, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((1296/169),1,(-2,-2,1,0,0,0,0)),
  ((16/169),1,(-2,0,1,0,0,0,0))]⟩,
  ⟨177, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨25, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((9/4),1,(1,-1,0,0,1,0,0))]⟩,
  ⟨24, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨11, 120, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨105, 121, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨20, 123, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 124, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨107, 125, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨9, 126, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 131, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨21, 132, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 133, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨177, 134, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨170, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨3, 130, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨40, 131, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨36, 135, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨156, 136, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨32, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨32, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨29, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨145, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨22, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((1296/169),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨208, 142, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨70, 145, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨157, 146, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 147, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨8, 148, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 149, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩
]













































































































































def compactBlock025Indices : List ℕ := [127, 125, 123, 120, 118, 117, 104, 98, 97, 96, 95, 94, 92, 90, 88, 86, 85, 84, 83, 79, 78, 76, 74, 73, 71, 70, 69, 64, 62, 59, 58, 56, 53, 49, 48, 47, 46, 42, 40, 37, 36, 35, 34, 33, 32, 29, 28, 27, 25, 24, 23, 22, 21, 20, 18, 17, 16, 15, 14, 13, 12, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock025Results : List Poly :=
  program_results% (compactBlock025Inputs) (compactBlock025Program) (compactBlock025Indices)

def node6806 : Poly := rowAt compactBlock025Results 0
def node6808 : Poly := rowAt compactBlock025Results 1
def node6810 : Poly := rowAt compactBlock025Results 2
def node6816 : Poly := rowAt compactBlock025Results 3
def node6818 : Poly := rowAt compactBlock025Results 4
def node6819 : Poly := rowAt compactBlock025Results 5
def node6839 : Poly := rowAt compactBlock025Results 6
def node6846 : Poly := rowAt compactBlock025Results 7
def node6847 : Poly := rowAt compactBlock025Results 8
def node6848 : Poly := rowAt compactBlock025Results 9
def node6849 : Poly := rowAt compactBlock025Results 10
def node6850 : Poly := rowAt compactBlock025Results 11
def node6852 : Poly := rowAt compactBlock025Results 12
def node6854 : Poly := rowAt compactBlock025Results 13
def node6856 : Poly := rowAt compactBlock025Results 14
def node6858 : Poly := rowAt compactBlock025Results 15
def node6859 : Poly := rowAt compactBlock025Results 16
def node6861 : Poly := rowAt compactBlock025Results 17
def node6862 : Poly := rowAt compactBlock025Results 18
def node6871 : Poly := rowAt compactBlock025Results 19
def node6875 : Poly := rowAt compactBlock025Results 20
def node6877 : Poly := rowAt compactBlock025Results 21
def node6879 : Poly := rowAt compactBlock025Results 22
def node6883 : Poly := rowAt compactBlock025Results 23
def node6885 : Poly := rowAt compactBlock025Results 24
def node6886 : Poly := rowAt compactBlock025Results 25
def node6887 : Poly := rowAt compactBlock025Results 26
def node6892 : Poly := rowAt compactBlock025Results 27
def node6895 : Poly := rowAt compactBlock025Results 28
def node6898 : Poly := rowAt compactBlock025Results 29
def node6899 : Poly := rowAt compactBlock025Results 30
def node6901 : Poly := rowAt compactBlock025Results 31
def node6904 : Poly := rowAt compactBlock025Results 32
def node6912 : Poly := rowAt compactBlock025Results 33
def node6913 : Poly := rowAt compactBlock025Results 34
def node6914 : Poly := rowAt compactBlock025Results 35
def node6915 : Poly := rowAt compactBlock025Results 36
def node6919 : Poly := rowAt compactBlock025Results 37
def node6921 : Poly := rowAt compactBlock025Results 38
def node6925 : Poly := rowAt compactBlock025Results 39
def node6926 : Poly := rowAt compactBlock025Results 40
def node6927 : Poly := rowAt compactBlock025Results 41
def node6929 : Poly := rowAt compactBlock025Results 42
def node6932 : Poly := rowAt compactBlock025Results 43
def node6933 : Poly := rowAt compactBlock025Results 44
def node6936 : Poly := rowAt compactBlock025Results 45
def node6937 : Poly := rowAt compactBlock025Results 46
def node6940 : Poly := rowAt compactBlock025Results 47
def node6942 : Poly := rowAt compactBlock025Results 48
def node6944 : Poly := rowAt compactBlock025Results 49
def node6945 : Poly := rowAt compactBlock025Results 50
def node6946 : Poly := rowAt compactBlock025Results 51
def node6947 : Poly := rowAt compactBlock025Results 52
def node6948 : Poly := rowAt compactBlock025Results 53
def node6950 : Poly := rowAt compactBlock025Results 54
def node6951 : Poly := rowAt compactBlock025Results 55
def node6952 : Poly := rowAt compactBlock025Results 56
def node6953 : Poly := rowAt compactBlock025Results 57
def node6954 : Poly := rowAt compactBlock025Results 58
def node6956 : Poly := rowAt compactBlock025Results 59
def node6957 : Poly := rowAt compactBlock025Results 60
def node6964 : Poly := rowAt compactBlock025Results 61
def node6967 : Poly := rowAt compactBlock025Results 62
def node6968 : Poly := rowAt compactBlock025Results 63
def node6969 : Poly := rowAt compactBlock025Results 64
def node6970 : Poly := rowAt compactBlock025Results 65
def node6971 : Poly := rowAt compactBlock025Results 66
def node6973 : Poly := rowAt compactBlock025Results 67
def node6974 : Poly := rowAt compactBlock025Results 68
def node6975 : Poly := rowAt compactBlock025Results 69

theorem compactBlock025_certificate : outputs compactBlock025Inputs compactBlock025Program compactBlock025Indices = compactBlock025Results := by
  decide +kernel

theorem compactBlock025_derived : ∀ p ∈ compactBlock025Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock025_inputs compactBlock025Program compactBlock025Indices compactBlock025_certificate

#print axioms compactBlock025_derived


def compactBlock026Inputs : List Poly := [node1112, node1116, node1129, node1191, node6193, node6234, node6252, node6291, node6364, node6375, node6380, node6392, node6399, node6441, node6481, node6559, node6565, node6573, node6592, node6614, node6626, node6632, node6637, node6640, node6725, node6731, node6761, node6772, node6777, node6783, node6787, node6790, node6801, node6802, node6808, node6810, node6816, node6818, node6819, node6839, node6847, node6848, node6849, node6852, node6854, node6858, node6859, node6861, node6862, node6875, node6877, node6879, node6885, node6887, node6892, node6895, node6898, node6913, node6915, node6921, node6925, node6927, node6929, node6932, node6936, node6944, node6945, node6947, node6951, node6954, node6956, node6957, node6964, node6967, node6968, node6969, node6970, node6971, node6973, node6974, node6975]

theorem compactBlock026_inputs : ∀ p ∈ compactBlock026Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node1112, node1116, node1129, node1191, node6193, node6234, node6252, node6291, node6364, node6375, node6380, node6392, node6399, node6441, node6481, node6559, node6565, node6573, node6592, node6614, node6626, node6632, node6637, node6640, node6725, node6731, node6761, node6772, node6777, node6783, node6787, node6790, node6801, node6802, node6808, node6810, node6816, node6818, node6819, node6839, node6847, node6848, node6849, node6852, node6854, node6858, node6859, node6861, node6862, node6875, node6877, node6879, node6885, node6887, node6892, node6895, node6898, node6913, node6915, node6921, node6925, node6927, node6929, node6932, node6936, node6944, node6945, node6947, node6951, node6954, node6956, node6957, node6964, node6967, node6968, node6969, node6970, node6971, node6973, node6974, node6975], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1112 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1116 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1129 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 69)
  exact nil_derived _ _

def compactBlock026Program : List Instruction := [
  ⟨27, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨41, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨64, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨71, 10, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨28, 8, [((-169/324),0,(1,2,-1,0,0,0,0))]⟩,
  ⟨28, 0, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨83, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨85, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨68, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-648),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨90, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨92, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨68, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨95, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((324/169),1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨82, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨72, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨17, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨62, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-360000/169),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨18, 14, [(1,0,(0,0,0,0,0,0,0)),
  (1296,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨18, 15, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨18, 16, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨61, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0))]⟩,
  ⟨93, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-8100/169),1,(-1,-2,1,-1,0,1,0))]⟩,
  ⟨78, 29, [((-13689/2500),0,(1,-2,-1,2,0,0,0))]⟩,
  ⟨45, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/13689),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨87, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨29, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨59, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨92, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/13689),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨11, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨45, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨41, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨91, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((64/9),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨105, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/1521),1,(-1,1,1,-2,1,0,0))]⟩,
  ⟨71, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨31, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 28, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨91, 29, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨69, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨62, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨69, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨97, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-202500/169),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨33, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((-648),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨32, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨31, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨31, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-648),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨81, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨83, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨76, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨89, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨92, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨78, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((3240000/169),1,(-3,-2,1,-2,0,0,0))]⟩,
  ⟨104, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-202500),1,(-1,-2,0,-2,0,0,0))]⟩,
  ⟨103, 45, [(1,0,(0,0,0,0,0,0,0)),
  (576,1,(-3,-1,0,0,1,0,0))]⟩,
  ⟨76, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨106, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨72, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨68, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-5184),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨65, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨126, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨137, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨110, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((3240000/169),1,(-3,-2,1,-2,0,0,0))]⟩,
  ⟨70, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/625),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨24, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((676/625),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨124, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((676/625),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨77, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((27378/625),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨23, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((676/625),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨42, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((13689/625),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨24, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((54756/625),1,(-1,-2,-1,2,0,0,0)),
  ((13689/625),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨42, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨16, 31, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨96, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨52, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((13689/625),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨13, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((-6084/625),1,(-1,-1,-1,2,1,0,0))]⟩,
  ⟨120, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((876096/625),1,(-3,-2,-1,2,0,0,0))]⟩,
  ⟨129, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨11, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨11, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨10, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨10, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨144, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨95, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨121, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨98, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨28, 17, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨134, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨72, 93, [((-1/40000),0,(3,0,0,2,0,0,0))]⟩,
  ⟨105, 0, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨53, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨163, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨86, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨55, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨167, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 6, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨17, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨89, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨54, 9, [(1,0,(0,0,0,0,0,0,0)),
  (648,1,(-1,-2,0,0,0,0,0)),
  ((324/169),1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨17, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0)),
  ((-324/169),1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨83, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨175, 12, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨84, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((360000/169),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨72, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨84, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨84, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨31, 17, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨84, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨183, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1296/169),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨49, 20, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨34, 21, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨188, 22, [(1,0,(0,0,0,0,0,0,0)),
  (1296,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨49, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-360000/169),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨159, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨90, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((202500/169),1,(-1,-2,1,-2,0,0,0)),
  ((8100/169),1,(-1,-2,1,-1,0,1,0)),
  ((324/169),1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨147, 120, [((625/5184),0,(3,2,0,-2,0,0,0))]⟩,
  ⟨159, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-5184/625),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨150, 122, [((1/4),0,(1,0,0,0,0,0,0))]⟩,
  ⟨61, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-5184/625),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨19, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨22, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨126, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨21, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]







































































































































def compactBlock026Indices : List ℕ := [113, 100, 98, 96, 94, 93, 92, 91, 90, 87, 84, 83, 78, 77, 76, 75, 74, 73, 72, 71, 67, 65, 62, 60, 54, 53, 52, 49, 46, 45, 43, 42, 41, 40, 39, 38, 36, 35, 34, 33, 32, 31, 30, 29, 28, 25, 24, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 9, 7, 6, 4, 3, 2, 1, 0]
def compactBlock026Results : List Poly :=
  program_results% (compactBlock026Inputs) (compactBlock026Program) (compactBlock026Indices)

def node6996 : Poly := rowAt compactBlock026Results 0
def node7014 : Poly := rowAt compactBlock026Results 1
def node7019 : Poly := rowAt compactBlock026Results 2
def node7022 : Poly := rowAt compactBlock026Results 3
def node7024 : Poly := rowAt compactBlock026Results 4
def node7025 : Poly := rowAt compactBlock026Results 5
def node7026 : Poly := rowAt compactBlock026Results 6
def node7027 : Poly := rowAt compactBlock026Results 7
def node7028 : Poly := rowAt compactBlock026Results 8
def node7031 : Poly := rowAt compactBlock026Results 9
def node7035 : Poly := rowAt compactBlock026Results 10
def node7036 : Poly := rowAt compactBlock026Results 11
def node7043 : Poly := rowAt compactBlock026Results 12
def node7045 : Poly := rowAt compactBlock026Results 13
def node7046 : Poly := rowAt compactBlock026Results 14
def node7047 : Poly := rowAt compactBlock026Results 15
def node7048 : Poly := rowAt compactBlock026Results 16
def node7049 : Poly := rowAt compactBlock026Results 17
def node7050 : Poly := rowAt compactBlock026Results 18
def node7051 : Poly := rowAt compactBlock026Results 19
def node7055 : Poly := rowAt compactBlock026Results 20
def node7057 : Poly := rowAt compactBlock026Results 21
def node7060 : Poly := rowAt compactBlock026Results 22
def node7064 : Poly := rowAt compactBlock026Results 23
def node7075 : Poly := rowAt compactBlock026Results 24
def node7076 : Poly := rowAt compactBlock026Results 25
def node7078 : Poly := rowAt compactBlock026Results 26
def node7082 : Poly := rowAt compactBlock026Results 27
def node7087 : Poly := rowAt compactBlock026Results 28
def node7088 : Poly := rowAt compactBlock026Results 29
def node7091 : Poly := rowAt compactBlock026Results 30
def node7092 : Poly := rowAt compactBlock026Results 31
def node7093 : Poly := rowAt compactBlock026Results 32
def node7094 : Poly := rowAt compactBlock026Results 33
def node7095 : Poly := rowAt compactBlock026Results 34
def node7096 : Poly := rowAt compactBlock026Results 35
def node7098 : Poly := rowAt compactBlock026Results 36
def node7099 : Poly := rowAt compactBlock026Results 37
def node7100 : Poly := rowAt compactBlock026Results 38
def node7101 : Poly := rowAt compactBlock026Results 39
def node7102 : Poly := rowAt compactBlock026Results 40
def node7103 : Poly := rowAt compactBlock026Results 41
def node7104 : Poly := rowAt compactBlock026Results 42
def node7107 : Poly := rowAt compactBlock026Results 43
def node7108 : Poly := rowAt compactBlock026Results 44
def node7117 : Poly := rowAt compactBlock026Results 45
def node7118 : Poly := rowAt compactBlock026Results 46
def node7120 : Poly := rowAt compactBlock026Results 47
def node7121 : Poly := rowAt compactBlock026Results 48
def node7125 : Poly := rowAt compactBlock026Results 49
def node7126 : Poly := rowAt compactBlock026Results 50
def node7127 : Poly := rowAt compactBlock026Results 51
def node7128 : Poly := rowAt compactBlock026Results 52
def node7129 : Poly := rowAt compactBlock026Results 53
def node7130 : Poly := rowAt compactBlock026Results 54
def node7131 : Poly := rowAt compactBlock026Results 55
def node7132 : Poly := rowAt compactBlock026Results 56
def node7135 : Poly := rowAt compactBlock026Results 57
def node7136 : Poly := rowAt compactBlock026Results 58
def node7139 : Poly := rowAt compactBlock026Results 59
def node7142 : Poly := rowAt compactBlock026Results 60
def node7143 : Poly := rowAt compactBlock026Results 61
def node7146 : Poly := rowAt compactBlock026Results 62
def node7147 : Poly := rowAt compactBlock026Results 63
def node7149 : Poly := rowAt compactBlock026Results 64
def node7150 : Poly := rowAt compactBlock026Results 65
def node7151 : Poly := rowAt compactBlock026Results 66

theorem compactBlock026_certificate : outputs compactBlock026Inputs compactBlock026Program compactBlock026Indices = compactBlock026Results := by
  decide +kernel

theorem compactBlock026_derived : ∀ p ∈ compactBlock026Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock026_inputs compactBlock026Program compactBlock026Indices compactBlock026_certificate

#print axioms compactBlock026_derived


def compactBlock027Inputs : List Poly := [node1126, node1128, node1132, node1191, node6565, node6610, node6613, node6624, node6695, node6700, node6739, node6749, node6752, node6774, node6798, node6799, node6805, node6806, node6846, node6850, node6856, node6871, node6883, node6886, node6899, node6901, node6904, node6912, node6914, node6937, node6948, node6950, node6952, node6953, node7014, node7019, node7022, node7024, node7026, node7027, node7028, node7031, node7035, node7036, node7043, node7045, node7046, node7047, node7048, node7049, node7050, node7051, node7055, node7057, node7060, node7064, node7075, node7076, node7078, node7082, node7087, node7088, node7091, node7092, node7093, node7094, node7095, node7096, node7098, node7099, node7100, node7101, node7104, node7107, node7108, node7117, node7118, node7120, node7121, node7125, node7126, node7127, node7129, node7130, node7131, node7132, node7136, node7139, node7142, node7143, node7146, node7149, node7150, node7151]

theorem compactBlock027_inputs : ∀ p ∈ compactBlock027Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node1126, node1128, node1132, node1191, node6565, node6610, node6613, node6624, node6695, node6700, node6739, node6749, node6752, node6774, node6798, node6799, node6805, node6806, node6846, node6850, node6856, node6871, node6883, node6886, node6899, node6901, node6904, node6912, node6914, node6937, node6948, node6950, node6952, node6953, node7014, node7019, node7022, node7024, node7026, node7027, node7028, node7031, node7035, node7036, node7043, node7045, node7046, node7047, node7048, node7049, node7050, node7051, node7055, node7057, node7060, node7064, node7075, node7076, node7078, node7082, node7087, node7088, node7091, node7092, node7093, node7094, node7095, node7096, node7098, node7099, node7100, node7101, node7104, node7107, node7108, node7117, node7118, node7120, node7121, node7125, node7126, node7127, node7129, node7130, node7131, node7132, node7136, node7139, node7142, node7143, node7146, node7149, node7150, node7151], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1126 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1128 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1132 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 66)
  exact nil_derived _ _

def compactBlock027Program : List Instruction := [
  ⟨85, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨62, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨13, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000),1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨63, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨57, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨67, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨42, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨101, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨13, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨48, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨99, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨108, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨56, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨25, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨18, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨63, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨3, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 95, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨97, 28, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((625/676),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨32, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨83, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨102, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/676),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨104, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((625/676),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨12, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨11, 6, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨54, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨46, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨79, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨81, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((625/676),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨29, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-16),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨47, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨95, 13, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨86, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨34, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0)),
  (16,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨120, 16, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨100, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((5625/676),1,(1,-1,1,-2,1,0,0))]⟩,
  ⟨102, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/676),1,(1,-2,1,-2,0,0,0)),
  ((625/676),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨124, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨126, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨128, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨101, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-5625/676),1,(1,-1,1,-2,1,0,0))]⟩,
  ⟨132, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0))]⟩,
  ⟨41, 24, [(1,0,(0,0,0,0,0,0,0)),
  (1296,1,(-2,-2,0,0,0,0,0)),
  ((-16),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨19, 78, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨28, 79, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 80, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 75, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨123, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨82, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨89, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨5, 83, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨136, 84, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨62, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨5, 86, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨152, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨81, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨148, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨151, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((64/9),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨67, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨3, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨102, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨19, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨11, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨150, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨19, 103, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨168, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨154, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((64/9),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨116, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨166, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨42, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨124, 85, [((-2704/50625),0,(-2,2,-1,2,0,0,0))]⟩,
  ⟨68, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨115, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨137, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨16, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨104, 4, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨131, 91, [((-2704/50625),0,(-2,2,-1,2,0,0,0))]⟩,
  ⟨5, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨96, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨109, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 3, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨11, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨104, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨134, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨82, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨159, 100, [((-1/50625),0,(0,2,0,2,0,0,0))]⟩,
  ⟨71, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨69, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨69, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨191, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨29, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨117, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨168, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨170, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨154, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨156, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000),1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨158, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨160, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨176, 13, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨178, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0))]⟩,
  ⟨54, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨57, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨140, 17, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨69, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨143, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨19, 121, [((-13689/2500),0,(1,-2,-1,2,0,0,0))]⟩,
  ⟨16, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨16, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨85, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨157, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨47, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨87, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/13689),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨61, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨114, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/13689),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨87, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((64/81),1,(-3,2,0,0,0,0,0))]⟩
]

















































































































































def compactBlock027Indices : List ℕ := [115, 111, 110, 106, 105, 103, 100, 99, 94, 93, 89, 87, 86, 85, 84, 83, 82, 80, 79, 78, 77, 66, 65, 63, 61, 60, 59, 55, 53, 51, 50, 48, 47, 43, 42, 41, 40, 38, 37, 36, 35, 34, 33, 32, 31, 28, 27, 26, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock027Results : List Poly :=
  program_results% (compactBlock027Inputs) (compactBlock027Program) (compactBlock027Indices)

def node7169 : Poly := rowAt compactBlock027Results 0
def node7174 : Poly := rowAt compactBlock027Results 1
def node7176 : Poly := rowAt compactBlock027Results 2
def node7181 : Poly := rowAt compactBlock027Results 3
def node7185 : Poly := rowAt compactBlock027Results 4
def node7187 : Poly := rowAt compactBlock027Results 5
def node7194 : Poly := rowAt compactBlock027Results 6
def node7195 : Poly := rowAt compactBlock027Results 7
def node7201 : Poly := rowAt compactBlock027Results 8
def node7202 : Poly := rowAt compactBlock027Results 9
def node7210 : Poly := rowAt compactBlock027Results 10
def node7212 : Poly := rowAt compactBlock027Results 11
def node7214 : Poly := rowAt compactBlock027Results 12
def node7215 : Poly := rowAt compactBlock027Results 13
def node7216 : Poly := rowAt compactBlock027Results 14
def node7218 : Poly := rowAt compactBlock027Results 15
def node7220 : Poly := rowAt compactBlock027Results 16
def node7222 : Poly := rowAt compactBlock027Results 17
def node7223 : Poly := rowAt compactBlock027Results 18
def node7224 : Poly := rowAt compactBlock027Results 19
def node7225 : Poly := rowAt compactBlock027Results 20
def node7238 : Poly := rowAt compactBlock027Results 21
def node7239 : Poly := rowAt compactBlock027Results 22
def node7241 : Poly := rowAt compactBlock027Results 23
def node7243 : Poly := rowAt compactBlock027Results 24
def node7244 : Poly := rowAt compactBlock027Results 25
def node7245 : Poly := rowAt compactBlock027Results 26
def node7249 : Poly := rowAt compactBlock027Results 27
def node7252 : Poly := rowAt compactBlock027Results 28
def node7255 : Poly := rowAt compactBlock027Results 29
def node7256 : Poly := rowAt compactBlock027Results 30
def node7258 : Poly := rowAt compactBlock027Results 31
def node7259 : Poly := rowAt compactBlock027Results 32
def node7264 : Poly := rowAt compactBlock027Results 33
def node7265 : Poly := rowAt compactBlock027Results 34
def node7266 : Poly := rowAt compactBlock027Results 35
def node7267 : Poly := rowAt compactBlock027Results 36
def node7270 : Poly := rowAt compactBlock027Results 37
def node7272 : Poly := rowAt compactBlock027Results 38
def node7273 : Poly := rowAt compactBlock027Results 39
def node7274 : Poly := rowAt compactBlock027Results 40
def node7275 : Poly := rowAt compactBlock027Results 41
def node7276 : Poly := rowAt compactBlock027Results 42
def node7277 : Poly := rowAt compactBlock027Results 43
def node7278 : Poly := rowAt compactBlock027Results 44
def node7283 : Poly := rowAt compactBlock027Results 45
def node7284 : Poly := rowAt compactBlock027Results 46
def node7285 : Poly := rowAt compactBlock027Results 47
def node7290 : Poly := rowAt compactBlock027Results 48
def node7291 : Poly := rowAt compactBlock027Results 49
def node7294 : Poly := rowAt compactBlock027Results 50
def node7295 : Poly := rowAt compactBlock027Results 51
def node7296 : Poly := rowAt compactBlock027Results 52
def node7297 : Poly := rowAt compactBlock027Results 53
def node7298 : Poly := rowAt compactBlock027Results 54
def node7299 : Poly := rowAt compactBlock027Results 55
def node7300 : Poly := rowAt compactBlock027Results 56
def node7301 : Poly := rowAt compactBlock027Results 57
def node7302 : Poly := rowAt compactBlock027Results 58
def node7303 : Poly := rowAt compactBlock027Results 59
def node7304 : Poly := rowAt compactBlock027Results 60
def node7305 : Poly := rowAt compactBlock027Results 61
def node7306 : Poly := rowAt compactBlock027Results 62
def node7309 : Poly := rowAt compactBlock027Results 63
def node7310 : Poly := rowAt compactBlock027Results 64
def node7313 : Poly := rowAt compactBlock027Results 65
def node7314 : Poly := rowAt compactBlock027Results 66
def node7316 : Poly := rowAt compactBlock027Results 67
def node7318 : Poly := rowAt compactBlock027Results 68
def node7319 : Poly := rowAt compactBlock027Results 69
def node7320 : Poly := rowAt compactBlock027Results 70
def node7321 : Poly := rowAt compactBlock027Results 71

private def compactBlock027Stage00Code : List Instruction := [
⟨85, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨62, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨13, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000),1,(-2,0,0,-2,0,0,0))]⟩,
⟨63, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨2, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨94, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨57, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨8, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨67, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨42, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨101, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨13, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨48, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨99, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨4, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨108, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩
]

private def compactBlock027Stage00State : List Poly := program_state% (compactBlock027Inputs) (compactBlock027Stage00Code)

private theorem compactBlock027Stage00_checked : run compactBlock027Inputs compactBlock027Stage00Code = compactBlock027Stage00State := by
  decide +kernel

private def compactBlock027Stage01Code : List Instruction := [
⟨56, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨25, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨14, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨14, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨14, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨18, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000),1,(-3,0,0,-2,0,0,0))]⟩,
⟨63, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨3, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨53, 95, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨97, 28, [((-1),0,(0,0,0,0,0,0,0))]⟩,
⟨41, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((625/676),1,(1,0,1,-2,0,0,0))]⟩,
⟨32, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨83, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨102, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/676),1,(1,0,1,-2,0,0,0))]⟩,
⟨104, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((625/676),1,(1,0,1,-2,0,0,0))]⟩,
⟨12, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩
]

private def compactBlock027Stage01State : List Poly := program_state% (compactBlock027Stage00State) (compactBlock027Stage01Code)

private theorem compactBlock027Stage01_checked : run compactBlock027Stage00State compactBlock027Stage01Code = compactBlock027Stage01State := by
  decide +kernel

private def compactBlock027Stage02Code : List Instruction := [
⟨11, 6, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨54, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625),1,(0,-2,0,-2,0,0,0))]⟩,
⟨46, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0))]⟩,
⟨79, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨81, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((625/676),1,(1,0,1,-2,0,0,0))]⟩,
⟨29, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-16),1,(-2,0,0,0,0,0,0))]⟩,
⟨47, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((625/169),1,(0,0,1,-2,0,0,0))]⟩,
⟨95, 13, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨86, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨34, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0)),
  (16,1,(-2,0,0,0,0,0,0))]⟩,
⟨120, 16, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
⟨100, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((5625/676),1,(1,-1,1,-2,1,0,0))]⟩,
⟨102, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/676),1,(1,-2,1,-2,0,0,0)),
  ((625/676),1,(1,0,1,-2,0,0,0))]⟩,
⟨124, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨126, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨128, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩
]

private def compactBlock027Stage02State : List Poly := program_state% (compactBlock027Stage01State) (compactBlock027Stage02Code)

private theorem compactBlock027Stage02_checked : run compactBlock027Stage01State compactBlock027Stage02Code = compactBlock027Stage02State := by
  decide +kernel

private def compactBlock027Stage03Code : List Instruction := [
⟨101, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-5625/676),1,(1,-1,1,-2,1,0,0))]⟩,
⟨132, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0))]⟩,
⟨41, 24, [(1,0,(0,0,0,0,0,0,0)),
  (1296,1,(-2,-2,0,0,0,0,0)),
  ((-16),1,(-2,0,0,0,0,0,0))]⟩,
⟨19, 78, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨28, 79, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨20, 80, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨1, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨44, 75, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨123, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨41, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨82, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨89, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
⟨5, 83, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨136, 84, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
⟨62, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨5, 86, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩
]

private def compactBlock027Stage03State : List Poly := program_state% (compactBlock027Stage02State) (compactBlock027Stage03Code)

private theorem compactBlock027Stage03_checked : run compactBlock027Stage02State compactBlock027Stage03Code = compactBlock027Stage03State := by
  decide +kernel

private def compactBlock027Stage04Code : List Instruction := [
⟨152, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩,
⟨81, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
⟨148, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨151, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((64/9),1,(-3,1,0,0,1,0,0))]⟩,
⟨67, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
⟨3, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨102, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
⟨19, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨11, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨19, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨150, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
⟨19, 103, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
⟨168, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
⟨154, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((64/9),1,(-3,1,0,0,1,0,0))]⟩,
⟨116, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
⟨166, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩
]

private def compactBlock027Stage04State : List Poly := program_state% (compactBlock027Stage03State) (compactBlock027Stage04Code)

private theorem compactBlock027Stage04_checked : run compactBlock027Stage03State compactBlock027Stage04Code = compactBlock027Stage04State := by
  decide +kernel

private def compactBlock027Stage05Code : List Instruction := [
⟨42, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨2, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨124, 85, [((-2704/50625),0,(-2,2,-1,2,0,0,0))]⟩,
⟨68, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
⟨115, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
⟨137, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨16, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
⟨104, 4, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
⟨131, 91, [((-2704/50625),0,(-2,2,-1,2,0,0,0))]⟩,
⟨5, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
⟨96, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
⟨109, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨129, 3, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
⟨11, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
⟨104, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨134, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩
]

private def compactBlock027Stage05State : List Poly := program_state% (compactBlock027Stage04State) (compactBlock027Stage05Code)

private theorem compactBlock027Stage05_checked : run compactBlock027Stage04State compactBlock027Stage05Code = compactBlock027Stage05State := by
  decide +kernel

private def compactBlock027Stage06Code : List Instruction := [
⟨82, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
⟨159, 100, [((-1/50625),0,(0,2,0,2,0,0,0))]⟩,
⟨71, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
⟨69, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
⟨69, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
⟨191, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨30, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨29, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨117, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/4),1,(1,0,0,-2,0,0,0))]⟩,
⟨168, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨170, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((625/4),1,(1,0,0,-2,0,0,0))]⟩,
⟨154, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
⟨156, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000),1,(-2,0,0,-2,0,0,0))]⟩,
⟨158, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
⟨160, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625),1,(0,-2,0,-2,0,0,0))]⟩,
⟨176, 13, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩
]

private def compactBlock027Stage06State : List Poly := program_state% (compactBlock027Stage05State) (compactBlock027Stage06Code)

private theorem compactBlock027Stage06_checked : run compactBlock027Stage05State compactBlock027Stage06Code = compactBlock027Stage06State := by
  decide +kernel

private def compactBlock027Stage07Code : List Instruction := [
⟨178, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0))]⟩,
⟨54, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
⟨57, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
⟨140, 17, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
⟨69, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨143, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
⟨19, 121, [((-13689/2500),0,(1,-2,-1,2,0,0,0))]⟩,
⟨16, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨16, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨85, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
⟨157, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨47, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
⟨87, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/13689),1,(-1,2,1,-2,0,0,0))]⟩,
⟨61, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/13689),1,(-2,2,1,-2,0,0,0))]⟩,
⟨114, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/13689),1,(-1,2,1,-2,0,0,0))]⟩,
⟨87, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((64/81),1,(-3,2,0,0,0,0,0))]⟩
]

private def compactBlock027Stage07State : List Poly := program_state% (compactBlock027Stage06State) (compactBlock027Stage07Code)

private theorem compactBlock027Stage07_checked : run compactBlock027Stage06State compactBlock027Stage07Code = compactBlock027Stage07State := by
  decide +kernel

theorem compactBlock027_certificate : outputs compactBlock027Inputs compactBlock027Program compactBlock027Indices = compactBlock027Results := by
  apply outputs_of_run_result (last := compactBlock027Stage07State)
  · change run compactBlock027Inputs (((((((compactBlock027Stage00Code ++ compactBlock027Stage01Code) ++ compactBlock027Stage02Code) ++ compactBlock027Stage03Code) ++ compactBlock027Stage04Code) ++ compactBlock027Stage05Code) ++ compactBlock027Stage06Code) ++ compactBlock027Stage07Code) = _
    exact run_append_of_results (run_append_of_results (run_append_of_results (run_append_of_results (run_append_of_results (run_append_of_results (run_append_of_results (compactBlock027Stage00_checked) compactBlock027Stage01_checked) compactBlock027Stage02_checked) compactBlock027Stage03_checked) compactBlock027Stage04_checked) compactBlock027Stage05_checked) compactBlock027Stage06_checked) compactBlock027Stage07_checked
  · decide +kernel

theorem compactBlock027_derived : ∀ p ∈ compactBlock027Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock027_inputs compactBlock027Program compactBlock027Indices compactBlock027_certificate

#print axioms compactBlock027_derived


}
end SmallLevelTwentySixGermDAG
end
