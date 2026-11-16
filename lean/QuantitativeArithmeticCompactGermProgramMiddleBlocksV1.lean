module
public import QuantitativeArithmeticCompactGermProgramInitialBlocksV1
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
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace SmallLevelTwentySixGermDAG
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation
open QuantitativeArithmeticLaurentProgram
certificate_batch {

def compactBlock010Inputs : List Poly := [node0438, node0453, node0484, node0538, node0541, node0572, node0800, node0850, node0881, node0935, node0938, node0969, node1191, node1204, node1205, node1206, node1271, node1277, node1295, node1302, node1533, node1539, node1568, node1574, node1797, node1798, node2065, node2066, node2104, node2107, node2156, node2157, node2159, node2237, node2329, node2352, node2488, node2489, node2557, node2558, node2570, node2571, node2747, node2749, node2751, node2753, node2756, node2757, node2773, node2774, node2779, node2780, node2853, node2987, node3005, node3008, node3101, node3102, node3220, node3221, node3235, node3236, node3240, node3241, node3248, node3296, node3398, node3399, node3403, node3419, node3436, node3490, node3491, node3492, node3494, node3495, node3497, node3500, node3501, node3507, node3564, node3571, node3572, node3573, node3574, node3575, node3576, node3579, node3580, node3584, node3595, node3626, node3631, node3632, node3633]

theorem compactBlock010_inputs : ∀ p ∈ compactBlock010Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0438, node0453, node0484, node0538, node0541, node0572, node0800, node0850, node0881, node0935, node0938, node0969, node1191, node1204, node1205, node1206, node1271, node1277, node1295, node1302, node1533, node1539, node1568, node1574, node1797, node1798, node2065, node2066, node2104, node2107, node2156, node2157, node2159, node2237, node2329, node2352, node2488, node2489, node2557, node2558, node2570, node2571, node2747, node2749, node2751, node2753, node2756, node2757, node2773, node2774, node2779, node2780, node2853, node2987, node3005, node3008, node3101, node3102, node3220, node3221, node3235, node3236, node3240, node3241, node3248, node3296, node3398, node3399, node3403, node3419, node3436, node3490, node3491, node3492, node3494, node3495, node3497, node3500, node3501, node3507, node3564, node3571, node3572, node3573, node3574, node3575, node3576, node3579, node3580, node3584, node3595, node3626, node3631, node3632, node3633], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 438 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 453 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 484 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 538 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 541 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 572 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 800 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 850 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 881 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 935 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 938 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 969 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 100)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 101)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 97)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 98)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 100)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 42)
  exact nil_derived _ _

def compactBlock010Program : List Instruction := [
  ⟨71, 81, [(1,0,(0,0,0,0,0,0,0)),
  (1800,1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨43, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((-4225/2),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨74, 83, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨33, 84, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨47, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/225),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨78, 86, [(1,0,(0,0,0,0,0,0,0)),
  ((338/25),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨81, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-338/9),1,(0,0,0,0,0,0,0))]⟩,
  ⟨83, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/50),1,(0,0,0,0,0,0,0))]⟩,
  ⟨40, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/8),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨45, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((169/450),1,(0,0,0,0,0,0,0))]⟩,
  ⟨87, 92, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨77, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-304200),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨57, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((-76050),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨48, 95, [(1,0,(0,0,0,0,0,0,0)),
  (3042,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨60, 96, [(1,0,(0,0,0,0,0,0,0)),
  (88200,1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨49, 97, [(1,0,(0,0,0,0,0,0,0)),
  ((194688/25),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨86, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨85, 99, [(1,0,(0,0,0,0,0,0,0)),
  (1800,1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨77, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(0,0,0,0,0,0,0))]⟩,
  ⟨79, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨68, 103, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨100, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨102, 105, [(1,0,(0,0,0,0,0,0,0)),
  (450,1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨72, 106, [(1,0,(0,0,0,0,0,0,0)),
  (1800,1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨81, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨114, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨92, 110, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 112, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 115, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 116, [(1,0,(0,0,0,0,0,0,0)),
  ((-65/6),1,(2,2,0,-2,0,0,0))]⟩,
  ⟨37, 117, [(1,0,(0,0,0,0,0,0,0)),
  ((65/3),1,(1,2,0,-2,0,0,0))]⟩,
  ⟨40, 118, [(1,0,(0,0,0,0,0,0,0)),
  (304200,1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨98, 119, [(1,0,(0,0,0,0,0,0,0)),
  ((-4225/72),1,(2,2,0,-2,0,0,0))]⟩,
  ⟨46, 120, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/18),1,(1,2,0,-2,0,0,0))]⟩,
  ⟨5, 122, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 123, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨100, 124, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨120, 126, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨133, 127, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨80, 128, [(1,0,(0,0,0,0,0,0,0)),
  ((15/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨82, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((225/8),1,(0,0,0,0,0,0,0))]⟩,
  ⟨100, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨115, 4, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨140, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨100, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-78/5),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨96, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨103, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨99, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨5, 63, [((-1),0,(1,0,-1,2,0,0,0))]⟩,
  ⟨120, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨6, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨78, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((39/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-30),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨81, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/50),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨146, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨111, 6, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨22, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨140, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨102, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((39/10),1,(0,0,0,0,0,0,0))]⟩,
  ⟨104, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/200),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 76, [((-1),0,(2,-2,-1,2,0,0,0))]⟩,
  ⟨34, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨71, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((20/3),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨78, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-200/9),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨161, 83, [((-1),0,(3,0,-1,2,0,0,0))]⟩,
  ⟨6, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨6, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨6, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨81, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-20/3),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨14, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/10),1,(0,0,0,0,0,0,0))]⟩,
  ⟨89, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-200/9),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨15, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/200),1,(0,0,0,0,0,0,0))]⟩,
  ⟨169, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨172, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨28, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨28, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨87, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((130/3),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨29, 11, [(1,0,(0,0,0,0,0,0,0)),
  (30,1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨108, 12, [(1,0,(0,0,0,0,0,0,0)),
  (30,1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨30, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/50),1,(0,0,0,0,0,0,0))]⟩,
  ⟨97, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((8450/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨31, 15, [(1,0,(0,0,0,0,0,0,0)),
  (450,1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨113, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨10, 103, [(1,0,(0,-2,0,2,0,0,0))]⟩,
  ⟨47, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨27, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨96, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((65/3),1,(1,2,0,-2,0,0,0))]⟩,
  ⟨103, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/18),1,(1,2,0,-2,0,0,0))]⟩,
  ⟨4, 109, [((-1),0,(1,0,1,-2,0,0,0))]⟩,
  ⟨155, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨57, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨17, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((78/5),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨130, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((78/5),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨54, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨154, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨55, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((3042/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨135, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨56, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨159, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨14, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨146, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((78/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨148, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((3042/25),1,(0,0,0,0,0,0,0))]⟩,
  ⟨132, 2, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨134, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨39, 126, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨21, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨40, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨47, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-20/3),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨144, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨48, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((200/9),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨147, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/50),1,(0,0,0,0,0,0,0))]⟩,
  ⟨137, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨9, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨140, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨10, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1800,1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨138, 125, [(1,0,(0,0,0,0,0,0,0)),
  (50,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨140, 126, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨142, 127, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩
]























































































































































def compactBlock010Indices : List ℕ := [127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 95, 94, 93, 92, 91, 89, 88, 85, 84, 51, 50, 49, 48, 46, 44, 43, 42, 41, 40, 39, 38, 37, 32, 31, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 17, 16, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock010Results : List Poly :=
  program_results% (compactBlock010Inputs) (compactBlock010Program) (compactBlock010Indices)

def node3722 : Poly := rowAt compactBlock010Results 0
def node3726 : Poly := rowAt compactBlock010Results 1
def node3727 : Poly := rowAt compactBlock010Results 2
def node3728 : Poly := rowAt compactBlock010Results 3
def node3730 : Poly := rowAt compactBlock010Results 4
def node3732 : Poly := rowAt compactBlock010Results 5
def node3737 : Poly := rowAt compactBlock010Results 6
def node3739 : Poly := rowAt compactBlock010Results 7
def node3740 : Poly := rowAt compactBlock010Results 8
def node3741 : Poly := rowAt compactBlock010Results 9
def node3742 : Poly := rowAt compactBlock010Results 10
def node3747 : Poly := rowAt compactBlock010Results 11
def node3748 : Poly := rowAt compactBlock010Results 12
def node3749 : Poly := rowAt compactBlock010Results 13
def node3750 : Poly := rowAt compactBlock010Results 14
def node3753 : Poly := rowAt compactBlock010Results 15
def node3754 : Poly := rowAt compactBlock010Results 16
def node3755 : Poly := rowAt compactBlock010Results 17
def node3756 : Poly := rowAt compactBlock010Results 18
def node3757 : Poly := rowAt compactBlock010Results 19
def node3758 : Poly := rowAt compactBlock010Results 20
def node3759 : Poly := rowAt compactBlock010Results 21
def node3760 : Poly := rowAt compactBlock010Results 22
def node3761 : Poly := rowAt compactBlock010Results 23
def node3762 : Poly := rowAt compactBlock010Results 24
def node3763 : Poly := rowAt compactBlock010Results 25
def node3764 : Poly := rowAt compactBlock010Results 26
def node3780 : Poly := rowAt compactBlock010Results 27
def node3781 : Poly := rowAt compactBlock010Results 28
def node3782 : Poly := rowAt compactBlock010Results 29
def node3783 : Poly := rowAt compactBlock010Results 30
def node3784 : Poly := rowAt compactBlock010Results 31
def node3792 : Poly := rowAt compactBlock010Results 32
def node3796 : Poly := rowAt compactBlock010Results 33
def node3803 : Poly := rowAt compactBlock010Results 34
def node3804 : Poly := rowAt compactBlock010Results 35
def node3867 : Poly := rowAt compactBlock010Results 36
def node3868 : Poly := rowAt compactBlock010Results 37
def node3871 : Poly := rowAt compactBlock010Results 38
def node3872 : Poly := rowAt compactBlock010Results 39
def node3889 : Poly := rowAt compactBlock010Results 40
def node3893 : Poly := rowAt compactBlock010Results 41
def node3894 : Poly := rowAt compactBlock010Results 42
def node3896 : Poly := rowAt compactBlock010Results 43
def node3897 : Poly := rowAt compactBlock010Results 44
def node3900 : Poly := rowAt compactBlock010Results 45
def node3901 : Poly := rowAt compactBlock010Results 46
def node3903 : Poly := rowAt compactBlock010Results 47
def node3904 : Poly := rowAt compactBlock010Results 48
def node3911 : Poly := rowAt compactBlock010Results 49
def node3912 : Poly := rowAt compactBlock010Results 50
def node3924 : Poly := rowAt compactBlock010Results 51
def node3925 : Poly := rowAt compactBlock010Results 52
def node3926 : Poly := rowAt compactBlock010Results 53
def node3927 : Poly := rowAt compactBlock010Results 54
def node3928 : Poly := rowAt compactBlock010Results 55
def node3929 : Poly := rowAt compactBlock010Results 56
def node3930 : Poly := rowAt compactBlock010Results 57
def node3931 : Poly := rowAt compactBlock010Results 58
def node3932 : Poly := rowAt compactBlock010Results 59
def node3933 : Poly := rowAt compactBlock010Results 60
def node3938 : Poly := rowAt compactBlock010Results 61
def node3940 : Poly := rowAt compactBlock010Results 62
def node3963 : Poly := rowAt compactBlock010Results 63
def node3964 : Poly := rowAt compactBlock010Results 64
def node3965 : Poly := rowAt compactBlock010Results 65
def node3967 : Poly := rowAt compactBlock010Results 66
def node3968 : Poly := rowAt compactBlock010Results 67
def node3974 : Poly := rowAt compactBlock010Results 68
def node3975 : Poly := rowAt compactBlock010Results 69
def node3977 : Poly := rowAt compactBlock010Results 70
def node3978 : Poly := rowAt compactBlock010Results 71
def node3985 : Poly := rowAt compactBlock010Results 72
def node3986 : Poly := rowAt compactBlock010Results 73
def node3987 : Poly := rowAt compactBlock010Results 74

theorem compactBlock010_certificate : outputs compactBlock010Inputs compactBlock010Program compactBlock010Indices = compactBlock010Results := by
  decide +kernel

theorem compactBlock010_derived : ∀ p ∈ compactBlock010Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock010_inputs compactBlock010Program compactBlock010Indices compactBlock010_certificate

#print axioms compactBlock010_derived


def compactBlock011Inputs : List Poly := [node0402, node0438, node0687, node0691, node0694, node0697, node0710, node0711, node0750, node0755, node0760, node0761, node0779, node0782, node0791, node1191, node1211, node1212, node1213, node1221, node1222, node1244, node1245, node1248, node1249, node1255, node1256, node1293, node1294, node1296, node1300, node1301, node1303, node1320, node1322, node1327, node1329, node1337, node1338, node1377, node1378, node1389, node1409, node1410, node1421, node1470, node1482, node1483, node1484, node1485, node1492, node1504, node1505, node1506, node1507, node1531, node2080, node2083, node2088, node2091, node2643, node2647, node2671, node2675, node2992, node3010, node3082, node3093, node3170, node3171, node3180, node3181, node3182, node3218, node3219, node3228, node3229, node3230, node3346, node3362, node3366, node3689, node3690, node3755, node3756, node3896, node3903, node3974, node3977, node3985, node3987]

theorem compactBlock011_inputs : ∀ p ∈ compactBlock011Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0402, node0438, node0687, node0691, node0694, node0697, node0710, node0711, node0750, node0755, node0760, node0761, node0779, node0782, node0791, node1191, node1211, node1212, node1213, node1221, node1222, node1244, node1245, node1248, node1249, node1255, node1256, node1293, node1294, node1296, node1300, node1301, node1303, node1320, node1322, node1327, node1329, node1337, node1338, node1377, node1378, node1389, node1409, node1410, node1421, node1470, node1482, node1483, node1484, node1485, node1492, node1504, node1505, node1506, node1507, node1531, node2080, node2083, node2088, node2091, node2643, node2647, node2671, node2675, node2992, node3010, node3082, node3093, node3170, node3171, node3180, node3181, node3182, node3218, node3219, node3228, node3229, node3230, node3346, node3362, node3366, node3689, node3690, node3755, node3756, node3896, node3903, node3974, node3977, node3985, node3987], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 402 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 438 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 687 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 691 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 694 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 697 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 710 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 711 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 750 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 755 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 760 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 761 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 779 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 782 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 791 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 90)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 92)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 96)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 98)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 93)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 89)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 91)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 74)
  exact nil_derived _ _

def compactBlock011Program : List Instruction := [
  ⟨81, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨72, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨75, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨68, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨21, 6, [(1,0,(0,0,0,0,0,0,0)),
  (6500,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨23, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((6750/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨25, 8, [(1,0,(0,0,0,0,0,0,0)),
  (676,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨91, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-12000/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨86, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨75, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨91, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨31, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((9/50),1,(1,-2,0,2,0,0,0))]⟩,
  ⟨20, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨34, 103, [(1,0,(0,0,0,0,0,0,0)),
  ((-4563/250),1,(1,-2,0,2,0,0,0))]⟩,
  ⟨20, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨38, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨22, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 34, [((-8/9),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨43, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨43, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/16),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨1, 37, [((-9),0,(0,-2,0,0,0,0,0))]⟩,
  ⟨35, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨48, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-208/27),1,(0,2,0,0,0,0,0))]⟩,
  ⟨8, 40, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 1, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨58, 119, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨117, 120, [(1,0,(0,0,0,0,0,0,0)),
  ((-100/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨97, 121, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨40, 122, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨43, 123, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨66, 124, [(1,0,(0,0,0,0,0,0,0)),
  ((13500/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨123, 125, [(1,0,(0,0,0,0,0,0,0)),
  ((-6000/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨103, 126, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨25, 127, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨9, 53, [((-1/2),0,(1,0,0,0,0,0,0))]⟩,
  ⟨76, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨68, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1/13),1,(0,0,1,0,0,0,0))]⟩,
  ⟨75, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨127, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨13, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨41, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨41, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨60, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨78, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨80, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((2/13),1,(0,0,1,0,0,0,0))]⟩,
  ⟨136, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1500/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨16, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((13500/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨42, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨42, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨16, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨13, 70, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨89, 0, [(1,0,(0,0,0,0,0,0,0)),
  (72,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨139, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨128, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨96, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-11232),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨98, 6, [(1,0,(0,0,0,0,0,0,0)),
  (208,1,(0,0,0,0,0,0,0))]⟩,
  ⟨147, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((12000/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨11, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨10, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨72, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨28, 83, [((-72),0,(-3,-2,0,0,0,0,0))]⟩,
  ⟨80, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨108, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((13/432),1,(3,2,0,0,0,0,0))]⟩,
  ⟨116, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨111, 31, [(1,0,(0,0,0,0,0,0,0)),
  (72,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨113, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-117),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨129, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨116, 34, [(1,0,(0,0,0,0,0,0,0)),
  (225,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨136, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨133, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨124, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-117),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨126, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((-117),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨128, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨130, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨139, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨144, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨25, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨83, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨25, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨40, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨130, 47, [(1,0,(0,0,0,0,0,0,0)),
  (11232,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨132, 48, [(1,0,(0,0,0,0,0,0,0)),
  (9126,1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨134, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-702000),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨153, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-2028),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨150, 51, [(1,0,(0,0,0,0,0,0,0)),
  (2028,1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨144, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-18252),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨146, 53, [(1,0,(0,0,0,0,0,0,0)),
  (18252,1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨148, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((-676),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨150, 55, [(1,0,(0,0,0,0,0,0,0)),
  (676,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨156, 56, [(1,0,(0,0,0,0,0,0,0)),
  ((-1014),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨161, 57, [(1,0,(0,0,0,0,0,0,0)),
  (1014,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨174, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-2028),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨176, 59, [(1,0,(0,0,0,0,0,0,0)),
  (2028,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨36, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨48, 61, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨37, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨182, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-104/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨108, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨120, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨186, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-16224/125),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨36, 123, [((-2),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨177, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨179, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨32, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-117),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨32, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-117),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨32, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨32, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨30, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨30, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨85, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨30, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨169, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨193, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-507/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨195, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((507/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨28, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-18252),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨28, 14, [(1,0,(0,0,0,0,0,0,0)),
  (18252,1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨28, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-676),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨28, 16, [(1,0,(0,0,0,0,0,0,0)),
  (676,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨26, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-2028),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨26, 18, [(1,0,(0,0,0,0,0,0,0)),
  (2028,1,(0,0,-1,0,0,0,0))]⟩
]

























































































































































def compactBlock011Indices : List ℕ := [127, 122, 121, 120, 119, 114, 113, 112, 106, 104, 103, 101, 100, 97, 95, 94, 92, 91, 85, 84, 80, 79, 78, 77, 76, 70, 68, 66, 65, 64, 61, 60, 58, 57, 55, 54, 53, 51, 50, 45, 44, 41, 39, 38, 37, 36, 35, 30, 29, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock011Results : List Poly :=
  program_results% (compactBlock011Inputs) (compactBlock011Program) (compactBlock011Indices)

def node3988 : Poly := rowAt compactBlock011Results 0
def node3996 : Poly := rowAt compactBlock011Results 1
def node3997 : Poly := rowAt compactBlock011Results 2
def node3998 : Poly := rowAt compactBlock011Results 3
def node3999 : Poly := rowAt compactBlock011Results 4
def node4005 : Poly := rowAt compactBlock011Results 5
def node4006 : Poly := rowAt compactBlock011Results 6
def node4009 : Poly := rowAt compactBlock011Results 7
def node4024 : Poly := rowAt compactBlock011Results 8
def node4026 : Poly := rowAt compactBlock011Results 9
def node4027 : Poly := rowAt compactBlock011Results 10
def node4031 : Poly := rowAt compactBlock011Results 11
def node4032 : Poly := rowAt compactBlock011Results 12
def node4038 : Poly := rowAt compactBlock011Results 13
def node4042 : Poly := rowAt compactBlock011Results 14
def node4043 : Poly := rowAt compactBlock011Results 15
def node4047 : Poly := rowAt compactBlock011Results 16
def node4048 : Poly := rowAt compactBlock011Results 17
def node4054 : Poly := rowAt compactBlock011Results 18
def node4055 : Poly := rowAt compactBlock011Results 19
def node4062 : Poly := rowAt compactBlock011Results 20
def node4063 : Poly := rowAt compactBlock011Results 21
def node4064 : Poly := rowAt compactBlock011Results 22
def node4065 : Poly := rowAt compactBlock011Results 23
def node4066 : Poly := rowAt compactBlock011Results 24
def node4075 : Poly := rowAt compactBlock011Results 25
def node4077 : Poly := rowAt compactBlock011Results 26
def node4083 : Poly := rowAt compactBlock011Results 27
def node4085 : Poly := rowAt compactBlock011Results 28
def node4086 : Poly := rowAt compactBlock011Results 29
def node4089 : Poly := rowAt compactBlock011Results 30
def node4090 : Poly := rowAt compactBlock011Results 31
def node4092 : Poly := rowAt compactBlock011Results 32
def node4093 : Poly := rowAt compactBlock011Results 33
def node4097 : Poly := rowAt compactBlock011Results 34
def node4098 : Poly := rowAt compactBlock011Results 35
def node4106 : Poly := rowAt compactBlock011Results 36
def node4111 : Poly := rowAt compactBlock011Results 37
def node4112 : Poly := rowAt compactBlock011Results 38
def node4119 : Poly := rowAt compactBlock011Results 39
def node4120 : Poly := rowAt compactBlock011Results 40
def node4127 : Poly := rowAt compactBlock011Results 41
def node4131 : Poly := rowAt compactBlock011Results 42
def node4132 : Poly := rowAt compactBlock011Results 43
def node4143 : Poly := rowAt compactBlock011Results 44
def node4144 : Poly := rowAt compactBlock011Results 45
def node4145 : Poly := rowAt compactBlock011Results 46
def node4152 : Poly := rowAt compactBlock011Results 47
def node4153 : Poly := rowAt compactBlock011Results 48
def node4160 : Poly := rowAt compactBlock011Results 49
def node4161 : Poly := rowAt compactBlock011Results 50
def node4162 : Poly := rowAt compactBlock011Results 51
def node4163 : Poly := rowAt compactBlock011Results 52
def node4164 : Poly := rowAt compactBlock011Results 53
def node4165 : Poly := rowAt compactBlock011Results 54
def node4166 : Poly := rowAt compactBlock011Results 55
def node4167 : Poly := rowAt compactBlock011Results 56
def node4177 : Poly := rowAt compactBlock011Results 57
def node4178 : Poly := rowAt compactBlock011Results 58
def node4179 : Poly := rowAt compactBlock011Results 59
def node4180 : Poly := rowAt compactBlock011Results 60
def node4181 : Poly := rowAt compactBlock011Results 61
def node4182 : Poly := rowAt compactBlock011Results 62
def node4185 : Poly := rowAt compactBlock011Results 63
def node4186 : Poly := rowAt compactBlock011Results 64
def node4187 : Poly := rowAt compactBlock011Results 65
def node4188 : Poly := rowAt compactBlock011Results 66
def node4191 : Poly := rowAt compactBlock011Results 67
def node4201 : Poly := rowAt compactBlock011Results 68
def node4202 : Poly := rowAt compactBlock011Results 69
def node4203 : Poly := rowAt compactBlock011Results 70
def node4204 : Poly := rowAt compactBlock011Results 71
def node4205 : Poly := rowAt compactBlock011Results 72
def node4206 : Poly := rowAt compactBlock011Results 73
def node4209 : Poly := rowAt compactBlock011Results 74
def node4210 : Poly := rowAt compactBlock011Results 75

theorem compactBlock011_certificate : outputs compactBlock011Inputs compactBlock011Program compactBlock011Indices = compactBlock011Results := by
  decide +kernel

theorem compactBlock011_derived : ∀ p ∈ compactBlock011Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock011_inputs compactBlock011Program compactBlock011Indices compactBlock011_certificate

#print axioms compactBlock011_derived


def compactBlock012Inputs : List Poly := [node0429, node0452, node0678, node0706, node0707, node0748, node0751, node0753, node0754, node0758, node0759, node0762, node0769, node0771, node0772, node0774, node0777, node0784, node1191, node1530, node1536, node1537, node1548, node1549, node1552, node1553, node1554, node1555, node1567, node1569, node1573, node1575, node1581, node1582, node1589, node1591, node1610, node1612, node1668, node1670, node1737, node1741, node1903, node2308, node2310, node2377, node2378, node2381, node2629, node2631, node2632, node2636, node2641, node2664, node2669, node2979, node2982, node2986, node2988, node3000, node3006, node3139, node3143, node3157, node3187, node3347, node3363, node3526, node3528, node3634, node3638, node3639, node3640, node3642, node3645, node3646, node3681, node3688, node3693, node3694, node3695, node3697, node3698, node3700, node3747, node3754, node3759, node3760, node3761, node3763, node3764, node3897, node3904, node3911, node3928, node3932, node3975, node3978, node3986, node4009, node4031, node4042, node4043, node4048, node4077, node4092, node4097, node4098, node4106, node4127, node4160, node4161, node4162, node4164, node4167, node4185, node4187, node4188]

theorem compactBlock012_inputs : ∀ p ∈ compactBlock012Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0429, node0452, node0678, node0706, node0707, node0748, node0751, node0753, node0754, node0758, node0759, node0762, node0769, node0771, node0772, node0774, node0777, node0784, node1191, node1530, node1536, node1537, node1548, node1549, node1552, node1553, node1554, node1555, node1567, node1569, node1573, node1575, node1581, node1582, node1589, node1591, node1610, node1612, node1668, node1670, node1737, node1741, node1903, node2308, node2310, node2377, node2378, node2381, node2629, node2631, node2632, node2636, node2641, node2664, node2669, node2979, node2982, node2986, node2988, node3000, node3006, node3139, node3143, node3157, node3187, node3347, node3363, node3526, node3528, node3634, node3638, node3639, node3640, node3642, node3645, node3646, node3681, node3688, node3693, node3694, node3695, node3697, node3698, node3700, node3747, node3754, node3759, node3760, node3761, node3763, node3764, node3897, node3904, node3911, node3928, node3932, node3975, node3978, node3986, node4009, node4031, node4042, node4043, node4048, node4077, node4092, node4097, node4098, node4106, node4127, node4160, node4161, node4162, node4164, node4167, node4185, node4187, node4188], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 429 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 452 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 678 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 706 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 707 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 748 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 751 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 753 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 754 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 758 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 759 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 762 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 769 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 771 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 772 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 774 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 777 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 784 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 90)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 66)
  exact nil_derived _ _

def compactBlock012Program : List Instruction := [
  ⟨103, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨113, 115, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨80, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨89, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-507/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨112, 22, [(26,0,(-1,0,-1,0,0,0,0))]⟩,
  ⟨24, 0, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨30, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨36, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨104, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-100/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨125, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨127, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨25, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨29, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨33, 8, [(1,0,(0,0,0,0,0,0,0)),
  (624,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨35, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-27/26),1,(1,0,1,0,0,0,0))]⟩,
  ⟨46, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-13500/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨113, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((6000/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨16, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨16, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨41, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 38, [((-9/8),0,(3,-2,0,0,0,0,0))]⟩,
  ⟨121, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-416/27),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨16, 41, [((-225/2),0,(1,-2,0,-2,0,0,0))]⟩,
  ⟨49, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((1/225),1,(0,2,0,2,0,0,0))]⟩,
  ⟨51, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/3375),1,(-1,2,0,2,0,0,0))]⟩,
  ⟨53, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-208/3375),1,(0,2,0,2,0,0,0))]⟩,
  ⟨59, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 3, [(1,0,(0,0,0,0,0,0,0)),
  (72,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨120, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨22, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨135, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨141, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨22, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨45, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨65, 10, [(1,0,(0,0,0,0,0,0,0)),
  (11232,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨128, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((1500/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨21, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-13500/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨148, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨150, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨21, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨13, 59, [((-50),0,(-1,0,0,-2,0,0,0))]⟩,
  ⟨76, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((13/250),1,(1,0,0,2,0,0,0))]⟩,
  ⟨1, 62, [((36/325),0,(-2,-2,1,2,0,0,0))]⟩,
  ⟨124, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨62, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨82, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((21125/108),1,(2,2,-1,-2,0,0,0))]⟩,
  ⟨135, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((507/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨114, 147, [(1,0,(0,0,0,0,0,0,0)),
  ((-104/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨163, 148, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨117, 149, [(1,0,(0,0,0,0,0,0,0)),
  ((16224/125),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨88, 159, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨43, 160, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨32, 161, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 73, [((-2),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨155, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨71, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨136, 77, [((-25/9),0,(0,2,0,-2,0,0,0))]⟩,
  ⟨145, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-5616/125),1,(0,-2,0,2,0,0,0))]⟩,
  ⟨117, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨105, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨75, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨102, 110, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨110, 111, [(1,0,(0,0,0,0,0,0,0)),
  ((9/100),1,(2,-2,0,2,0,0,0))]⟩,
  ⟨113, 112, [(1,0,(0,0,0,0,0,0,0)),
  ((4563/500),1,(2,-2,0,2,0,0,0))]⟩,
  ⟨128, 85, [((-25/72),0,(3,2,0,-2,0,0,0))]⟩,
  ⟨131, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨134, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-11232/125),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨140, 141, [(1,0,(0,0,0,0,0,0,0)),
  (25,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨153, 142, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨18, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨157, 144, [(1,0,(0,0,0,0,0,0,0)),
  ((-9750),1,(0,0,0,-2,0,0,0))]⟩,
  ⟨164, 145, [(1,0,(0,0,0,0,0,0,0)),
  ((-1500/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨6, 147, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 125, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨82, 150, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 79, [(1,0,(0,0,0,0,0,0,0)),
  ((100/9),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨23, 80, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 81, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨121, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((182000/27),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨165, 156, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨33, 157, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨93, 158, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 135, [(1,0,(0,0,0,0,0,0,0)),
  ((8/225),1,(-3,2,0,2,0,0,0))]⟩,
  ⟨141, 136, [(1,0,(0,0,0,0,0,0,0)),
  ((5408/3375),1,(-3,2,0,2,0,0,0))]⟩,
  ⟨203, 150, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 151, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨9, 152, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨29, 146, [(1,0,(0,0,0,0,0,0,0)),
  ((25/4),1,(2,0,0,-2,0,0,0))]⟩,
  ⟨97, 147, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨102, 148, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨199, 149, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨154, 150, [(1,0,(0,0,0,0,0,0,0)),
  ((-11375/4),1,(2,0,0,-2,0,0,0))]⟩,
  ⟨147, 146, [(1,0,(0,0,0,0,0,0,0)),
  ((-468/25),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨155, 147, [(1,0,(0,0,0,0,0,0,0)),
  ((-117/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨192, 148, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨101, 149, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨27, 150, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨111, 151, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨117, 152, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨156, 153, [(1,0,(0,0,0,0,0,0,0)),
  ((73008/125),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨164, 154, [(1,0,(0,0,0,0,0,0,0)),
  ((-18252/125),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨200, 155, [(1,0,(0,0,0,0,0,0,0)),
  ((-8112/125),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨182, 180, [(1,0,(0,0,0,0,0,0,0)),
  (50,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨187, 181, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨54, 182, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨35, 183, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨194, 184, [(1,0,(0,0,0,0,0,0,0)),
  ((-19500),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨199, 185, [(1,0,(0,0,0,0,0,0,0)),
  ((-750/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨35, 187, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨153, 114, [(1,0,(0,0,0,0,0,0,0)),
  (100,1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨156, 115, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨31, 116, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨7, 117, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨83, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨219, 119, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨221, 120, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 121, [(1,0,(0,0,0,0,0,0,0)),
  ((-78000),1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨211, 122, [(1,0,(0,0,0,0,0,0,0)),
  ((1500/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨104, 123, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨82, 124, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨45, 217, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨192, 143, [((-8/9),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨194, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨133, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩
]











































































































































































def compactBlock012Indices : List ℕ := [125, 124, 119, 116, 115, 114, 113, 111, 105, 102, 101, 98, 97, 96, 93, 92, 91, 90, 89, 88, 84, 82, 81, 80, 79, 78, 76, 70, 69, 67, 65, 64, 62, 61, 59, 57, 56, 53, 52, 48, 46, 45, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock012Results : List Poly :=
  program_results% (compactBlock012Inputs) (compactBlock012Program) (compactBlock012Indices)

def node4214 : Poly := rowAt compactBlock012Results 0
def node4216 : Poly := rowAt compactBlock012Results 1
def node4221 : Poly := rowAt compactBlock012Results 2
def node4226 : Poly := rowAt compactBlock012Results 3
def node4227 : Poly := rowAt compactBlock012Results 4
def node4228 : Poly := rowAt compactBlock012Results 5
def node4229 : Poly := rowAt compactBlock012Results 6
def node4231 : Poly := rowAt compactBlock012Results 7
def node4239 : Poly := rowAt compactBlock012Results 8
def node4242 : Poly := rowAt compactBlock012Results 9
def node4243 : Poly := rowAt compactBlock012Results 10
def node4246 : Poly := rowAt compactBlock012Results 11
def node4247 : Poly := rowAt compactBlock012Results 12
def node4248 : Poly := rowAt compactBlock012Results 13
def node4254 : Poly := rowAt compactBlock012Results 14
def node4255 : Poly := rowAt compactBlock012Results 15
def node4256 : Poly := rowAt compactBlock012Results 16
def node4257 : Poly := rowAt compactBlock012Results 17
def node4258 : Poly := rowAt compactBlock012Results 18
def node4259 : Poly := rowAt compactBlock012Results 19
def node4263 : Poly := rowAt compactBlock012Results 20
def node4267 : Poly := rowAt compactBlock012Results 21
def node4268 : Poly := rowAt compactBlock012Results 22
def node4269 : Poly := rowAt compactBlock012Results 23
def node4270 : Poly := rowAt compactBlock012Results 24
def node4271 : Poly := rowAt compactBlock012Results 25
def node4275 : Poly := rowAt compactBlock012Results 26
def node4286 : Poly := rowAt compactBlock012Results 27
def node4289 : Poly := rowAt compactBlock012Results 28
def node4300 : Poly := rowAt compactBlock012Results 29
def node4303 : Poly := rowAt compactBlock012Results 30
def node4305 : Poly := rowAt compactBlock012Results 31
def node4307 : Poly := rowAt compactBlock012Results 32
def node4308 : Poly := rowAt compactBlock012Results 33
def node4313 : Poly := rowAt compactBlock012Results 34
def node4315 : Poly := rowAt compactBlock012Results 35
def node4316 : Poly := rowAt compactBlock012Results 36
def node4320 : Poly := rowAt compactBlock012Results 37
def node4321 : Poly := rowAt compactBlock012Results 38
def node4326 : Poly := rowAt compactBlock012Results 39
def node4332 : Poly := rowAt compactBlock012Results 40
def node4333 : Poly := rowAt compactBlock012Results 41
def node4336 : Poly := rowAt compactBlock012Results 42
def node4338 : Poly := rowAt compactBlock012Results 43
def node4340 : Poly := rowAt compactBlock012Results 44
def node4342 : Poly := rowAt compactBlock012Results 45
def node4344 : Poly := rowAt compactBlock012Results 46
def node4345 : Poly := rowAt compactBlock012Results 47
def node4346 : Poly := rowAt compactBlock012Results 48
def node4349 : Poly := rowAt compactBlock012Results 49
def node4351 : Poly := rowAt compactBlock012Results 50
def node4352 : Poly := rowAt compactBlock012Results 51
def node4353 : Poly := rowAt compactBlock012Results 52
def node4354 : Poly := rowAt compactBlock012Results 53
def node4355 : Poly := rowAt compactBlock012Results 54
def node4356 : Poly := rowAt compactBlock012Results 55
def node4357 : Poly := rowAt compactBlock012Results 56
def node4358 : Poly := rowAt compactBlock012Results 57
def node4359 : Poly := rowAt compactBlock012Results 58
def node4361 : Poly := rowAt compactBlock012Results 59
def node4362 : Poly := rowAt compactBlock012Results 60
def node4363 : Poly := rowAt compactBlock012Results 61
def node4364 : Poly := rowAt compactBlock012Results 62
def node4365 : Poly := rowAt compactBlock012Results 63
def node4367 : Poly := rowAt compactBlock012Results 64
def node4368 : Poly := rowAt compactBlock012Results 65
def node4370 : Poly := rowAt compactBlock012Results 66
def node4375 : Poly := rowAt compactBlock012Results 67
def node4376 : Poly := rowAt compactBlock012Results 68
def node4379 : Poly := rowAt compactBlock012Results 69
def node4380 : Poly := rowAt compactBlock012Results 70
def node4381 : Poly := rowAt compactBlock012Results 71
def node4384 : Poly := rowAt compactBlock012Results 72
def node4385 : Poly := rowAt compactBlock012Results 73
def node4386 : Poly := rowAt compactBlock012Results 74
def node4389 : Poly := rowAt compactBlock012Results 75
def node4390 : Poly := rowAt compactBlock012Results 76
def node4391 : Poly := rowAt compactBlock012Results 77
def node4392 : Poly := rowAt compactBlock012Results 78
def node4393 : Poly := rowAt compactBlock012Results 79
def node4394 : Poly := rowAt compactBlock012Results 80
def node4395 : Poly := rowAt compactBlock012Results 81
def node4396 : Poly := rowAt compactBlock012Results 82
def node4397 : Poly := rowAt compactBlock012Results 83
def node4399 : Poly := rowAt compactBlock012Results 84

theorem compactBlock012_certificate : outputs compactBlock012Inputs compactBlock012Program compactBlock012Indices = compactBlock012Results := by
  decide +kernel

theorem compactBlock012_derived : ∀ p ∈ compactBlock012Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock012_inputs compactBlock012Program compactBlock012Indices compactBlock012_certificate

#print axioms compactBlock012_derived


def compactBlock013Inputs : List Poly := [node0649, node0664, node0665, node0692, node0693, node0699, node0700, node0717, node0724, node0764, node0766, node0767, node0775, node0780, node0781, node0783, node0792, node0793, node1191, node1904, node2376, node2380, node2633, node2659, node2661, node2980, node2981, node2985, node2998, node2999, node3136, node3145, node3147, node3148, node3149, node3151, node3154, node3165, node3168, node3174, node3193, node3196, node3197, node3202, node3213, node3216, node3222, node3336, node3337, node3338, node3339, node3344, node3345, node3352, node3353, node3360, node3445, node3447, node3527, node3529, node3532, node3533, node3647, node3648, node3653, node3654, node3655, node3660, node3664, node3691, node3714, node3721, node3726, node3757, node3780, node3783, node3893, node3900, node3926, node3929, node3930, node4026, node4090, node4177, node4186, node4201, node4210, node4226, node4227, node4267, node4268, node4270, node4305, node4307, node4316, node4321, node4338, node4340, node4342, node4344, node4345, node4346, node4352, node4356, node4359, node4362, node4370, node4380, node4381, node4384, node4385, node4386, node4390, node4392, node4393, node4394, node4396, node4399]

theorem compactBlock013_inputs : ∀ p ∈ compactBlock013Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0649, node0664, node0665, node0692, node0693, node0699, node0700, node0717, node0724, node0764, node0766, node0767, node0775, node0780, node0781, node0783, node0792, node0793, node1191, node1904, node2376, node2380, node2633, node2659, node2661, node2980, node2981, node2985, node2998, node2999, node3136, node3145, node3147, node3148, node3149, node3151, node3154, node3165, node3168, node3174, node3193, node3196, node3197, node3202, node3213, node3216, node3222, node3336, node3337, node3338, node3339, node3344, node3345, node3352, node3353, node3360, node3445, node3447, node3527, node3529, node3532, node3533, node3647, node3648, node3653, node3654, node3655, node3660, node3664, node3691, node3714, node3721, node3726, node3757, node3780, node3783, node3893, node3900, node3926, node3929, node3930, node4026, node4090, node4177, node4186, node4201, node4210, node4226, node4227, node4267, node4268, node4270, node4305, node4307, node4316, node4321, node4338, node4340, node4342, node4344, node4345, node4346, node4352, node4356, node4359, node4362, node4370, node4380, node4381, node4384, node4385, node4386, node4390, node4392, node4393, node4394, node4396, node4399], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 649 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 664 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 665 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 692 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 693 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 699 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 700 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 717 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 724 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 764 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 766 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 767 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 775 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 780 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 781 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 783 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 792 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 793 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 89)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 92)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 84)
  exact nil_derived _ _

def compactBlock013Program : List Instruction := [
  ⟨82, 116, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨10, 117, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨62, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((351/16),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨82, 65, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨11, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨122, 67, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨4, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨71, 26, [((-2),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨74, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨109, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨121, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨123, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨21, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨28, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨85, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((13/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨130, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨132, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨92, 36, [((-72/25),0,(-3,-2,0,2,0,0,0))]⟩,
  ⟨121, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨95, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((1625/432),1,(3,2,0,-2,0,0,0))]⟩,
  ⟨68, 39, [((-9/2),0,(1,-2,0,0,0,0,0))]⟩,
  ⟨71, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨74, 1, [(1,0,(0,0,0,0,0,0,0)),
  (8,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨130, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨78, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((52/27),1,(-1,2,0,0,0,0,0))]⟩,
  ⟨81, 4, [(1,0,(0,0,0,0,0,0,0)),
  (1248,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨103, 45, [((-50/9),0,(-1,2,0,-2,0,0,0))]⟩,
  ⟨105, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((351/250),1,(1,-2,0,2,0,0,0))]⟩,
  ⟨60, 47, [((-8),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨65, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨71, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((13/16),1,(3,0,0,0,0,0,0))]⟩,
  ⟨57, 50, [((-18),0,(-1,-2,0,0,0,0,0))]⟩,
  ⟨60, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨143, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨136, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨148, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨65, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((13/54),1,(1,2,0,0,0,0,0))]⟩,
  ⟨151, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((1500/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨61, 57, [((-200/9),0,(-3,2,0,-2,0,0,0))]⟩,
  ⟨43, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 1, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨66, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((351/2000),1,(3,-2,0,2,0,0,0))]⟩,
  ⟨79, 81, [(1,0,(0,0,0,0,0,0,0)),
  ((1/450),1,(1,2,0,2,0,0,0))]⟩,
  ⟨87, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/6750),1,(1,2,0,2,0,0,0))]⟩,
  ⟨65, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((25/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨150, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨147, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨12, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨136, 142, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨71, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-4875/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨146, 144, [(1,0,(0,0,0,0,0,0,0)),
  ((-1500/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨8, 70, [((-8),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨85, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨87, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/52),1,(2,-2,1,0,0,0,0))]⟩,
  ⟨96, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((27/52),1,(2,-2,1,0,0,0,0))]⟩,
  ⟨11, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/120),1,(3,0,0,0,0,0,0))]⟩,
  ⟨102, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-570375/4),1,(2,-2,0,-2,0,0,0))]⟩,
  ⟨63, 152, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨65, 166, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨97, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((1/225),1,(0,2,0,2,0,0,0))]⟩,
  ⟨105, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((52/3375),1,(0,2,0,2,0,0,0))]⟩,
  ⟨159, 80, [((-1/4),0,(2,0,0,0,0,0,0))]⟩,
  ⟨16, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨51, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨15, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨154, 3, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨90, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((43875/2),1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨166, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/15),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨17, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1500/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨52, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨179, 89, [((100/13),0,(-2,0,1,-2,0,0,0))]⟩,
  ⟨31, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨84, 1, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨90, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((169/500),1,(2,0,-1,2,0,0,0))]⟩,
  ⟨159, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨116, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/9),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨80, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨163, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨32, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-25),1,(0,0,0,-2,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨167, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-507/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨129, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-676/27),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨170, 29, [(1,0,(0,0,0,0,0,0,0)),
  (2028,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨133, 103, [((117/25),0,(0,-2,-1,2,0,0,0))]⟩,
  ⟨136, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨139, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨64, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨144, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((250/351),1,(0,2,1,-2,0,0,0))]⟩,
  ⟨147, 109, [((225/52),0,(2,-2,1,-2,0,0,0))]⟩,
  ⟨57, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨97, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨199, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨13, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨153, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/3375),1,(-2,2,-1,2,0,0,0))]⟩,
  ⟨163, 161, [(1,0,(0,0,0,0,0,0,0)),
  ((-117/4),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨165, 162, [(1,0,(0,0,0,0,0,0,0)),
  ((-325/4),1,(2,0,-1,-2,0,0,0))]⟩,
  ⟨167, 163, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨169, 164, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/8),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨101, 165, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨191, 166, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨193, 167, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨175, 168, [(1,0,(0,0,0,0,0,0,0)),
  ((4563/4),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨177, 169, [(1,0,(0,0,0,0,0,0,0)),
  ((-21125/4),1,(2,0,-1,-2,0,0,0))]⟩,
  ⟨179, 170, [(1,0,(0,0,0,0,0,0,0)),
  ((-507/16),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨198, 171, [(1,0,(0,0,0,0,0,0,0)),
  ((507/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨142, 126, [((36/13),0,(-2,-2,1,0,0,0,0))]⟩,
  ⟨8, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/8),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨6, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨153, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((169/108),1,(2,2,-1,0,0,0,0))]⟩,
  ⟨5, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-507/16),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨171, 131, [((52/25),0,(-2,0,-1,2,0,0,0))]⟩,
  ⟨173, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨207, 1, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨197, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨132, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨179, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((125/52),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨145, 137, [((25/13),0,(0,0,1,-2,0,0,0))]⟩,
  ⟨198, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨224, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-117/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨123, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨59, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨220, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨138, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨155, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((338/125),1,(0,0,-1,2,0,0,0))]⟩,
  ⟨207, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-2028/125),1,(-1,0,-1,2,0,0,0))]⟩
]





























































































































































































def compactBlock013Indices : List ℕ := [127, 125, 124, 123, 122, 121, 120, 118, 117, 114, 113, 112, 111, 108, 107, 105, 104, 102, 101, 99, 97, 96, 94, 91, 90, 89, 86, 85, 82, 79, 77, 74, 72, 71, 70, 69, 68, 67, 66, 63, 62, 61, 60, 59, 58, 57, 55, 54, 53, 52, 51, 50, 49, 48, 47, 45, 44, 43, 41, 40, 39, 38, 37, 35, 34, 33, 32, 31, 30, 29, 28, 26, 25, 23, 22, 20, 18, 17, 16, 15, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock013Results : List Poly :=
  program_results% (compactBlock013Inputs) (compactBlock013Program) (compactBlock013Indices)

def node4400 : Poly := rowAt compactBlock013Results 0
def node4402 : Poly := rowAt compactBlock013Results 1
def node4403 : Poly := rowAt compactBlock013Results 2
def node4404 : Poly := rowAt compactBlock013Results 3
def node4405 : Poly := rowAt compactBlock013Results 4
def node4406 : Poly := rowAt compactBlock013Results 5
def node4407 : Poly := rowAt compactBlock013Results 6
def node4413 : Poly := rowAt compactBlock013Results 7
def node4414 : Poly := rowAt compactBlock013Results 8
def node4419 : Poly := rowAt compactBlock013Results 9
def node4422 : Poly := rowAt compactBlock013Results 10
def node4423 : Poly := rowAt compactBlock013Results 11
def node4424 : Poly := rowAt compactBlock013Results 12
def node4427 : Poly := rowAt compactBlock013Results 13
def node4428 : Poly := rowAt compactBlock013Results 14
def node4430 : Poly := rowAt compactBlock013Results 15
def node4431 : Poly := rowAt compactBlock013Results 16
def node4435 : Poly := rowAt compactBlock013Results 17
def node4436 : Poly := rowAt compactBlock013Results 18
def node4439 : Poly := rowAt compactBlock013Results 19
def node4441 : Poly := rowAt compactBlock013Results 20
def node4443 : Poly := rowAt compactBlock013Results 21
def node4447 : Poly := rowAt compactBlock013Results 22
def node4453 : Poly := rowAt compactBlock013Results 23
def node4454 : Poly := rowAt compactBlock013Results 24
def node4455 : Poly := rowAt compactBlock013Results 25
def node4459 : Poly := rowAt compactBlock013Results 26
def node4461 : Poly := rowAt compactBlock013Results 27
def node4470 : Poly := rowAt compactBlock013Results 28
def node4473 : Poly := rowAt compactBlock013Results 29
def node4475 : Poly := rowAt compactBlock013Results 30
def node4480 : Poly := rowAt compactBlock013Results 31
def node4483 : Poly := rowAt compactBlock013Results 32
def node4484 : Poly := rowAt compactBlock013Results 33
def node4485 : Poly := rowAt compactBlock013Results 34
def node4487 : Poly := rowAt compactBlock013Results 35
def node4488 : Poly := rowAt compactBlock013Results 36
def node4490 : Poly := rowAt compactBlock013Results 37
def node4492 : Poly := rowAt compactBlock013Results 38
def node4500 : Poly := rowAt compactBlock013Results 39
def node4503 : Poly := rowAt compactBlock013Results 40
def node4504 : Poly := rowAt compactBlock013Results 41
def node4505 : Poly := rowAt compactBlock013Results 42
def node4506 : Poly := rowAt compactBlock013Results 43
def node4507 : Poly := rowAt compactBlock013Results 44
def node4508 : Poly := rowAt compactBlock013Results 45
def node4514 : Poly := rowAt compactBlock013Results 46
def node4515 : Poly := rowAt compactBlock013Results 47
def node4516 : Poly := rowAt compactBlock013Results 48
def node4517 : Poly := rowAt compactBlock013Results 49
def node4519 : Poly := rowAt compactBlock013Results 50
def node4520 : Poly := rowAt compactBlock013Results 51
def node4521 : Poly := rowAt compactBlock013Results 52
def node4523 : Poly := rowAt compactBlock013Results 53
def node4524 : Poly := rowAt compactBlock013Results 54
def node4528 : Poly := rowAt compactBlock013Results 55
def node4529 : Poly := rowAt compactBlock013Results 56
def node4531 : Poly := rowAt compactBlock013Results 57
def node4533 : Poly := rowAt compactBlock013Results 58
def node4534 : Poly := rowAt compactBlock013Results 59
def node4535 : Poly := rowAt compactBlock013Results 60
def node4536 : Poly := rowAt compactBlock013Results 61
def node4541 : Poly := rowAt compactBlock013Results 62
def node4544 : Poly := rowAt compactBlock013Results 63
def node4545 : Poly := rowAt compactBlock013Results 64
def node4547 : Poly := rowAt compactBlock013Results 65
def node4548 : Poly := rowAt compactBlock013Results 66
def node4549 : Poly := rowAt compactBlock013Results 67
def node4550 : Poly := rowAt compactBlock013Results 68
def node4552 : Poly := rowAt compactBlock013Results 69
def node4553 : Poly := rowAt compactBlock013Results 70
def node4555 : Poly := rowAt compactBlock013Results 71
def node4556 : Poly := rowAt compactBlock013Results 72
def node4560 : Poly := rowAt compactBlock013Results 73
def node4562 : Poly := rowAt compactBlock013Results 74
def node4564 : Poly := rowAt compactBlock013Results 75
def node4566 : Poly := rowAt compactBlock013Results 76
def node4567 : Poly := rowAt compactBlock013Results 77
def node4568 : Poly := rowAt compactBlock013Results 78
def node4569 : Poly := rowAt compactBlock013Results 79
def node4571 : Poly := rowAt compactBlock013Results 80
def node4573 : Poly := rowAt compactBlock013Results 81
def node4574 : Poly := rowAt compactBlock013Results 82
def node4575 : Poly := rowAt compactBlock013Results 83
def node4576 : Poly := rowAt compactBlock013Results 84
def node4577 : Poly := rowAt compactBlock013Results 85
def node4578 : Poly := rowAt compactBlock013Results 86
def node4579 : Poly := rowAt compactBlock013Results 87
def node4580 : Poly := rowAt compactBlock013Results 88
def node4582 : Poly := rowAt compactBlock013Results 89
def node4584 : Poly := rowAt compactBlock013Results 90
def node4585 : Poly := rowAt compactBlock013Results 91
def node4586 : Poly := rowAt compactBlock013Results 92
def node4587 : Poly := rowAt compactBlock013Results 93

theorem compactBlock013_certificate : outputs compactBlock013Inputs compactBlock013Program compactBlock013Indices = compactBlock013Results := by
  decide +kernel

theorem compactBlock013_derived : ∀ p ∈ compactBlock013Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock013_inputs compactBlock013Program compactBlock013Indices compactBlock013_certificate

#print axioms compactBlock013_derived


def compactBlock014Inputs : List Poly := [node0487, node0634, node0726, node0727, node0747, node0768, node0785, node0787, node1191, node2078, node2079, node2086, node2087, node2309, node2311, node2313, node2316, node2635, node2660, node3150, node3153, node3164, node3199, node3201, node3212, node3354, node3431, node3481, node3534, node3656, node3661, node3662, node3683, node3684, node3692, node3696, node3708, node3720, node3728, node3741, node3758, node3927, node3931, node3964, node3965, node3968, node3988, node4054, node4075, node4111, node4112, node4119, node4120, node4144, node4145, node4152, node4153, node4165, node4178, node4202, node4209, node4214, node4216, node4271, node4275, node4300, node4303, node4336, node4355, node4357, node4358, node4361, node4363, node4364, node4365, node4397, node4403, node4406, node4413, node4414, node4430, node4441, node4459, node4461, node4473, node4488, node4514, node4515, node4516, node4520, node4521, node4523, node4524, node4529, node4531, node4535, node4544, node4545, node4547, node4548, node4550, node4552, node4555, node4567, node4577, node4579, node4580, node4582, node4584, node4585]

theorem compactBlock014_inputs : ∀ p ∈ compactBlock014Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0487, node0634, node0726, node0727, node0747, node0768, node0785, node0787, node1191, node2078, node2079, node2086, node2087, node2309, node2311, node2313, node2316, node2635, node2660, node3150, node3153, node3164, node3199, node3201, node3212, node3354, node3431, node3481, node3534, node3656, node3661, node3662, node3683, node3684, node3692, node3696, node3708, node3720, node3728, node3741, node3758, node3927, node3931, node3964, node3965, node3968, node3988, node4054, node4075, node4111, node4112, node4119, node4120, node4144, node4145, node4152, node4153, node4165, node4178, node4202, node4209, node4214, node4216, node4271, node4275, node4300, node4303, node4336, node4355, node4357, node4358, node4361, node4363, node4364, node4365, node4397, node4403, node4406, node4413, node4414, node4430, node4441, node4459, node4461, node4473, node4488, node4514, node4515, node4516, node4520, node4521, node4523, node4524, node4529, node4531, node4535, node4544, node4545, node4547, node4548, node4550, node4552, node4555, node4567, node4577, node4579, node4580, node4582, node4584, node4585], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 487 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 634 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 726 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 727 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 747 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 768 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 785 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 787 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 89)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 94)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 95)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 91)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 89)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 90)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 91)
  exact nil_derived _ _

def compactBlock014Program : List Instruction := [
  ⟨73, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((-18252/125),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨69, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-104),1,(-3,0,-1,0,0,0,0))]⟩,
  ⟨3, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨52, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨109, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨57, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨75, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-104/9),1,(-3,2,-1,0,0,0,0))]⟩,
  ⟨77, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨87, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨116, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨105, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨97, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-200/9),1,(-3,2,0,-2,0,0,0))]⟩,
  ⟨83, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨95, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((200/3),1,(-3,1,0,-2,1,0,0))]⟩,
  ⟨112, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-50),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨72, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-25),1,(0,0,0,-2,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨34, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((6500/27),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨100, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((39/10),1,(0,0,0,0,0,0,0))]⟩,
  ⟨90, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((16224/5),1,(-3,0,-1,0,0,0,0))]⟩,
  ⟨72, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((-2028),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨19, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-4056/5),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨77, 38, [(1,0,(0,0,0,0,0,0,0)),
  (1014,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨96, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-5408/15),1,(-3,2,-1,0,0,0,0))]⟩,
  ⟨83, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-2028),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨70, 67, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨13, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨13, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨116, 71, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 37, [((100/117),0,(-2,2,1,-2,0,0,0))]⟩,
  ⟨78, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨119, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨40, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨79, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((4563/500),1,(2,-2,-1,2,0,0,0))]⟩,
  ⟨44, 43, [((9/13),0,(0,-2,1,0,0,0,0))]⟩,
  ⟨46, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-325/9),1,(0,2,-1,-2,0,0,0))]⟩,
  ⟨34, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨128, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/9),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨91, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨132, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨26, 6, [(1,0,(0,0,0,0,0,0,0)),
  (5,1,(0,0,0,-1,0,1,0))]⟩,
  ⟨54, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((338/27),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨56, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-42250/27),1,(0,2,-1,-2,0,0,0))]⟩,
  ⟨99, 9, [(1,0,(0,0,0,0,0,0,0)),
  (2028,1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨139, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-676/27),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨102, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1014),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨142, 12, [(1,0,(0,0,0,0,0,0,0)),
  (2028,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨90, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨64, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-117/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨157, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨148, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨163, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨97, 55, [(1,0,(0,0,0,0,0,0,0)),
  ((2028/125),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨72, 56, [(1,0,(0,0,0,0,0,0,0)),
  ((18252/125),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨132, 65, [((25/52),0,(2,0,1,-2,0,0,0))]⟩,
  ⟨105, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 2, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨67, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨90, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/125),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨97, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/8),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨104, 83, [(1,0,(0,0,0,0,0,0,0)),
  ((507/16),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨143, 73, [((4/13),0,(-2,0,1,0,0,0,0))]⟩,
  ⟨97, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-117/4),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨3, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/8),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨170, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨130, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨17, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/8),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨138, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/8),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨18, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/8),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨176, 7, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨45, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-25),1,(0,0,0,-2,0,0,0)),
  (5,1,(0,0,0,-1,0,1,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨111, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-43875/16),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨113, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((169/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨115, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-4563/4),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨117, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((570375/16),1,(3,-2,-1,-2,0,0,0))]⟩,
  ⟨14, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((507/16),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨142, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-507/4),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨71, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨179, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨70, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨164, 92, [((25/117),0,(0,2,1,-2,0,0,0))]⟩,
  ⟨148, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-104/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨113, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨35, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨123, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨34, 4, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨115, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((9126/125),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨155, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((16224/125),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨173, 100, [((9/52),0,(2,-2,1,0,0,0,0))]⟩,
  ⟨113, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1300/9),1,(-2,2,-1,-2,0,0,0))]⟩,
  ⟨115, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((100/9),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨153, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨186, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨197, 5, [(1,0,(0,0,0,0,0,0,0)),
  (5,1,(0,0,0,-1,0,1,0))]⟩,
  ⟨121, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/27),1,(-2,2,-1,0,0,0,0))]⟩,
  ⟨123, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-338000/27),1,(-2,2,-1,-2,0,0,0))]⟩,
  ⟨125, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((26000/27),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨161, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((507/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨79, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-2028),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨181, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨197, 205, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨190, 206, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨109, 207, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨80, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨194, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨142, 211, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨78, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨125, 75, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨146, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨118, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨121, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨182, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-624/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨184, 126, [((25/468),0,(2,2,1,-2,0,0,0))]⟩,
  ⟨68, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-117/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨196, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨61, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨39, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨63, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 6, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨141, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-73008/125),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨70, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((18252/125),1,(0,-2,-1,2,0,0,0))]⟩
]



















































































































































































def compactBlock014Indices : List ℕ := [124, 123, 122, 121, 117, 111, 110, 109, 108, 107, 106, 105, 103, 101, 97, 96, 94, 93, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 72, 69, 65, 60, 59, 58, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 42, 41, 40, 39, 38, 37, 36, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock014Results : List Poly :=
  program_results% (compactBlock014Inputs) (compactBlock014Program) (compactBlock014Indices)

def node4595 : Poly := rowAt compactBlock014Results 0
def node4596 : Poly := rowAt compactBlock014Results 1
def node4600 : Poly := rowAt compactBlock014Results 2
def node4601 : Poly := rowAt compactBlock014Results 3
def node4606 : Poly := rowAt compactBlock014Results 4
def node4617 : Poly := rowAt compactBlock014Results 5
def node4618 : Poly := rowAt compactBlock014Results 6
def node4619 : Poly := rowAt compactBlock014Results 7
def node4623 : Poly := rowAt compactBlock014Results 8
def node4624 : Poly := rowAt compactBlock014Results 9
def node4627 : Poly := rowAt compactBlock014Results 10
def node4628 : Poly := rowAt compactBlock014Results 11
def node4632 : Poly := rowAt compactBlock014Results 12
def node4634 : Poly := rowAt compactBlock014Results 13
def node4638 : Poly := rowAt compactBlock014Results 14
def node4639 : Poly := rowAt compactBlock014Results 15
def node4641 : Poly := rowAt compactBlock014Results 16
def node4643 : Poly := rowAt compactBlock014Results 17
def node4646 : Poly := rowAt compactBlock014Results 18
def node4647 : Poly := rowAt compactBlock014Results 19
def node4648 : Poly := rowAt compactBlock014Results 20
def node4650 : Poly := rowAt compactBlock014Results 21
def node4652 : Poly := rowAt compactBlock014Results 22
def node4654 : Poly := rowAt compactBlock014Results 23
def node4655 : Poly := rowAt compactBlock014Results 24
def node4656 : Poly := rowAt compactBlock014Results 25
def node4657 : Poly := rowAt compactBlock014Results 26
def node4658 : Poly := rowAt compactBlock014Results 27
def node4660 : Poly := rowAt compactBlock014Results 28
def node4662 : Poly := rowAt compactBlock014Results 29
def node4663 : Poly := rowAt compactBlock014Results 30
def node4673 : Poly := rowAt compactBlock014Results 31
def node4677 : Poly := rowAt compactBlock014Results 32
def node4685 : Poly := rowAt compactBlock014Results 33
def node4696 : Poly := rowAt compactBlock014Results 34
def node4697 : Poly := rowAt compactBlock014Results 35
def node4698 : Poly := rowAt compactBlock014Results 36
def node4700 : Poly := rowAt compactBlock014Results 37
def node4702 : Poly := rowAt compactBlock014Results 38
def node4704 : Poly := rowAt compactBlock014Results 39
def node4706 : Poly := rowAt compactBlock014Results 40
def node4707 : Poly := rowAt compactBlock014Results 41
def node4708 : Poly := rowAt compactBlock014Results 42
def node4711 : Poly := rowAt compactBlock014Results 43
def node4712 : Poly := rowAt compactBlock014Results 44
def node4713 : Poly := rowAt compactBlock014Results 45
def node4714 : Poly := rowAt compactBlock014Results 46
def node4715 : Poly := rowAt compactBlock014Results 47
def node4716 : Poly := rowAt compactBlock014Results 48
def node4720 : Poly := rowAt compactBlock014Results 49
def node4721 : Poly := rowAt compactBlock014Results 50
def node4722 : Poly := rowAt compactBlock014Results 51
def node4723 : Poly := rowAt compactBlock014Results 52
def node4729 : Poly := rowAt compactBlock014Results 53
def node4730 : Poly := rowAt compactBlock014Results 54
def node4731 : Poly := rowAt compactBlock014Results 55
def node4736 : Poly := rowAt compactBlock014Results 56
def node4737 : Poly := rowAt compactBlock014Results 57
def node4740 : Poly := rowAt compactBlock014Results 58
def node4742 : Poly := rowAt compactBlock014Results 59
def node4746 : Poly := rowAt compactBlock014Results 60
def node4747 : Poly := rowAt compactBlock014Results 61
def node4748 : Poly := rowAt compactBlock014Results 62
def node4749 : Poly := rowAt compactBlock014Results 63
def node4750 : Poly := rowAt compactBlock014Results 64
def node4753 : Poly := rowAt compactBlock014Results 65
def node4755 : Poly := rowAt compactBlock014Results 66
def node4756 : Poly := rowAt compactBlock014Results 67
def node4758 : Poly := rowAt compactBlock014Results 68
def node4761 : Poly := rowAt compactBlock014Results 69
def node4762 : Poly := rowAt compactBlock014Results 70
def node4763 : Poly := rowAt compactBlock014Results 71
def node4764 : Poly := rowAt compactBlock014Results 72
def node4765 : Poly := rowAt compactBlock014Results 73
def node4766 : Poly := rowAt compactBlock014Results 74
def node4769 : Poly := rowAt compactBlock014Results 75
def node4771 : Poly := rowAt compactBlock014Results 76
def node4773 : Poly := rowAt compactBlock014Results 77
def node4776 : Poly := rowAt compactBlock014Results 78
def node4778 : Poly := rowAt compactBlock014Results 79
def node4779 : Poly := rowAt compactBlock014Results 80
def node4780 : Poly := rowAt compactBlock014Results 81
def node4781 : Poly := rowAt compactBlock014Results 82
def node4782 : Poly := rowAt compactBlock014Results 83
def node4784 : Poly := rowAt compactBlock014Results 84
def node4785 : Poly := rowAt compactBlock014Results 85
def node4786 : Poly := rowAt compactBlock014Results 86
def node4787 : Poly := rowAt compactBlock014Results 87
def node4788 : Poly := rowAt compactBlock014Results 88

theorem compactBlock014_certificate : outputs compactBlock014Inputs compactBlock014Program compactBlock014Indices = compactBlock014Results := by
  decide +kernel

theorem compactBlock014_derived : ∀ p ∈ compactBlock014Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock014_inputs compactBlock014Program compactBlock014Indices compactBlock014_certificate

#print axioms compactBlock014_derived


def compactBlock015Inputs : List Poly := [node0786, node1191, node2314, node2315, node2382, node2642, node2977, node2995, node3003, node3004, node3159, node3184, node3207, node3355, node3361, node3666, node3671, node3673, node3676, node3687, node3702, node3730, node3732, node3737, node3739, node3742, node3749, node3750, node3762, node3781, node3792, node3894, node3933, node3938, node3940, node4005, node4062, node4089, node4246, node4248, node4258, node4259, node4289, node4308, node4313, node4315, node4326, node4349, node4351, node4367, node4379, node4395, node4405, node4407, node4422, node4424, node4427, node4431, node4447, node4455, node4470, node4475, node4480, node4487, node4490, node4492, node4500, node4503, node4507, node4508, node4533, node4534, node4536, node4553, node4556, node4571, node4573, node4574, node4575, node4576, node4601, node4606, node4639, node4641, node4648, node4650, node4652, node4654, node4700, node4715, node4716, node4721, node4723, node4729, node4746, node4756, node4762, node4763, node4765, node4766, node4769, node4778, node4779, node4780, node4781, node4782, node4784, node4785, node4786, node4787, node4788]

theorem compactBlock015_inputs : ∀ p ∈ compactBlock015Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0786, node1191, node2314, node2315, node2382, node2642, node2977, node2995, node3003, node3004, node3159, node3184, node3207, node3355, node3361, node3666, node3671, node3673, node3676, node3687, node3702, node3730, node3732, node3737, node3739, node3742, node3749, node3750, node3762, node3781, node3792, node3894, node3933, node3938, node3940, node4005, node4062, node4089, node4246, node4248, node4258, node4259, node4289, node4308, node4313, node4315, node4326, node4349, node4351, node4367, node4379, node4395, node4405, node4407, node4422, node4424, node4427, node4431, node4447, node4455, node4470, node4475, node4480, node4487, node4490, node4492, node4500, node4503, node4507, node4508, node4533, node4534, node4536, node4553, node4556, node4571, node4573, node4574, node4575, node4576, node4601, node4606, node4639, node4641, node4648, node4650, node4652, node4654, node4700, node4715, node4716, node4721, node4723, node4729, node4746, node4756, node4762, node4763, node4765, node4766, node4769, node4778, node4779, node4780, node4781, node4782, node4784, node4785, node4786, node4787, node4788], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 786 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 88)
  exact nil_derived _ _

def compactBlock015Program : List Instruction := [
  ⟨32, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((8112/125),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨59, 2, [((-25/2),0,(1,0,0,-2,0,0,0))]⟩,
  ⟨10, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/125),1,(-1,0,0,2,0,0,0))]⟩,
  ⟨66, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨101, 5, [((-1/50),0,(1,0,0,2,0,0,0))]⟩,
  ⟨90, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨102, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨74, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨45, 4, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨36, 5, [(1,0,(0,0,0,0,0,0,0)),
  (19500,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨51, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨53, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨82, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨112, 15, [((-8/25),0,(-3,0,0,2,0,0,0))]⟩,
  ⟨117, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((9/4),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨119, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨121, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((25/52),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨123, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((25/52),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨125, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((225/52),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨96, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨128, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((25/52),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨130, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-75/52),1,(2,-1,1,-2,1,0,0))]⟩,
  ⟨132, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((1404/5),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨26, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((4875/16),1,(3,0,0,-2,0,0,0))]⟩,
  ⟨28, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-5616),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨136, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/5),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨26, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨127, 29, [((-1/2),0,(1,0,0,0,0,0,0))]⟩,
  ⟨10, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨111, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨103, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨22, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨60, 4, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨93, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((1500/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨106, 36, [((-8),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨36, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((39/16),1,(3,0,0,0,0,0,0))]⟩,
  ⟨56, 39, [((450/13),0,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨129, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨17, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨135, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨67, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/6750),1,(1,2,-1,2,0,0,0))]⟩,
  ⟨49, 44, [((1800/13),0,(-3,-2,1,-2,0,0,0))]⟩,
  ⟨127, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨52, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/54000),1,(3,2,-1,2,0,0,0))]⟩,
  ⟨93, 47, [((9/25),0,(0,-2,0,2,0,0,0))]⟩,
  ⟨39, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨148, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨103, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨59, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-26000/27),1,(0,2,0,-2,0,0,0))]⟩,
  ⟨97, 52, [((1/25),0,(0,0,0,2,0,0,0))]⟩,
  ⟨112, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((225/8),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨142, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/52),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨6, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/4),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨6, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/4),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨98, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨124, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/4),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨111, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨22, 7, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨121, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-43875/8),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨104, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((4563/20),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨66, 10, [(1,0,(0,0,0,0,0,0,0)),
  (26000,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨131, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-3375/13),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨128, 65, [((-36),0,(-2,-2,0,0,0,0,0))]⟩,
  ⟨143, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((4875/4),1,(2,0,0,-2,0,0,0))]⟩,
  ⟨132, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((13/135),1,(2,2,0,0,0,0,0))]⟩,
  ⟨64, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨165, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨118, 127, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨144, 72, [((-225/8),0,(3,-2,0,-2,0,0,0))]⟩,
  ⟨18, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨167, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨162, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨97, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-416/3375),1,(-3,2,0,2,0,0,0))]⟩,
  ⟨92, 78, [((-25/2),0,(1,0,0,-2,0,0,0))]⟩,
  ⟨100, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/125),1,(-1,0,0,2,0,0,0))]⟩,
  ⟨123, 80, [((72/25),0,(-3,-2,0,2,0,0,0))]⟩,
  ⟨130, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/72),1,(3,2,0,-2,0,0,0))]⟩,
  ⟨133, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨127, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨134, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨154, 85, [((-2/9),0,(-1,2,0,0,0,0,0))]⟩,
  ⟨169, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨160, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨79, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨39, 4, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨103, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨146, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨78, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨130, 123, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨35, 124, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨130, 124, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 97, [((-8/9),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨177, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨154, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨78, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨34, 3, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨124, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((351/16),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨177, 103, [((-25/52),0,(2,0,1,-2,0,0,0))]⟩,
  ⟨141, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨195, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨87, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨86, 3, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨7, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/25),1,(-2,-1,-1,2,1,0,0))]⟩,
  ⟨185, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((52/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨8, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((468/25),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨69, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨190, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨145, 113, [((-25/18),0,(1,2,0,-2,0,0,0))]⟩,
  ⟨147, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((1404/125),1,(-1,-2,0,2,0,0,0))]⟩,
  ⟨131, 115, [((-9/2),0,(1,-2,0,0,0,0,0))]⟩,
  ⟨207, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨84, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨137, 2, [(1,0,(0,0,0,0,0,0,0)),
  (19500,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨142, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((52/27),1,(-1,2,0,0,0,0,0))]⟩,
  ⟨147, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((750/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨130, 121, [((-18),0,(-1,-2,0,0,0,0,0))]⟩,
  ⟨207, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨135, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((13/54),1,(1,2,0,0,0,0,0))]⟩,
  ⟨84, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨187, 126, [((25/13),0,(0,0,1,-2,0,0,0))]⟩,
  ⟨208, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨82, 1, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩
]





































































































































































def compactBlock015Indices : List ℕ := [125, 122, 121, 117, 116, 115, 112, 111, 106, 104, 103, 102, 101, 100, 98, 95, 94, 93, 90, 86, 85, 82, 77, 73, 71, 70, 68, 67, 66, 65, 64, 61, 60, 59, 58, 57, 55, 54, 53, 52, 51, 49, 47, 46, 45, 44, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 30, 29, 26, 24, 23, 22, 21, 20, 19, 18, 17, 16, 14, 12, 11, 10, 9, 8, 6, 5, 4, 3, 2, 1, 0]
def compactBlock015Results : List Poly :=
  program_results% (compactBlock015Inputs) (compactBlock015Program) (compactBlock015Indices)

def node4798 : Poly := rowAt compactBlock015Results 0
def node4805 : Poly := rowAt compactBlock015Results 1
def node4806 : Poly := rowAt compactBlock015Results 2
def node4816 : Poly := rowAt compactBlock015Results 3
def node4818 : Poly := rowAt compactBlock015Results 4
def node4819 : Poly := rowAt compactBlock015Results 5
def node4822 : Poly := rowAt compactBlock015Results 6
def node4823 : Poly := rowAt compactBlock015Results 7
def node4830 : Poly := rowAt compactBlock015Results 8
def node4832 : Poly := rowAt compactBlock015Results 9
def node4833 : Poly := rowAt compactBlock015Results 10
def node4834 : Poly := rowAt compactBlock015Results 11
def node4835 : Poly := rowAt compactBlock015Results 12
def node4836 : Poly := rowAt compactBlock015Results 13
def node4838 : Poly := rowAt compactBlock015Results 14
def node4844 : Poly := rowAt compactBlock015Results 15
def node4845 : Poly := rowAt compactBlock015Results 16
def node4846 : Poly := rowAt compactBlock015Results 17
def node4850 : Poly := rowAt compactBlock015Results 18
def node4862 : Poly := rowAt compactBlock015Results 19
def node4863 : Poly := rowAt compactBlock015Results 20
def node4867 : Poly := rowAt compactBlock015Results 21
def node4874 : Poly := rowAt compactBlock015Results 22
def node4878 : Poly := rowAt compactBlock015Results 23
def node4881 : Poly := rowAt compactBlock015Results 24
def node4882 : Poly := rowAt compactBlock015Results 25
def node4884 : Poly := rowAt compactBlock015Results 26
def node4885 : Poly := rowAt compactBlock015Results 27
def node4886 : Poly := rowAt compactBlock015Results 28
def node4887 : Poly := rowAt compactBlock015Results 29
def node4888 : Poly := rowAt compactBlock015Results 30
def node4892 : Poly := rowAt compactBlock015Results 31
def node4893 : Poly := rowAt compactBlock015Results 32
def node4894 : Poly := rowAt compactBlock015Results 33
def node4896 : Poly := rowAt compactBlock015Results 34
def node4901 : Poly := rowAt compactBlock015Results 35
def node4912 : Poly := rowAt compactBlock015Results 36
def node4913 : Poly := rowAt compactBlock015Results 37
def node4914 : Poly := rowAt compactBlock015Results 38
def node4915 : Poly := rowAt compactBlock015Results 39
def node4916 : Poly := rowAt compactBlock015Results 40
def node4921 : Poly := rowAt compactBlock015Results 41
def node4928 : Poly := rowAt compactBlock015Results 42
def node4929 : Poly := rowAt compactBlock015Results 43
def node4931 : Poly := rowAt compactBlock015Results 44
def node4932 : Poly := rowAt compactBlock015Results 45
def node4935 : Poly := rowAt compactBlock015Results 46
def node4936 : Poly := rowAt compactBlock015Results 47
def node4937 : Poly := rowAt compactBlock015Results 48
def node4938 : Poly := rowAt compactBlock015Results 49
def node4944 : Poly := rowAt compactBlock015Results 50
def node4945 : Poly := rowAt compactBlock015Results 51
def node4947 : Poly := rowAt compactBlock015Results 52
def node4948 : Poly := rowAt compactBlock015Results 53
def node4949 : Poly := rowAt compactBlock015Results 54
def node4950 : Poly := rowAt compactBlock015Results 55
def node4952 : Poly := rowAt compactBlock015Results 56
def node4955 : Poly := rowAt compactBlock015Results 57
def node4956 : Poly := rowAt compactBlock015Results 58
def node4959 : Poly := rowAt compactBlock015Results 59
def node4961 : Poly := rowAt compactBlock015Results 60
def node4962 : Poly := rowAt compactBlock015Results 61
def node4963 : Poly := rowAt compactBlock015Results 62
def node4967 : Poly := rowAt compactBlock015Results 63
def node4968 : Poly := rowAt compactBlock015Results 64
def node4969 : Poly := rowAt compactBlock015Results 65
def node4970 : Poly := rowAt compactBlock015Results 66
def node4971 : Poly := rowAt compactBlock015Results 67
def node4972 : Poly := rowAt compactBlock015Results 68
def node4975 : Poly := rowAt compactBlock015Results 69
def node4983 : Poly := rowAt compactBlock015Results 70
def node4984 : Poly := rowAt compactBlock015Results 71
def node4987 : Poly := rowAt compactBlock015Results 72
def node4988 : Poly := rowAt compactBlock015Results 73
def node4989 : Poly := rowAt compactBlock015Results 74
def node4994 : Poly := rowAt compactBlock015Results 75
def node4997 : Poly := rowAt compactBlock015Results 76
def node4999 : Poly := rowAt compactBlock015Results 77
def node5004 : Poly := rowAt compactBlock015Results 78
def node5009 : Poly := rowAt compactBlock015Results 79
def node5010 : Poly := rowAt compactBlock015Results 80
def node5011 : Poly := rowAt compactBlock015Results 81

theorem compactBlock015_certificate : outputs compactBlock015Inputs compactBlock015Program compactBlock015Indices = compactBlock015Results := by
  decide +kernel

theorem compactBlock015_derived : ∀ p ∈ compactBlock015Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock015_inputs compactBlock015Program compactBlock015Indices compactBlock015_certificate

#print axioms compactBlock015_derived


def compactBlock016Inputs : List Poly := [node0570, node0714, node0736, node1191, node2657, node2663, node2670, node3195, node3342, node3358, node3569, node3674, node3704, node3719, node3740, node3753, node3803, node3804, node3867, node3868, node3872, node4038, node4055, node4179, node4180, node4181, node4221, node4247, node4320, node4332, node4404, node4419, node4504, node4505, node4506, node4560, node4562, node4564, node4566, node4569, node4595, node4596, node4600, node4617, node4618, node4619, node4623, node4624, node4627, node4628, node4634, node4646, node4663, node4696, node4697, node4704, node4706, node4736, node4742, node4753, node4755, node4758, node4761, node4764, node4773, node4805, node4806, node4816, node4818, node4819, node4823, node4830, node4836, node4838, node4844, node4846, node4862, node4878, node4882, node4884, node4888, node4894, node4896, node4901, node4913, node4914, node4915, node4916, node4929, node4936, node4937, node4938, node4944, node4947, node4948, node4950, node4955, node4956, node4963, node4967, node4970, node4984, node4994, node4997, node5004, node5009, node5010, node5011]

theorem compactBlock016_inputs : ∀ p ∈ compactBlock016Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0570, node0714, node0736, node1191, node2657, node2663, node2670, node3195, node3342, node3358, node3569, node3674, node3704, node3719, node3740, node3753, node3803, node3804, node3867, node3868, node3872, node4038, node4055, node4179, node4180, node4181, node4221, node4247, node4320, node4332, node4404, node4419, node4504, node4505, node4506, node4560, node4562, node4564, node4566, node4569, node4595, node4596, node4600, node4617, node4618, node4619, node4623, node4624, node4627, node4628, node4634, node4646, node4663, node4696, node4697, node4704, node4706, node4736, node4742, node4753, node4755, node4758, node4761, node4764, node4773, node4805, node4806, node4816, node4818, node4819, node4823, node4830, node4836, node4838, node4844, node4846, node4862, node4878, node4882, node4884, node4888, node4894, node4896, node4901, node4913, node4914, node4915, node4916, node4929, node4936, node4937, node4938, node4944, node4947, node4948, node4950, node4955, node4956, node4963, node4967, node4970, node4984, node4994, node4997, node5004, node5009, node5010, node5011], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 570 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 714 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 736 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 90)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 81)
  exact nil_derived _ _

def compactBlock016Program : List Instruction := [
  ⟨56, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-4056/125),1,(0,0,-1,2,0,0,0))]⟩,
  ⟨13, 5, [((-100),0,(-2,0,0,-2,0,0,0))]⟩,
  ⟨17, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/500),1,(2,0,0,2,0,0,0))]⟩,
  ⟨110, 61, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 62, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨0, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨23, 10, [((104/225),0,(-3,2,-1,2,0,0,0))]⟩,
  ⟨39, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨97, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨105, 2, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨90, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨29, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-3375/208),1,(3,-2,1,-2,0,0,0))]⟩,
  ⟨39, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨9, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨78, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨16, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨37, 21, [((200/117),0,(-3,2,1,-2,0,0,0))]⟩,
  ⟨40, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨84, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨43, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-4563/2000),1,(3,-2,-1,2,0,0,0))]⟩,
  ⟨107, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨122, 35, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨126, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨35, 30, [((-225),0,(0,-2,0,-2,0,0,0))]⟩,
  ⟨37, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/3375),1,(0,2,0,2,0,0,0))]⟩,
  ⟨80, 32, [((-13/9),0,(0,2,-1,0,0,0,0))]⟩,
  ⟨70, 0, [(1,0,(0,0,0,0,0,0,0)),
  (18,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨84, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 2, [(1,0,(0,0,0,0,0,0,0)),
  (18,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨75, 3, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨130, 4, [(1,0,(0,0,0,0,0,0,0)),
  (8,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨133, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨94, 6, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨110, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨104, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨116, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨130, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((9/13),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨132, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨21, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨125, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-100),1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨143, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨105, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-72),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨29, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-600/13),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨125, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨119, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((450/13),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨123, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨82, 20, [(1,0,(0,0,0,0,0,0,0)),
  (6,1,(-1,-1,0,0,1,0,0))]⟩,
  ⟨137, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((225/13),1,(0,-2,1,-2,0,0,0)),
  ((9/13),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨56, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-416),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨86, 23, [(1,0,(0,0,0,0,0,0,0)),
  (43875,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨97, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-500/3),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨99, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-27/10),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨61, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((54/13),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨102, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-11232/5),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨92, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((5408/15),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨65, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-19500),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨106, 30, [(1,0,(0,0,0,0,0,0,0)),
  (1404,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨108, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((2808/5),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨110, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-702),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨112, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((1248/5),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨123, 34, [(1,0,(0,0,0,0,0,0,0)),
  (1404,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨145, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-3000/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨141, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((1500/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨135, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨137, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨163, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-2808),1,(-1,-2,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨124, 73, [((-13/4),0,(2,0,-1,0,0,0,0))]⟩,
  ⟨109, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((1/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨137, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨162, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨176, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨36, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨36, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨36, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨36, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨163, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((225/26),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨184, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨182, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨185, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨164, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/2),1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨145, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨114, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨150, 15, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨142, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((36/13),1,(-2,-2,1,0,0,0,0)),
  ((4/13),1,(-2,0,1,0,0,0,0))]⟩,
  ⟨173, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((225/26),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨39, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((3/2),1,(1,-1,0,0,1,0,0))]⟩,
  ⟨38, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((225/26),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨119, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-43875),1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨104, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨106, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((16/13),1,(-2,0,1,0,0,0,0))]⟩,
  ⟨129, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-351),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨131, 24, [(1,0,(0,0,0,0,0,0,0)),
  (1625,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨183, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((16/15),1,(-2,0,1,0,0,0,0))]⟩,
  ⟨164, 26, [(1,0,(0,0,0,0,0,0,0)),
  (9750,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨113, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((94500/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨138, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((39/4),1,(1,0,0,0,0,0,0))]⟩,
  ⟨137, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(0,0,0,0,0,0,0))]⟩,
  ⟨35, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-6750/13),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨34, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-702),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨196, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨35, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(0,0,0,0,0,0,0))]⟩,
  ⟨35, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0)),
  ((-702),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨23, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨109, 130, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨31, 132, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 133, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨111, 134, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨76, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨31, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨68, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨190, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 142, [(1,0,(0,0,0,0,0,0,0)),
  ((-8112/125),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨186, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨4, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨69, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨191, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((8112/125),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨48, 145, [(1,0,(0,0,0,0,0,0,0)),
  ((9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨173, 146, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 147, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨44, 148, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨154, 149, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨37, 150, [(1,0,(0,0,0,0,0,0,0)),
  ((36/13),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨218, 151, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨100, 152, [(1,0,(0,0,0,0,0,0,0)),
  ((-36),1,(-2,-2,0,0,0,0,0))]⟩
]























































































































































































def compactBlock016Indices : List ℕ := [126, 124, 119, 118, 117, 116, 115, 114, 112, 110, 108, 106, 105, 104, 103, 102, 99, 97, 96, 95, 94, 92, 91, 90, 85, 84, 82, 81, 80, 77, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 63, 61, 55, 54, 53, 52, 48, 46, 44, 43, 42, 41, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 20, 19, 18, 17, 16, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock016Results : List Poly :=
  program_results% (compactBlock016Inputs) (compactBlock016Program) (compactBlock016Indices)

def node5013 : Poly := rowAt compactBlock016Results 0
def node5018 : Poly := rowAt compactBlock016Results 1
def node5025 : Poly := rowAt compactBlock016Results 2
def node5026 : Poly := rowAt compactBlock016Results 3
def node5027 : Poly := rowAt compactBlock016Results 4
def node5028 : Poly := rowAt compactBlock016Results 5
def node5029 : Poly := rowAt compactBlock016Results 6
def node5030 : Poly := rowAt compactBlock016Results 7
def node5032 : Poly := rowAt compactBlock016Results 8
def node5034 : Poly := rowAt compactBlock016Results 9
def node5036 : Poly := rowAt compactBlock016Results 10
def node5038 : Poly := rowAt compactBlock016Results 11
def node5039 : Poly := rowAt compactBlock016Results 12
def node5041 : Poly := rowAt compactBlock016Results 13
def node5042 : Poly := rowAt compactBlock016Results 14
def node5043 : Poly := rowAt compactBlock016Results 15
def node5056 : Poly := rowAt compactBlock016Results 16
def node5063 : Poly := rowAt compactBlock016Results 17
def node5064 : Poly := rowAt compactBlock016Results 18
def node5065 : Poly := rowAt compactBlock016Results 19
def node5069 : Poly := rowAt compactBlock016Results 20
def node5071 : Poly := rowAt compactBlock016Results 21
def node5072 : Poly := rowAt compactBlock016Results 22
def node5073 : Poly := rowAt compactBlock016Results 23
def node5078 : Poly := rowAt compactBlock016Results 24
def node5081 : Poly := rowAt compactBlock016Results 25
def node5084 : Poly := rowAt compactBlock016Results 26
def node5085 : Poly := rowAt compactBlock016Results 27
def node5087 : Poly := rowAt compactBlock016Results 28
def node5090 : Poly := rowAt compactBlock016Results 29
def node5094 : Poly := rowAt compactBlock016Results 30
def node5096 : Poly := rowAt compactBlock016Results 31
def node5097 : Poly := rowAt compactBlock016Results 32
def node5098 : Poly := rowAt compactBlock016Results 33
def node5100 : Poly := rowAt compactBlock016Results 34
def node5101 : Poly := rowAt compactBlock016Results 35
def node5106 : Poly := rowAt compactBlock016Results 36
def node5107 : Poly := rowAt compactBlock016Results 37
def node5108 : Poly := rowAt compactBlock016Results 38
def node5109 : Poly := rowAt compactBlock016Results 39
def node5112 : Poly := rowAt compactBlock016Results 40
def node5115 : Poly := rowAt compactBlock016Results 41
def node5117 : Poly := rowAt compactBlock016Results 42
def node5126 : Poly := rowAt compactBlock016Results 43
def node5127 : Poly := rowAt compactBlock016Results 44
def node5128 : Poly := rowAt compactBlock016Results 45
def node5129 : Poly := rowAt compactBlock016Results 46
def node5133 : Poly := rowAt compactBlock016Results 47
def node5135 : Poly := rowAt compactBlock016Results 48
def node5139 : Poly := rowAt compactBlock016Results 49
def node5140 : Poly := rowAt compactBlock016Results 50
def node5143 : Poly := rowAt compactBlock016Results 51
def node5146 : Poly := rowAt compactBlock016Results 52
def node5150 : Poly := rowAt compactBlock016Results 53
def node5151 : Poly := rowAt compactBlock016Results 54
def node5154 : Poly := rowAt compactBlock016Results 55
def node5155 : Poly := rowAt compactBlock016Results 56
def node5156 : Poly := rowAt compactBlock016Results 57
def node5159 : Poly := rowAt compactBlock016Results 58
def node5160 : Poly := rowAt compactBlock016Results 59
def node5162 : Poly := rowAt compactBlock016Results 60
def node5164 : Poly := rowAt compactBlock016Results 61
def node5166 : Poly := rowAt compactBlock016Results 62
def node5168 : Poly := rowAt compactBlock016Results 63
def node5169 : Poly := rowAt compactBlock016Results 64
def node5171 : Poly := rowAt compactBlock016Results 65
def node5172 : Poly := rowAt compactBlock016Results 66
def node5173 : Poly := rowAt compactBlock016Results 67
def node5174 : Poly := rowAt compactBlock016Results 68
def node5175 : Poly := rowAt compactBlock016Results 69
def node5176 : Poly := rowAt compactBlock016Results 70
def node5178 : Poly := rowAt compactBlock016Results 71
def node5180 : Poly := rowAt compactBlock016Results 72
def node5181 : Poly := rowAt compactBlock016Results 73
def node5182 : Poly := rowAt compactBlock016Results 74
def node5184 : Poly := rowAt compactBlock016Results 75
def node5186 : Poly := rowAt compactBlock016Results 76
def node5187 : Poly := rowAt compactBlock016Results 77
def node5188 : Poly := rowAt compactBlock016Results 78
def node5189 : Poly := rowAt compactBlock016Results 79
def node5190 : Poly := rowAt compactBlock016Results 80
def node5191 : Poly := rowAt compactBlock016Results 81
def node5193 : Poly := rowAt compactBlock016Results 82
def node5194 : Poly := rowAt compactBlock016Results 83
def node5195 : Poly := rowAt compactBlock016Results 84
def node5197 : Poly := rowAt compactBlock016Results 85
def node5198 : Poly := rowAt compactBlock016Results 86
def node5202 : Poly := rowAt compactBlock016Results 87
def node5205 : Poly := rowAt compactBlock016Results 88
def node5206 : Poly := rowAt compactBlock016Results 89
def node5207 : Poly := rowAt compactBlock016Results 90

theorem compactBlock016_certificate : outputs compactBlock016Inputs compactBlock016Program compactBlock016Indices = compactBlock016Results := by
  decide +kernel

theorem compactBlock016_derived : ∀ p ∈ compactBlock016Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock016_inputs compactBlock016Program compactBlock016Indices compactBlock016_certificate

#print axioms compactBlock016_derived


def compactBlock017Inputs : List Poly := [node0715, node1191, node2997, node3002, node3191, node3198, node3205, node3711, node3727, node4163, node4166, node4181, node4182, node4254, node4353, node4354, node4368, node4375, node4376, node4389, node4400, node4402, node4443, node4453, node4454, node4541, node4568, node4578, node4586, node4587, node4677, node4685, node4702, node4713, node4722, node4737, node4740, node4747, node4748, node4749, node4750, node4798, node4850, node4867, node4874, node4892, node4893, node4912, node4921, node4928, node4931, node4935, node4945, node4971, node4983, node4989, node5026, node5028, node5032, node5038, node5039, node5042, node5043, node5063, node5064, node5065, node5071, node5073, node5078, node5081, node5084, node5109, node5115, node5117, node5127, node5129, node5135, node5139, node5143, node5146, node5150, node5169, node5173, node5174, node5175, node5176, node5180, node5181, node5187, node5191, node5197, node5198, node5206]

theorem compactBlock017_inputs : ∀ p ∈ compactBlock017Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0715, node1191, node2997, node3002, node3191, node3198, node3205, node3711, node3727, node4163, node4166, node4181, node4182, node4254, node4353, node4354, node4368, node4375, node4376, node4389, node4400, node4402, node4443, node4453, node4454, node4541, node4568, node4578, node4586, node4587, node4677, node4685, node4702, node4713, node4722, node4737, node4740, node4747, node4748, node4749, node4750, node4798, node4850, node4867, node4874, node4892, node4893, node4912, node4921, node4928, node4931, node4935, node4945, node4971, node4983, node4989, node5026, node5028, node5032, node5038, node5039, node5042, node5043, node5063, node5064, node5065, node5071, node5073, node5078, node5081, node5084, node5109, node5115, node5117, node5127, node5129, node5135, node5139, node5143, node5146, node5150, node5169, node5173, node5174, node5175, node5176, node5180, node5181, node5187, node5191, node5197, node5198, node5206], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 715 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 92)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 93)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 89)
  exact nil_derived _ _

def compactBlock017Program : List Instruction := [
  ⟨45, 11, [(1,0,(0,0,0,0,0,0,0)),
  (43875,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨27, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨48, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((52/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨84, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((351/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨87, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨90, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨70, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨34, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨100, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨59, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨67, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-36),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨90, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨92, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨64, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-5616/5),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨20, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((432/13),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨22, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((1625/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨50, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨13, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨13, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨56, 21, [((-13/18),0,(1,2,-1,0,0,0,0))]⟩,
  ⟨56, 0, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨15, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨15, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨78, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨100, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-36),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨18, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨18, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨97, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨117, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨100, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-200),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨21, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((25/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨91, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-600/13),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨22, 13, [(1,0,(0,0,0,0,0,0,0)),
  (36,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨22, 14, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨22, 15, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨125, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-90/13),1,(-1,-2,1,-1,0,1,0))]⟩,
  ⟨23, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((5616/5),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨43, 18, [(1,0,(0,0,0,0,0,0,0)),
  (1404,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨62, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((13/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨25, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-432/13),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨79, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-416/3),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨81, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((52000/3),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨27, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-1625/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨84, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-4000/3),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨86, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-351),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨29, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((351/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨103, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((750/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨121, 28, [(1,0,(0,0,0,0,0,0,0)),
  (2808,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨132, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨32, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨136, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨119, 54, [((-117/50),0,(1,-2,-1,2,0,0,0))]⟩,
  ⟨84, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((50/117),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨131, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨22, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-8),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨78, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-8/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨72, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨130, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((8/3),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨150, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/39),1,(-1,1,1,-2,1,0,0))]⟩,
  ⟨115, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨84, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨95, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-416/45),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨43, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨42, 40, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨132, 41, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨119, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨103, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨117, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨138, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-450/13),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨45, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-36),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨44, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨43, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((-36),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨136, 49, [(1,0,(0,0,0,0,0,0,0)),
  (24,1,(-3,-1,0,0,1,0,0))]⟩,
  ⟨108, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨139, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-8),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨101, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨93, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-72),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨160, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨173, 55, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨142, 56, [(1,0,(0,0,0,0,0,0,0)),
  ((1800/13),1,(-3,-2,1,-2,0,0,0))]⟩,
  ⟨126, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((13/30),1,(0,0,0,0,0,0,0))]⟩,
  ⟨86, 58, [(1,0,(0,0,0,0,0,0,0)),
  (416,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨109, 59, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨114, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨102, 61, [(1,0,(0,0,0,0,0,0,0)),
  ((-22750),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨91, 62, [(1,0,(0,0,0,0,0,0,0)),
  (52000,1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨130, 63, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404/5),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨134, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-52000/3),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨120, 65, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨163, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((1404/5),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨166, 67, [(1,0,(0,0,0,0,0,0,0)),
  ((27000/13),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨43, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨42, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨76, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨106, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-104/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨29, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((26/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨173, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((26/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨116, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((234/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨28, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((26/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨47, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((117/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨27, 34, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨23, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-78/25),1,(-1,-1,-1,2,1,0,0))]⟩,
  ⟨163, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((936/25),1,(-3,-2,-1,2,0,0,0))]⟩,
  ⟨132, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-10/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨160, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((-4563/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨151, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-4563/50),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨120, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-16224/125),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨59, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((4563/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨15, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((36504/25),1,(-1,-2,-1,2,0,0,0))]⟩,
  ⟨176, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨13, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/26),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨13, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨12, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨194, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-225),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨137, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨40, 16, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨179, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((900/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨128, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨130, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-54000/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨171, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨141, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-87750),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨143, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-3375/13),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨14, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨14, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(0,-2,0,0,0,0,0))]⟩
]











































































































































































def compactBlock017Indices : List ℕ := [127, 126, 125, 124, 105, 103, 98, 96, 95, 94, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 73, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 57, 56, 55, 53, 52, 50, 48, 47, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 30, 29, 28, 23, 22, 21, 20, 19, 18, 17, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock017Results : List Poly :=
  program_results% (compactBlock017Inputs) (compactBlock017Program) (compactBlock017Indices)

def node5208 : Poly := rowAt compactBlock017Results 0
def node5211 : Poly := rowAt compactBlock017Results 1
def node5212 : Poly := rowAt compactBlock017Results 2
def node5213 : Poly := rowAt compactBlock017Results 3
def node5239 : Poly := rowAt compactBlock017Results 4
def node5243 : Poly := rowAt compactBlock017Results 5
def node5250 : Poly := rowAt compactBlock017Results 6
def node5254 : Poly := rowAt compactBlock017Results 7
def node5255 : Poly := rowAt compactBlock017Results 8
def node5256 : Poly := rowAt compactBlock017Results 9
def node5258 : Poly := rowAt compactBlock017Results 10
def node5261 : Poly := rowAt compactBlock017Results 11
def node5266 : Poly := rowAt compactBlock017Results 12
def node5269 : Poly := rowAt compactBlock017Results 13
def node5271 : Poly := rowAt compactBlock017Results 14
def node5272 : Poly := rowAt compactBlock017Results 15
def node5273 : Poly := rowAt compactBlock017Results 16
def node5274 : Poly := rowAt compactBlock017Results 17
def node5275 : Poly := rowAt compactBlock017Results 18
def node5278 : Poly := rowAt compactBlock017Results 19
def node5283 : Poly := rowAt compactBlock017Results 20
def node5284 : Poly := rowAt compactBlock017Results 21
def node5285 : Poly := rowAt compactBlock017Results 22
def node5287 : Poly := rowAt compactBlock017Results 23
def node5289 : Poly := rowAt compactBlock017Results 24
def node5295 : Poly := rowAt compactBlock017Results 25
def node5300 : Poly := rowAt compactBlock017Results 26
def node5304 : Poly := rowAt compactBlock017Results 27
def node5305 : Poly := rowAt compactBlock017Results 28
def node5306 : Poly := rowAt compactBlock017Results 29
def node5307 : Poly := rowAt compactBlock017Results 30
def node5308 : Poly := rowAt compactBlock017Results 31
def node5309 : Poly := rowAt compactBlock017Results 32
def node5310 : Poly := rowAt compactBlock017Results 33
def node5311 : Poly := rowAt compactBlock017Results 34
def node5313 : Poly := rowAt compactBlock017Results 35
def node5314 : Poly := rowAt compactBlock017Results 36
def node5315 : Poly := rowAt compactBlock017Results 37
def node5319 : Poly := rowAt compactBlock017Results 38
def node5320 : Poly := rowAt compactBlock017Results 39
def node5321 : Poly := rowAt compactBlock017Results 40
def node5325 : Poly := rowAt compactBlock017Results 41
def node5335 : Poly := rowAt compactBlock017Results 42
def node5337 : Poly := rowAt compactBlock017Results 43
def node5339 : Poly := rowAt compactBlock017Results 44
def node5341 : Poly := rowAt compactBlock017Results 45
def node5343 : Poly := rowAt compactBlock017Results 46
def node5344 : Poly := rowAt compactBlock017Results 47
def node5346 : Poly := rowAt compactBlock017Results 48
def node5347 : Poly := rowAt compactBlock017Results 49
def node5348 : Poly := rowAt compactBlock017Results 50
def node5349 : Poly := rowAt compactBlock017Results 51
def node5351 : Poly := rowAt compactBlock017Results 52
def node5352 : Poly := rowAt compactBlock017Results 53
def node5353 : Poly := rowAt compactBlock017Results 54
def node5354 : Poly := rowAt compactBlock017Results 55
def node5355 : Poly := rowAt compactBlock017Results 56
def node5357 : Poly := rowAt compactBlock017Results 57
def node5358 : Poly := rowAt compactBlock017Results 58
def node5359 : Poly := rowAt compactBlock017Results 59
def node5362 : Poly := rowAt compactBlock017Results 60
def node5364 : Poly := rowAt compactBlock017Results 61
def node5366 : Poly := rowAt compactBlock017Results 62
def node5378 : Poly := rowAt compactBlock017Results 63
def node5383 : Poly := rowAt compactBlock017Results 64
def node5384 : Poly := rowAt compactBlock017Results 65
def node5385 : Poly := rowAt compactBlock017Results 66
def node5386 : Poly := rowAt compactBlock017Results 67
def node5389 : Poly := rowAt compactBlock017Results 68
def node5390 : Poly := rowAt compactBlock017Results 69
def node5397 : Poly := rowAt compactBlock017Results 70
def node5400 : Poly := rowAt compactBlock017Results 71
def node5401 : Poly := rowAt compactBlock017Results 72
def node5402 : Poly := rowAt compactBlock017Results 73
def node5405 : Poly := rowAt compactBlock017Results 74
def node5408 : Poly := rowAt compactBlock017Results 75
def node5409 : Poly := rowAt compactBlock017Results 76
def node5410 : Poly := rowAt compactBlock017Results 77
def node5411 : Poly := rowAt compactBlock017Results 78
def node5412 : Poly := rowAt compactBlock017Results 79
def node5413 : Poly := rowAt compactBlock017Results 80
def node5416 : Poly := rowAt compactBlock017Results 81
def node5418 : Poly := rowAt compactBlock017Results 82
def node5419 : Poly := rowAt compactBlock017Results 83
def node5420 : Poly := rowAt compactBlock017Results 84

theorem compactBlock017_certificate : outputs compactBlock017Inputs compactBlock017Program compactBlock017Indices = compactBlock017Results := by
  decide +kernel

theorem compactBlock017_derived : ∀ p ∈ compactBlock017Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock017_inputs compactBlock017Program compactBlock017Indices compactBlock017_certificate

#print axioms compactBlock017_derived


def compactBlock018Inputs : List Poly := [node1191, node3259, node3705, node3713, node3748, node3796, node3999, node4086, node4428, node4435, node4436, node4483, node4484, node4485, node4519, node4528, node4632, node4638, node4647, node4658, node4662, node4698, node4720, node4730, node4731, node4822, node4949, node4952, node4959, node4961, node4962, node4968, node4999, node5013, node5027, node5030, node5034, node5036, node5056, node5069, node5072, node5085, node5126, node5128, node5151, node5184, node5189, node5190, node5194, node5195, node5202, node5205, node5207, node5208, node5211, node5212, node5213, node5239, node5243, node5254, node5255, node5256, node5258, node5261, node5266, node5269, node5271, node5272, node5273, node5274, node5275, node5278, node5283, node5284, node5285, node5287, node5289, node5295, node5304, node5307, node5309, node5313, node5314, node5315, node5321, node5325, node5335, node5337, node5341, node5343, node5358, node5362, node5364, node5366, node5378, node5383, node5384, node5385, node5386, node5389, node5390, node5397, node5400, node5401, node5402, node5410, node5418, node5420]

theorem compactBlock018_inputs : ∀ p ∈ compactBlock018Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node1191, node3259, node3705, node3713, node3748, node3796, node3999, node4086, node4428, node4435, node4436, node4483, node4484, node4485, node4519, node4528, node4632, node4638, node4647, node4658, node4662, node4698, node4720, node4730, node4731, node4822, node4949, node4952, node4959, node4961, node4962, node4968, node4999, node5013, node5027, node5030, node5034, node5036, node5056, node5069, node5072, node5085, node5126, node5128, node5151, node5184, node5189, node5190, node5194, node5195, node5202, node5205, node5207, node5208, node5211, node5212, node5213, node5239, node5243, node5254, node5255, node5256, node5258, node5261, node5266, node5269, node5271, node5272, node5273, node5274, node5275, node5278, node5283, node5284, node5285, node5287, node5289, node5295, node5304, node5307, node5309, node5313, node5314, node5315, node5321, node5325, node5335, node5337, node5341, node5343, node5358, node5362, node5364, node5366, node5378, node5383, node5384, node5385, node5386, node5389, node5390, node5397, node5400, node5401, node5402, node5410, node5418, node5420], Derived sourceRows 1191 p
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 90)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 84)
  exact nil_derived _ _

def compactBlock018Program : List Instruction := [
  ⟨59, 0, [((-1/200),0,(3,0,0,2,0,0,0))]⟩,
  ⟨15, 0, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨83, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨51, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨61, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨87, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨99, 6, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨110, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨67, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨94, 9, [(1,0,(0,0,0,0,0,0,0)),
  (36,1,(-1,-2,0,0,0,0,0)),
  ((18/13),1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨71, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨62, 11, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨74, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((600/13),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨92, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-36),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨77, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨79, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨68, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-36/13),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨113, 17, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨71, 18, [(1,0,(0,0,0,0,0,0,0)),
  (36,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨109, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-600/13),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨57, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨86, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((450/13),1,(-1,-2,1,-2,0,0,0)),
  ((90/13),1,(-1,-2,1,-1,0,1,0)),
  ((18/13),1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨76, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-43875),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨89, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-5616/5),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨91, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1404),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨93, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨60, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((2496/5),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨39, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((54/13),1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨83, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((432/13),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨100, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((416/3),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨102, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-52000/3),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨45, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨105, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((1625/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨67, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨108, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((4000/3),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨92, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-1140750),1,(-1,-2,0,-2,0,0,0))]⟩,
  ⟨54, 38, [(1,0,(0,0,0,0,0,0,0)),
  (351,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨113, 39, [(1,0,(0,0,0,0,0,0,0)),
  (351,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨97, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨116, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨62, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((104/3),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨150, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-750/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨120, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-750/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨122, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-2808),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨67, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-2808),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨138, 47, [(1,0,(0,0,0,0,0,0,0)),
  (1404,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨75, 49, [((25/72),0,(3,2,0,-2,0,0,0))]⟩,
  ⟨84, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-72/25),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨56, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((11232/125),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨79, 52, [((1/2),0,(1,0,0,0,0,0,0))]⟩,
  ⟨140, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-72/25),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨62, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((65/6),1,(0,0,0,0,0,0,0))]⟩,
  ⟨140, 156, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 75, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨38, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨164, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨62, 59, [(1,0,(0,0,0,0,0,0,0)),
  (19500,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨165, 59, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨150, 155, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨113, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 144, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 97, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨149, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨95, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 67, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 69, [(1,0,(0,0,0,0,0,0,0)),
  (156000,1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨157, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨120, 71, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨69, 77, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨108, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((25/26),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨100, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨173, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/26),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨72, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((25/26),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨11, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨19, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-36),1,(-2,-2,0,0,0,0,0)),
  (4,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨69, 7, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨180, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((75/26),1,(1,-1,1,-2,1,0,0))]⟩,
  ⟨70, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨176, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-75/26),1,(1,-1,1,-2,1,0,0))]⟩,
  ⟨70, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-3),1,(0,-1,0,0,1,0,0))]⟩,
  ⟨24, 12, [(1,0,(0,0,0,0,0,0,0)),
  (36,1,(-2,-2,0,0,0,0,0)),
  ((-4),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨100, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((26/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨189, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-125/39),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨116, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/5),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨192, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨133, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨106, 18, [(1,0,(0,0,0,0,0,0,0)),
  (5616,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨196, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨198, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-624/5),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨123, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-624/5),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨207, 22, [(1,0,(0,0,0,0,0,0,0)),
  (1404,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨17, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 144, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 142, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨209, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨146, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨151, 146, [(1,0,(0,0,0,0,0,0,0)),
  ((-8/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨3, 147, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨96, 148, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨55, 149, [(1,0,(0,0,0,0,0,0,0)),
  ((-8),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨141, 150, [(1,0,(0,0,0,0,0,0,0)),
  ((-8/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨91, 151, [(1,0,(0,0,0,0,0,0,0)),
  ((8/3),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨52, 152, [(1,0,(0,0,0,0,0,0,0)),
  ((200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨115, 153, [(1,0,(0,0,0,0,0,0,0)),
  ((-6500/27),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨142, 154, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨122, 155, [(1,0,(0,0,0,0,0,0,0)),
  ((12000/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨5, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨163, 160, [(1,0,(0,0,0,0,0,0,0)),
  ((-8/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨16, 161, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨11, 162, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨107, 163, [(1,0,(0,0,0,0,0,0,0)),
  ((-8/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨62, 164, [(1,0,(0,0,0,0,0,0,0)),
  ((200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨107, 165, [(1,0,(0,0,0,0,0,0,0)),
  ((8/3),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨202, 166, [(1,0,(0,0,0,0,0,0,0)),
  ((-8/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨73, 167, [(1,0,(0,0,0,0,0,0,0)),
  ((-8),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨128, 168, [(1,0,(0,0,0,0,0,0,0)),
  ((416/27),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨132, 169, [(1,0,(0,0,0,0,0,0,0)),
  ((-12000/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨3, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]







































































































































































def compactBlock018Indices : List ℕ := [122, 121, 110, 106, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 76, 73, 71, 70, 66, 60, 59, 58, 57, 54, 53, 51, 49, 48, 47, 46, 45, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 23, 22, 19, 18, 16, 15, 14, 13, 12, 11, 9, 8, 7, 6, 5, 3, 2, 1, 0]
def compactBlock018Results : List Poly :=
  program_results% (compactBlock018Inputs) (compactBlock018Program) (compactBlock018Indices)

def node5427 : Poly := rowAt compactBlock018Results 0
def node5428 : Poly := rowAt compactBlock018Results 1
def node5453 : Poly := rowAt compactBlock018Results 2
def node5460 : Poly := rowAt compactBlock018Results 3
def node5462 : Poly := rowAt compactBlock018Results 4
def node5465 : Poly := rowAt compactBlock018Results 5
def node5469 : Poly := rowAt compactBlock018Results 6
def node5471 : Poly := rowAt compactBlock018Results 7
def node5473 : Poly := rowAt compactBlock018Results 8
def node5474 : Poly := rowAt compactBlock018Results 9
def node5475 : Poly := rowAt compactBlock018Results 10
def node5476 : Poly := rowAt compactBlock018Results 11
def node5477 : Poly := rowAt compactBlock018Results 12
def node5479 : Poly := rowAt compactBlock018Results 13
def node5480 : Poly := rowAt compactBlock018Results 14
def node5483 : Poly := rowAt compactBlock018Results 15
def node5485 : Poly := rowAt compactBlock018Results 16
def node5490 : Poly := rowAt compactBlock018Results 17
def node5491 : Poly := rowAt compactBlock018Results 18
def node5494 : Poly := rowAt compactBlock018Results 19
def node5496 : Poly := rowAt compactBlock018Results 20
def node5497 : Poly := rowAt compactBlock018Results 21
def node5498 : Poly := rowAt compactBlock018Results 22
def node5499 : Poly := rowAt compactBlock018Results 23
def node5500 : Poly := rowAt compactBlock018Results 24
def node5502 : Poly := rowAt compactBlock018Results 25
def node5503 : Poly := rowAt compactBlock018Results 26
def node5506 : Poly := rowAt compactBlock018Results 27
def node5507 : Poly := rowAt compactBlock018Results 28
def node5508 : Poly := rowAt compactBlock018Results 29
def node5513 : Poly := rowAt compactBlock018Results 30
def node5517 : Poly := rowAt compactBlock018Results 31
def node5522 : Poly := rowAt compactBlock018Results 32
def node5523 : Poly := rowAt compactBlock018Results 33
def node5533 : Poly := rowAt compactBlock018Results 34
def node5549 : Poly := rowAt compactBlock018Results 35
def node5550 : Poly := rowAt compactBlock018Results 36
def node5553 : Poly := rowAt compactBlock018Results 37
def node5555 : Poly := rowAt compactBlock018Results 38
def node5565 : Poly := rowAt compactBlock018Results 39
def node5567 : Poly := rowAt compactBlock018Results 40
def node5569 : Poly := rowAt compactBlock018Results 41
def node5573 : Poly := rowAt compactBlock018Results 42
def node5578 : Poly := rowAt compactBlock018Results 43
def node5579 : Poly := rowAt compactBlock018Results 44
def node5580 : Poly := rowAt compactBlock018Results 45
def node5581 : Poly := rowAt compactBlock018Results 46
def node5598 : Poly := rowAt compactBlock018Results 47
def node5599 : Poly := rowAt compactBlock018Results 48
def node5600 : Poly := rowAt compactBlock018Results 49
def node5604 : Poly := rowAt compactBlock018Results 50
def node5607 : Poly := rowAt compactBlock018Results 51
def node5608 : Poly := rowAt compactBlock018Results 52
def node5609 : Poly := rowAt compactBlock018Results 53
def node5610 : Poly := rowAt compactBlock018Results 54
def node5611 : Poly := rowAt compactBlock018Results 55
def node5612 : Poly := rowAt compactBlock018Results 56
def node5613 : Poly := rowAt compactBlock018Results 57
def node5616 : Poly := rowAt compactBlock018Results 58
def node5618 : Poly := rowAt compactBlock018Results 59
def node5619 : Poly := rowAt compactBlock018Results 60
def node5620 : Poly := rowAt compactBlock018Results 61
def node5621 : Poly := rowAt compactBlock018Results 62
def node5624 : Poly := rowAt compactBlock018Results 63
def node5636 : Poly := rowAt compactBlock018Results 64
def node5638 : Poly := rowAt compactBlock018Results 65
def node5641 : Poly := rowAt compactBlock018Results 66
def node5644 : Poly := rowAt compactBlock018Results 67
def node5647 : Poly := rowAt compactBlock018Results 68
def node5648 : Poly := rowAt compactBlock018Results 69
def node5649 : Poly := rowAt compactBlock018Results 70
def node5650 : Poly := rowAt compactBlock018Results 71
def node5651 : Poly := rowAt compactBlock018Results 72
def node5652 : Poly := rowAt compactBlock018Results 73
def node5654 : Poly := rowAt compactBlock018Results 74
def node5655 : Poly := rowAt compactBlock018Results 75
def node5658 : Poly := rowAt compactBlock018Results 76
def node5661 : Poly := rowAt compactBlock018Results 77
def node5662 : Poly := rowAt compactBlock018Results 78
def node5664 : Poly := rowAt compactBlock018Results 79
def node5665 : Poly := rowAt compactBlock018Results 80
def node5667 : Poly := rowAt compactBlock018Results 81
def node5670 : Poly := rowAt compactBlock018Results 82

theorem compactBlock018_certificate : outputs compactBlock018Inputs compactBlock018Program compactBlock018Indices = compactBlock018Results := by
  decide +kernel

theorem compactBlock018_derived : ∀ p ∈ compactBlock018Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock018_inputs compactBlock018Program compactBlock018Indices compactBlock018_certificate

#print axioms compactBlock018_derived


def compactBlock019Inputs : List Poly := [node1191, node3433, node3498, node3535, node3570, node3706, node3712, node3722, node4423, node4549, node4707, node4708, node4771, node4881, node4932, node4969, node4972, node4987, node4988, node5018, node5025, node5087, node5090, node5133, node5140, node5154, node5155, node5156, node5159, node5160, node5162, node5178, node5182, node5186, node5300, node5305, node5306, node5308, node5310, node5311, node5319, node5320, node5339, node5405, node5408, node5409, node5411, node5412, node5413, node5416, node5453, node5460, node5502, node5503, node5522, node5549, node5550, node5553, node5555, node5567, node5569, node5573, node5578, node5579, node5580, node5581, node5598, node5599, node5600, node5604, node5607, node5608, node5636, node5638, node5641, node5644, node5647, node5648, node5649, node5652, node5654, node5658, node5661, node5662, node5664, node5665, node5670]

theorem compactBlock019_inputs : ∀ p ∈ compactBlock019Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node1191, node3433, node3498, node3535, node3570, node3706, node3712, node3722, node4423, node4549, node4707, node4708, node4771, node4881, node4932, node4969, node4972, node4987, node4988, node5018, node5025, node5087, node5090, node5133, node5140, node5154, node5155, node5156, node5159, node5160, node5162, node5178, node5182, node5186, node5300, node5305, node5306, node5308, node5310, node5311, node5319, node5320, node5339, node5405, node5408, node5409, node5411, node5412, node5413, node5416, node5453, node5460, node5502, node5503, node5522, node5549, node5550, node5553, node5555, node5567, node5569, node5573, node5578, node5579, node5580, node5581, node5598, node5599, node5600, node5604, node5607, node5608, node5636, node5638, node5641, node5644, node5647, node5648, node5649, node5652, node5654, node5658, node5661, node5662, node5664, node5665, node5670], Derived sourceRows 1191 p
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock009_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 82)
  exact nil_derived _ _

def compactBlock019Program : List Instruction := [
  ⟨40, 0, [((-52/225),0,(-2,2,-1,2,0,0,0))]⟩,
  ⟨57, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((225/52),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨35, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((225/52),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨45, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨83, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨20, 4, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨7, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((3375/52),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨48, 7, [((-52/225),0,(-2,2,-1,2,0,0,0))]⟩,
  ⟨6, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((225/52),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨29, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 2, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨97, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨25, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨50, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((225/52),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨69, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((225/52),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨24, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨59, 16, [((-1/225),0,(0,2,0,2,0,0,0))]⟩,
  ⟨78, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨82, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((225/26),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨84, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/26),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨74, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨101, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨36, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨67, 6, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨69, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-3),1,(0,-1,0,0,1,0,0))]⟩,
  ⟨98, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((900/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨98, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-900/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨48, 10, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨50, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨46, 12, [(1,0,(0,0,0,0,0,0,0)),
  (87750,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨35, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1625/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨77, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨39, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((54000/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨80, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((54000/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨82, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((26/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((26/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨86, 20, [(1,0,(0,0,0,0,0,0,0)),
  (87750,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨40, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-500/13),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨91, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((3375/13),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨93, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((3375/13),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨23, 41, [((-117/50),0,(1,-2,-1,2,0,0,0))]⟩,
  ⟨20, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨127, 2, [(1,0,(0,0,0,0,0,0,0)),
  (8,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨34, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((8/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨43, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/39),1,(-1,1,1,-2,1,0,0))]⟩,
  ⟨83, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨36, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-8/3),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨44, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((8/3),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨36, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((50/39),1,(-1,1,1,-2,1,0,0))]⟩,
  ⟨45, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-8/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨128, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-8),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨110, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨39, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((50/117),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨93, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((250/117),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨96, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((416/45),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨61, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((416/27),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨133, 59, [((4/25),0,(-2,0,0,2,0,0,0))]⟩,
  ⟨56, 0, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨9, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨68, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((1625/16),1,(3,0,0,-2,0,0,0))]⟩,
  ⟨2, 95, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨18, 145, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨52, 146, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨150, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 79, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨23, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨135, 69, [((-25/104),0,(3,0,1,-2,0,0,0))]⟩,
  ⟨51, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨147, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-104/75),1,(-3,1,-1,2,1,0,0))]⟩,
  ⟨20, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((104/225),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨78, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-5408/3375),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨4, 75, [((26/225),0,(-1,2,-1,2,0,0,0))]⟩,
  ⟨135, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨135, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨140, 2, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨142, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨60, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((225/26),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨60, 5, [(1,0,(0,0,0,0,0,0,0)),
  (18,1,(-1,-2,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨39, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0)),
  ((-9/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨60, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((25/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨74, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨167, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((400/13),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨62, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨18, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((16/3),1,(-4,1,0,0,1,0,0))]⟩,
  ⟨155, 12, [(1,0,(0,0,0,0,0,0,0)),
  (18,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨157, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨25, 14, [(1,0,(0,0,0,0,0,0,0)),
  (16,1,(-4,0,0,0,0,0,0))]⟩,
  ⟨18, 15, [(1,0,(0,0,0,0,0,0,0)),
  (16,1,(-4,0,0,0,0,0,0))]⟩,
  ⟨67, 16, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨29, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((16/3),1,(-4,1,0,0,1,0,0))]⟩,
  ⟨46, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨69, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-900/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨69, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((900/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨166, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0)),
  ((-6),1,(-1,-1,0,0,1,0,0))]⟩,
  ⟨32, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-16/3),1,(-4,1,0,0,1,0,0))]⟩,
  ⟨71, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-3),1,(0,-1,0,0,1,0,0))]⟩,
  ⟨33, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-16),1,(-4,0,0,0,0,0,0)),
  ((-36),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨151, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-72/13),1,(-3,-2,1,0,0,0,0)),
  ((-24/13),1,(-3,-1,1,0,1,0,0)),
  ((-8/13),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨34, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-16),1,(-4,0,0,0,0,0,0)),
  (36,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨173, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨175, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨165, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-2,0,0,0,0,0)),
  ((-3),1,(0,-1,0,0,1,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨32, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-16/3),1,(-4,1,0,0,1,0,0))]⟩,
  ⟨78, 31, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨54, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((450/13),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨186, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-400/13),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨135, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨162, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((200/13),1,(-3,0,1,-2,0,0,0)),
  ((-40/13),1,(-3,0,1,-1,0,1,0)),
  ((8/13),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨57, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((450/13),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨139, 37, [(1,0,(0,0,0,0,0,0,0)),
  (87750,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨84, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((-87750),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨142, 39, [(1,0,(0,0,0,0,0,0,0)),
  (351,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨194, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((13000/27),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨86, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((1625/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨128, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((3375/2),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨87, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((351/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨57, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((1625/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨206, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((832/27),1,(-4,2,0,0,0,0,0))]⟩,
  ⟨130, 46, [(1,0,(0,0,0,0,0,0,0)),
  (13,1,(0,0,0,0,0,0,0))]⟩,
  ⟨151, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-32/13),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨135, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨154, 49, [(1,0,(0,0,0,0,0,0,0)),
  (702,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨93, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-54000/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨157, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-3250),1,(-1,0,0,-2,0,0,0))]⟩
]























































































































































def compactBlock019Indices : List ℕ := [121, 119, 112, 94, 93, 92, 91, 90, 89, 88, 87, 84, 81, 79, 78, 77, 72, 71, 70, 69, 56, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock019Results : List Poly :=
  program_results% (compactBlock019Inputs) (compactBlock019Program) (compactBlock019Indices)

def node5679 : Poly := rowAt compactBlock019Results 0
def node5682 : Poly := rowAt compactBlock019Results 1
def node5691 : Poly := rowAt compactBlock019Results 2
def node5725 : Poly := rowAt compactBlock019Results 3
def node5726 : Poly := rowAt compactBlock019Results 4
def node5728 : Poly := rowAt compactBlock019Results 5
def node5729 : Poly := rowAt compactBlock019Results 6
def node5731 : Poly := rowAt compactBlock019Results 7
def node5732 : Poly := rowAt compactBlock019Results 8
def node5734 : Poly := rowAt compactBlock019Results 9
def node5735 : Poly := rowAt compactBlock019Results 10
def node5742 : Poly := rowAt compactBlock019Results 11
def node5752 : Poly := rowAt compactBlock019Results 12
def node5754 : Poly := rowAt compactBlock019Results 13
def node5755 : Poly := rowAt compactBlock019Results 14
def node5757 : Poly := rowAt compactBlock019Results 15
def node5763 : Poly := rowAt compactBlock019Results 16
def node5764 : Poly := rowAt compactBlock019Results 17
def node5765 : Poly := rowAt compactBlock019Results 18
def node5766 : Poly := rowAt compactBlock019Results 19
def node5790 : Poly := rowAt compactBlock019Results 20
def node5795 : Poly := rowAt compactBlock019Results 21
def node5796 : Poly := rowAt compactBlock019Results 22
def node5797 : Poly := rowAt compactBlock019Results 23
def node5798 : Poly := rowAt compactBlock019Results 24
def node5799 : Poly := rowAt compactBlock019Results 25
def node5800 : Poly := rowAt compactBlock019Results 26
def node5801 : Poly := rowAt compactBlock019Results 27
def node5804 : Poly := rowAt compactBlock019Results 28
def node5805 : Poly := rowAt compactBlock019Results 29
def node5809 : Poly := rowAt compactBlock019Results 30
def node5814 : Poly := rowAt compactBlock019Results 31
def node5820 : Poly := rowAt compactBlock019Results 32
def node5822 : Poly := rowAt compactBlock019Results 33
def node5823 : Poly := rowAt compactBlock019Results 34
def node5825 : Poly := rowAt compactBlock019Results 35
def node5826 : Poly := rowAt compactBlock019Results 36
def node5827 : Poly := rowAt compactBlock019Results 37
def node5830 : Poly := rowAt compactBlock019Results 38
def node5831 : Poly := rowAt compactBlock019Results 39
def node5832 : Poly := rowAt compactBlock019Results 40
def node5833 : Poly := rowAt compactBlock019Results 41
def node5835 : Poly := rowAt compactBlock019Results 42
def node5836 : Poly := rowAt compactBlock019Results 43
def node5837 : Poly := rowAt compactBlock019Results 44
def node5839 : Poly := rowAt compactBlock019Results 45
def node5840 : Poly := rowAt compactBlock019Results 46
def node5842 : Poly := rowAt compactBlock019Results 47
def node5844 : Poly := rowAt compactBlock019Results 48
def node5846 : Poly := rowAt compactBlock019Results 49
def node5847 : Poly := rowAt compactBlock019Results 50
def node5848 : Poly := rowAt compactBlock019Results 51
def node5849 : Poly := rowAt compactBlock019Results 52
def node5850 : Poly := rowAt compactBlock019Results 53
def node5851 : Poly := rowAt compactBlock019Results 54
def node5852 : Poly := rowAt compactBlock019Results 55
def node5853 : Poly := rowAt compactBlock019Results 56
def node5857 : Poly := rowAt compactBlock019Results 57
def node5858 : Poly := rowAt compactBlock019Results 58
def node5859 : Poly := rowAt compactBlock019Results 59
def node5860 : Poly := rowAt compactBlock019Results 60
def node5862 : Poly := rowAt compactBlock019Results 61
def node5864 : Poly := rowAt compactBlock019Results 62
def node5865 : Poly := rowAt compactBlock019Results 63
def node5866 : Poly := rowAt compactBlock019Results 64
def node5868 : Poly := rowAt compactBlock019Results 65
def node5871 : Poly := rowAt compactBlock019Results 66
def node5872 : Poly := rowAt compactBlock019Results 67
def node5873 : Poly := rowAt compactBlock019Results 68
def node5874 : Poly := rowAt compactBlock019Results 69
def node5879 : Poly := rowAt compactBlock019Results 70
def node5880 : Poly := rowAt compactBlock019Results 71
def node5881 : Poly := rowAt compactBlock019Results 72
def node5882 : Poly := rowAt compactBlock019Results 73
def node5886 : Poly := rowAt compactBlock019Results 74

theorem compactBlock019_certificate : outputs compactBlock019Inputs compactBlock019Program compactBlock019Indices = compactBlock019Results := by
  decide +kernel

theorem compactBlock019_derived : ∀ p ∈ compactBlock019Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock019_inputs compactBlock019Program compactBlock019Indices compactBlock019_certificate

#print axioms compactBlock019_derived


}
end SmallLevelTwentySixGermDAG
end
