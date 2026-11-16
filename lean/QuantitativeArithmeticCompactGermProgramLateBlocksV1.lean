module
public import QuantitativeArithmeticCompactGermProgramMiddleBlocksV1
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

def compactBlock020Inputs : List Poly := [node1191, node3782, node3784, node3871, node3901, node3912, node3967, node4065, node4231, node4256, node4439, node4643, node4673, node4711, node4712, node4714, node4776, node4845, node4863, node4975, node5029, node5041, node5164, node5166, node5168, node5171, node5172, node5188, node5193, node5250, node5354, node5357, node5427, node5428, node5498, node5499, node5513, node5517, node5523, node5565, node5609, node5650, node5651, node5655, node5667, node5682, node5725, node5726, node5728, node5729, node5731, node5734, node5735, node5742, node5752, node5754, node5755, node5757, node5790, node5796, node5797, node5798, node5799, node5800, node5801, node5804, node5805, node5809, node5814, node5820, node5822, node5823, node5825, node5826, node5830, node5831, node5832, node5833, node5835, node5836, node5837, node5840, node5842, node5847, node5848, node5851, node5852, node5853, node5857, node5858, node5859]

theorem compactBlock020_inputs : ∀ p ∈ compactBlock020Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node1191, node3782, node3784, node3871, node3901, node3912, node3967, node4065, node4231, node4256, node4439, node4643, node4673, node4711, node4712, node4714, node4776, node4845, node4863, node4975, node5029, node5041, node5164, node5166, node5168, node5171, node5172, node5188, node5193, node5250, node5354, node5357, node5427, node5428, node5498, node5499, node5513, node5517, node5523, node5565, node5609, node5650, node5651, node5655, node5667, node5682, node5725, node5726, node5728, node5729, node5731, node5734, node5735, node5742, node5752, node5754, node5755, node5757, node5790, node5796, node5797, node5798, node5799, node5800, node5801, node5804, node5805, node5809, node5814, node5820, node5822, node5823, node5825, node5826, node5830, node5831, node5832, node5833, node5835, node5836, node5837, node5840, node5842, node5847, node5848, node5851, node5852, node5853, node5857, node5858, node5859], Derived sourceRows 1191 p
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock010_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 59)
  exact nil_derived _ _

def compactBlock020Program : List Instruction := [
  ⟨46, 59, [(1,0,(0,0,0,0,0,0,0)),
  ((-54000/13),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨14, 60, [(1,0,(0,0,0,0,0,0,0)),
  (702,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨24, 61, [(1,0,(0,0,0,0,0,0,0)),
  ((-32/15),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨50, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 63, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨53, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 65, [(1,0,(0,0,0,0,0,0,0)),
  ((13/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨21, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-43875/2),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨26, 67, [(1,0,(0,0,0,0,0,0,0)),
  ((13/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨59, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-87750),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨49, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-156000),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨34, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-19500),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨29, 71, [(1,0,(0,0,0,0,0,0,0)),
  (1404,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨37, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((-189000/13),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨30, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-11232/5),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨59, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-24000/13),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨58, 75, [(1,0,(0,0,0,0,0,0,0)),
  ((-24000/13),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨51, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨34, 78, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨45, 79, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨72, 80, [(1,0,(0,0,0,0,0,0,0)),
  ((-3375/13),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨74, 81, [(1,0,(0,0,0,0,0,0,0)),
  ((-3375/13),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨49, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((13500/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨55, 83, [(1,0,(0,0,0,0,0,0,0)),
  ((13500/13),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨90, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨64, 86, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨102, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨110, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 92, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨106, 94, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨113, 95, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨35, 96, [(1,0,(0,0,0,0,0,0,0)),
  (78000,1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨72, 97, [(1,0,(0,0,0,0,0,0,0)),
  ((-1625/216),1,(2,2,0,-2,0,0,0))]⟩,
  ⟨38, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((1625/54),1,(1,2,0,-2,0,0,0))]⟩,
  ⟨5, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨120, 101, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨75, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-312/5),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨98, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨109, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((104/225),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨113, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((104/225),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨4, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-104/75),1,(-3,1,-1,2,1,0,0))]⟩,
  ⟨84, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((104/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨133, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 110, [(1,0,(0,0,0,0,0,0,0)),
  ((15/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨79, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨93, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨103, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨106, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨134, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨142, 11, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨83, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-2028/125),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨81, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((8112/125),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨6, 55, [((-13/50),0,(1,0,-1,2,0,0,0))]⟩,
  ⟨99, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨68, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((39/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1500/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨126, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨90, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((200/117),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨24, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨116, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨21, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨152, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨87, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((39/10),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 67, [((-117/100),0,(2,-2,-1,2,0,0,0))]⟩,
  ⟨37, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨6, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨6, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨149, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((100/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨157, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨162, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((100/117),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨80, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((2000/351),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨144, 75, [((-13/200),0,(3,0,-1,2,0,0,0))]⟩,
  ⟨7, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨16, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 2, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨14, 3, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨156, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨15, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-200/13),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨8, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((200/117),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨86, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-4000/351),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨17, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/10),1,(0,0,0,0,0,0,0))]⟩,
  ⟨152, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨163, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨173, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨30, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨30, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((6500/27),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨31, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((1500/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨101, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((1500/13),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨7, 93, [((9/25),0,(0,-2,0,2,0,0,0))]⟩,
  ⟨46, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨18, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨169, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨103, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((1625/54),1,(1,2,0,-2,0,0,0))]⟩,
  ⟨4, 99, [((-25/26),0,(1,0,1,-2,0,0,0))]⟩,
  ⟨133, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨174, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨52, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨158, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨53, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((52/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨162, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨54, 6, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((2028/125),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨122, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((2028/125),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨56, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-8112/125),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨140, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-8112/125),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨16, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨198, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨134, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((78/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((100/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨44, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨126, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((6000/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨40, 119, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨24, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨191, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-100/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨202, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((100/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨6, 4, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨42, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-100/117),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨51, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-2000/351),1,(-2,2,1,-2,0,0,0))]⟩,
  ⟨138, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/5),1,(0,0,0,0,0,0,0))]⟩
]



















































































































































def compactBlock020Indices : List ℕ := [127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 100, 98, 95, 94, 93, 92, 91, 88, 86, 84, 83, 81, 48, 47, 46, 44, 43, 41, 40, 38, 37, 36, 35, 30, 29, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 13, 12, 9, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock020Results : List Poly :=
  program_results% (compactBlock020Inputs) (compactBlock020Program) (compactBlock020Indices)

def node5887 : Poly := rowAt compactBlock020Results 0
def node5888 : Poly := rowAt compactBlock020Results 1
def node5890 : Poly := rowAt compactBlock020Results 2
def node5892 : Poly := rowAt compactBlock020Results 3
def node5897 : Poly := rowAt compactBlock020Results 4
def node5899 : Poly := rowAt compactBlock020Results 5
def node5900 : Poly := rowAt compactBlock020Results 6
def node5901 : Poly := rowAt compactBlock020Results 7
def node5902 : Poly := rowAt compactBlock020Results 8
def node5907 : Poly := rowAt compactBlock020Results 9
def node5908 : Poly := rowAt compactBlock020Results 10
def node5909 : Poly := rowAt compactBlock020Results 11
def node5910 : Poly := rowAt compactBlock020Results 12
def node5913 : Poly := rowAt compactBlock020Results 13
def node5914 : Poly := rowAt compactBlock020Results 14
def node5915 : Poly := rowAt compactBlock020Results 15
def node5916 : Poly := rowAt compactBlock020Results 16
def node5917 : Poly := rowAt compactBlock020Results 17
def node5918 : Poly := rowAt compactBlock020Results 18
def node5919 : Poly := rowAt compactBlock020Results 19
def node5920 : Poly := rowAt compactBlock020Results 20
def node5921 : Poly := rowAt compactBlock020Results 21
def node5922 : Poly := rowAt compactBlock020Results 22
def node5923 : Poly := rowAt compactBlock020Results 23
def node5924 : Poly := rowAt compactBlock020Results 24
def node5928 : Poly := rowAt compactBlock020Results 25
def node5933 : Poly := rowAt compactBlock020Results 26
def node5939 : Poly := rowAt compactBlock020Results 27
def node5940 : Poly := rowAt compactBlock020Results 28
def node5941 : Poly := rowAt compactBlock020Results 29
def node5942 : Poly := rowAt compactBlock020Results 30
def node5943 : Poly := rowAt compactBlock020Results 31
def node5951 : Poly := rowAt compactBlock020Results 32
def node5956 : Poly := rowAt compactBlock020Results 33
def node5959 : Poly := rowAt compactBlock020Results 34
def node5960 : Poly := rowAt compactBlock020Results 35
def node5962 : Poly := rowAt compactBlock020Results 36
def node6013 : Poly := rowAt compactBlock020Results 37
def node6015 : Poly := rowAt compactBlock020Results 38
def node6018 : Poly := rowAt compactBlock020Results 39
def node6021 : Poly := rowAt compactBlock020Results 40
def node6022 : Poly := rowAt compactBlock020Results 41
def node6037 : Poly := rowAt compactBlock020Results 42
def node6039 : Poly := rowAt compactBlock020Results 43
def node6043 : Poly := rowAt compactBlock020Results 44
def node6044 : Poly := rowAt compactBlock020Results 45
def node6046 : Poly := rowAt compactBlock020Results 46
def node6047 : Poly := rowAt compactBlock020Results 47
def node6053 : Poly := rowAt compactBlock020Results 48
def node6054 : Poly := rowAt compactBlock020Results 49
def node6060 : Poly := rowAt compactBlock020Results 50
def node6061 : Poly := rowAt compactBlock020Results 51
def node6062 : Poly := rowAt compactBlock020Results 52
def node6063 : Poly := rowAt compactBlock020Results 53
def node6064 : Poly := rowAt compactBlock020Results 54
def node6065 : Poly := rowAt compactBlock020Results 55
def node6068 : Poly := rowAt compactBlock020Results 56
def node6069 : Poly := rowAt compactBlock020Results 57
def node6070 : Poly := rowAt compactBlock020Results 58
def node6071 : Poly := rowAt compactBlock020Results 59
def node6072 : Poly := rowAt compactBlock020Results 60
def node6073 : Poly := rowAt compactBlock020Results 61
def node6080 : Poly := rowAt compactBlock020Results 62
def node6081 : Poly := rowAt compactBlock020Results 63
def node6089 : Poly := rowAt compactBlock020Results 64
def node6092 : Poly := rowAt compactBlock020Results 65
def node6097 : Poly := rowAt compactBlock020Results 66
def node6098 : Poly := rowAt compactBlock020Results 67
def node6099 : Poly := rowAt compactBlock020Results 68
def node6100 : Poly := rowAt compactBlock020Results 69
def node6102 : Poly := rowAt compactBlock020Results 70
def node6103 : Poly := rowAt compactBlock020Results 71
def node6104 : Poly := rowAt compactBlock020Results 72

theorem compactBlock020_certificate : outputs compactBlock020Inputs compactBlock020Program compactBlock020Indices = compactBlock020Results := by
  decide +kernel

theorem compactBlock020_derived : ∀ p ∈ compactBlock020Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock020_inputs compactBlock020Program compactBlock020Indices compactBlock020_certificate

#print axioms compactBlock020_derived


def compactBlock021Inputs : List Poly := [node0799, node0835, node1084, node1088, node1091, node1094, node1107, node1108, node1147, node1152, node1157, node1158, node1159, node1167, node1169, node1170, node1175, node1176, node1179, node1181, node1188, node1191, node3996, node3997, node3998, node4006, node4024, node4027, node4032, node4047, node4063, node4064, node4066, node4083, node4085, node4093, node4131, node4132, node4143, node4191, node4203, node4204, node4205, node4206, node4228, node4229, node4239, node4242, node4243, node4255, node4257, node4263, node4269, node4657, node4660, node5108, node5112, node5359, node5419, node5496, node5497, node5506, node5507, node5508, node5620, node5624, node5827, node5839, node5846, node5850, node5915, node5916, node5919, node5920, node5939, node5959, node6013, node6015, node6046, node6047, node6089, node6092, node6097, node6098, node6099, node6100]

theorem compactBlock021_inputs : ∀ p ∈ compactBlock021Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0799, node0835, node1084, node1088, node1091, node1094, node1107, node1108, node1147, node1152, node1157, node1158, node1159, node1167, node1169, node1170, node1175, node1176, node1179, node1181, node1188, node1191, node3996, node3997, node3998, node4006, node4024, node4027, node4032, node4047, node4063, node4064, node4066, node4083, node4085, node4093, node4131, node4132, node4143, node4191, node4203, node4204, node4205, node4206, node4228, node4229, node4239, node4242, node4243, node4255, node4257, node4263, node4269, node4657, node4660, node5108, node5112, node5359, node5419, node5496, node5497, node5506, node5507, node5508, node5620, node5624, node5827, node5839, node5846, node5850, node5915, node5916, node5919, node5920, node5939, node5959, node6013, node6015, node6046, node6047, node6089, node6092, node6097, node6098, node6099, node6100], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 799 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 835 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1084 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1088 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1091 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1094 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1107 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1108 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1147 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1152 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1157 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1158 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1159 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1167 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1169 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1170 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1175 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1176 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1179 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1181 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1188 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock011_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 69)
  exact nil_derived _ _

def compactBlock021Program : List Instruction := [
  ⟨82, 81, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨84, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((-100/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨86, 83, [(1,0,(0,0,0,0,0,0,0)),
  ((100/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨88, 84, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨33, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((-6000/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨85, 86, [(1,0,(0,0,0,0,0,0,0)),
  ((-6000/13),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨82, 27, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨74, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨83, 74, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 83, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨87, 31, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨80, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨34, 13, [(1,0,(0,0,0,0,0,0,0)),
  (2500,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨36, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨38, 15, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨85, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨78, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨81, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨76, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨85, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨36, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨47, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((81/2500),1,(1,-2,0,2,0,0,0))]⟩,
  ⟨30, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨29, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨52, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨31, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 50, [((-64/81),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨57, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 52, [((-81),0,(0,-2,0,0,0,0,0))]⟩,
  ⟨49, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 54, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨6, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨65, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨68, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨32, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨96, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨10, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨48, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨6, 63, [((-1/4),0,(1,0,0,0,0,0,0))]⟩,
  ⟨78, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨75, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1/169),1,(0,0,1,0,0,0,0))]⟩,
  ⟨79, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨124, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨10, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨30, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨30, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨11, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨65, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨71, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨8, 75, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 0, [(1,0,(0,0,0,0,0,0,0)),
  (5184,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨127, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨118, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨9, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨9, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨8, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨77, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨68, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 85, [((-5184),0,(-3,-2,0,0,0,0,0))]⟩,
  ⟨76, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨105, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨103, 22, [(1,0,(0,0,0,0,0,0,0)),
  (5184,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨105, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨114, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨108, 25, [(1,0,(0,0,0,0,0,0,0)),
  (50625,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨126, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-676),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨125, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-676),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨113, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨115, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨117, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨119, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨131, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨134, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨21, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨63, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨21, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨31, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨22, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨148, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/625),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨88, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨106, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 108, [((-4),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨147, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/4),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨149, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/4),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨16, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨16, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨16, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨16, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨14, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨14, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨57, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨14, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨171, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/16),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨30, 121, [(676,0,(-1,0,-1,0,0,0,0))]⟩,
  ⟨145, 0, [(1,0,(0,0,0,0,0,0,0)),
  (16,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨149, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨153, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨98, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨8, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨8, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨122, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨128, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨156, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 132, [((-81/64),0,(3,-2,0,0,0,0,0))]⟩,
  ⟨77, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨10, 134, [((-50625/4),0,(1,-2,0,-2,0,0,0))]⟩,
  ⟨162, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((1/50625),1,(0,2,0,2,0,0,0))]⟩,
  ⟨166, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨165, 1, [(1,0,(0,0,0,0,0,0,0)),
  (5184,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨196, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨14, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨60, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨38, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨14, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨14, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨135, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 145, [((-2500),0,(-1,0,0,-2,0,0,0))]⟩,
  ⟨177, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 147, [((1296/105625),0,(-2,-2,1,2,0,0,0))]⟩,
  ⟨200, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/16),1,(2,0,-1,0,0,0,0))]⟩
]





















































































































def compactBlock021Indices : List ℕ := [127, 126, 125, 124, 120, 119, 118, 116, 114, 112, 106, 104, 103, 95, 90, 87, 86, 81, 80, 75, 74, 71, 66, 65, 64, 62, 59, 56, 55, 50, 49, 43, 42, 41, 39, 38, 37, 36, 35, 34, 33, 32, 28, 23, 22, 19, 18, 15, 11, 10, 9, 8, 7, 6, 5, 4, 1, 0]
def compactBlock021Results : List Poly :=
  program_results% (compactBlock021Inputs) (compactBlock021Program) (compactBlock021Indices)

def node6112 : Poly := rowAt compactBlock021Results 0
def node6113 : Poly := rowAt compactBlock021Results 1
def node6114 : Poly := rowAt compactBlock021Results 2
def node6115 : Poly := rowAt compactBlock021Results 3
def node6120 : Poly := rowAt compactBlock021Results 4
def node6121 : Poly := rowAt compactBlock021Results 5
def node6122 : Poly := rowAt compactBlock021Results 6
def node6124 : Poly := rowAt compactBlock021Results 7
def node6127 : Poly := rowAt compactBlock021Results 8
def node6129 : Poly := rowAt compactBlock021Results 9
def node6136 : Poly := rowAt compactBlock021Results 10
def node6139 : Poly := rowAt compactBlock021Results 11
def node6142 : Poly := rowAt compactBlock021Results 12
def node6154 : Poly := rowAt compactBlock021Results 13
def node6163 : Poly := rowAt compactBlock021Results 14
def node6167 : Poly := rowAt compactBlock021Results 15
def node6168 : Poly := rowAt compactBlock021Results 16
def node6173 : Poly := rowAt compactBlock021Results 17
def node6174 : Poly := rowAt compactBlock021Results 18
def node6180 : Poly := rowAt compactBlock021Results 19
def node6181 : Poly := rowAt compactBlock021Results 20
def node6187 : Poly := rowAt compactBlock021Results 21
def node6193 : Poly := rowAt compactBlock021Results 22
def node6194 : Poly := rowAt compactBlock021Results 23
def node6195 : Poly := rowAt compactBlock021Results 24
def node6197 : Poly := rowAt compactBlock021Results 25
def node6201 : Poly := rowAt compactBlock021Results 26
def node6214 : Poly := rowAt compactBlock021Results 27
def node6215 : Poly := rowAt compactBlock021Results 28
def node6222 : Poly := rowAt compactBlock021Results 29
def node6223 : Poly := rowAt compactBlock021Results 30
def node6234 : Poly := rowAt compactBlock021Results 31
def node6235 : Poly := rowAt compactBlock021Results 32
def node6236 : Poly := rowAt compactBlock021Results 33
def node6247 : Poly := rowAt compactBlock021Results 34
def node6248 : Poly := rowAt compactBlock021Results 35
def node6249 : Poly := rowAt compactBlock021Results 36
def node6250 : Poly := rowAt compactBlock021Results 37
def node6251 : Poly := rowAt compactBlock021Results 38
def node6252 : Poly := rowAt compactBlock021Results 39
def node6255 : Poly := rowAt compactBlock021Results 40
def node6256 : Poly := rowAt compactBlock021Results 41
def node6262 : Poly := rowAt compactBlock021Results 42
def node6268 : Poly := rowAt compactBlock021Results 43
def node6269 : Poly := rowAt compactBlock021Results 44
def node6273 : Poly := rowAt compactBlock021Results 45
def node6274 : Poly := rowAt compactBlock021Results 46
def node6278 : Poly := rowAt compactBlock021Results 47
def node6282 : Poly := rowAt compactBlock021Results 48
def node6283 : Poly := rowAt compactBlock021Results 49
def node6284 : Poly := rowAt compactBlock021Results 50
def node6285 : Poly := rowAt compactBlock021Results 51
def node6286 : Poly := rowAt compactBlock021Results 52
def node6287 : Poly := rowAt compactBlock021Results 53
def node6288 : Poly := rowAt compactBlock021Results 54
def node6291 : Poly := rowAt compactBlock021Results 55
def node6295 : Poly := rowAt compactBlock021Results 56
def node6296 : Poly := rowAt compactBlock021Results 57

theorem compactBlock021_certificate : outputs compactBlock021Inputs compactBlock021Program compactBlock021Indices = compactBlock021Results := by
  decide +kernel

theorem compactBlock021_derived : ∀ p ∈ compactBlock021Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock021_inputs compactBlock021Program compactBlock021Indices compactBlock021_certificate

#print axioms compactBlock021_derived


def compactBlock022Inputs : List Poly := [node0826, node0849, node1075, node1089, node1096, node1097, node1098, node1102, node1103, node1104, node1106, node1109, node1110, node1114, node1121, node1135, node1136, node1137, node1138, node1140, node1145, node1146, node1148, node1150, node1151, node1155, node1156, node1160, node1161, node1163, node1166, node1168, node1171, node1172, node1174, node1178, node1191, node4286, node4333, node4391, node4517, node4832, node4834, node4885, node4886, node4887, node5094, node5096, node5097, node5098, node5101, node5106, node5346, node5347, node5349, node5352, node5353, node5355, node5462, node5465, node5469, node5471, node5473, node5474, node5477, node5480, node5483, node5491, node5494, node5610, node5612, node5618, node5621, node5763, node5765, node5860, node5864, node5865, node5866, node5868, node5871, node5872, node5873, node5874, node5880, node5907, node5914, node5921, node5923, node5924, node5941, node5942, node6043, node6054, node6072, node6073, node6127, node6142, node6167, node6168, node6195, node6197, node6201, node6235, node6255, node6269, node6273, node6278, node6282, node6286, node6287, node6288, node6295]

theorem compactBlock022_inputs : ∀ p ∈ compactBlock022Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0826, node0849, node1075, node1089, node1096, node1097, node1098, node1102, node1103, node1104, node1106, node1109, node1110, node1114, node1121, node1135, node1136, node1137, node1138, node1140, node1145, node1146, node1148, node1150, node1151, node1155, node1156, node1160, node1161, node1163, node1166, node1168, node1171, node1172, node1174, node1178, node1191, node4286, node4333, node4391, node4517, node4832, node4834, node4885, node4886, node4887, node5094, node5096, node5097, node5098, node5101, node5106, node5346, node5347, node5349, node5352, node5353, node5355, node5462, node5465, node5469, node5471, node5473, node5474, node5477, node5480, node5483, node5491, node5494, node5610, node5612, node5618, node5621, node5763, node5765, node5860, node5864, node5865, node5866, node5868, node5871, node5872, node5873, node5874, node5880, node5907, node5914, node5921, node5923, node5924, node5941, node5942, node6043, node6054, node6072, node6073, node6127, node6142, node6167, node6168, node6195, node6197, node6201, node6235, node6255, node6269, node6273, node6278, node6282, node6286, node6287, node6288, node6295], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 826 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 849 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1075 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1089 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1096 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1097 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1098 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1102 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1103 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1104 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1106 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1109 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1110 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1114 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1121 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1135 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1136 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1137 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1138 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1140 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1145 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1146 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1148 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1150 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1151 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1155 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1156 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1160 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1161 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1163 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1166 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1168 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1171 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1172 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1174 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1178 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock012_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock013_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 56)
  exact nil_derived _ _

def compactBlock022Program : List Instruction := [
  ⟨34, 112, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 97, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/625),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨105, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨110, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨113, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨118, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨3, 44, [((-4),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨1, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨107, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨42, 119, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 48, [((-625/81),0,(0,2,0,-2,0,0,0))]⟩,
  ⟨32, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨68, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨23, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨47, 59, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 63, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((81/10000),1,(2,-2,0,2,0,0,0))]⟩,
  ⟨79, 56, [((-625/5184),0,(3,2,0,-2,0,0,0))]⟩,
  ⟨87, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 99, [(1,0,(0,0,0,0,0,0,0)),
  (625,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨112, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨18, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨3, 103, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨78, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨37, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨10, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/81),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨20, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨15, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨56, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨123, 113, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨32, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨46, 115, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 116, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨10, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((64/50625),1,(-3,2,0,2,0,0,0))]⟩,
  ⟨143, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨149, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨9, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨27, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((625/16),1,(2,0,0,-2,0,0,0))]⟩,
  ⟨54, 95, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨64, 96, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨70, 97, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨147, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨97, 95, [(1,0,(0,0,0,0,0,0,0)),
  ((-219024/625),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨105, 96, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689/625),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨143, 97, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨52, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 100, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨79, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨86, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨140, 135, [(1,0,(0,0,0,0,0,0,0)),
  (2500,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨143, 136, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨51, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨32, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨28, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨34, 142, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨101, 63, [(1,0,(0,0,0,0,0,0,0)),
  (10000,1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨103, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨29, 65, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨7, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨176, 67, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨166, 69, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨168, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 163, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨144, 107, [((-64/81),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨146, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨96, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨175, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨104, 4, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨172, 159, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨91, 160, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 161, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨3, 162, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨114, 163, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨165, 118, [((-4),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨167, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨19, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨102, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨124, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨181, 126, [((-5184/625),0,(-3,-2,0,2,0,0,0))]⟩,
  ⟨45, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 128, [((-81/4),0,(1,-2,0,0,0,0,0))]⟩,
  ⟨163, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨165, 1, [(1,0,(0,0,0,0,0,0,0)),
  (64,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨36, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨189, 133, [((-2500/81),0,(-1,2,0,-2,0,0,0))]⟩,
  ⟨115, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨160, 135, [((-64),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨164, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨154, 137, [((-324),0,(-1,-2,0,0,0,0,0))]⟩,
  ⟨157, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨38, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨16, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨124, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨37, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨157, 144, [((-40000/81),0,(-3,2,0,-2,0,0,0))]⟩,
  ⟨112, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨139, 1, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨176, 179, [(1,0,(0,0,0,0,0,0,0)),
  ((1/202500),1,(1,2,0,2,0,0,0))]⟩,
  ⟨155, 92, [(1,0,(0,0,0,0,0,0,0)),
  ((625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨61, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨73, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨9, 95, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨222, 96, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 153, [((-64),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨180, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨182, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/2704),1,(2,-2,1,0,0,0,0))]⟩,
  ⟨124, 96, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨126, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 212, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨190, 181, [(1,0,(0,0,0,0,0,0,0)),
  ((1/50625),1,(0,2,0,2,0,0,0))]⟩,
  ⟨85, 160, [((-1/16),0,(2,0,0,0,0,0,0))]⟩,
  ⟨11, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨39, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨22, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩
]

















































































































































def compactBlock022Indices : List ℕ := [127, 126, 124, 116, 114, 112, 110, 106, 98, 95, 94, 92, 91, 90, 85, 84, 83, 81, 80, 79, 78, 77, 75, 74, 73, 72, 71, 67, 66, 64, 59, 57, 55, 54, 52, 50, 49, 48, 47, 46, 44, 43, 42, 39, 38, 36, 34, 33, 32, 31, 29, 27, 25, 24, 21, 20, 18, 17, 15, 13, 12, 11, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock022Results : List Poly :=
  program_results% (compactBlock022Inputs) (compactBlock022Program) (compactBlock022Indices)

def node6297 : Poly := rowAt compactBlock022Results 0
def node6298 : Poly := rowAt compactBlock022Results 1
def node6300 : Poly := rowAt compactBlock022Results 2
def node6312 : Poly := rowAt compactBlock022Results 3
def node6319 : Poly := rowAt compactBlock022Results 4
def node6322 : Poly := rowAt compactBlock022Results 5
def node6324 : Poly := rowAt compactBlock022Results 6
def node6330 : Poly := rowAt compactBlock022Results 7
def node6340 : Poly := rowAt compactBlock022Results 8
def node6344 : Poly := rowAt compactBlock022Results 9
def node6346 : Poly := rowAt compactBlock022Results 10
def node6348 : Poly := rowAt compactBlock022Results 11
def node6349 : Poly := rowAt compactBlock022Results 12
def node6350 : Poly := rowAt compactBlock022Results 13
def node6360 : Poly := rowAt compactBlock022Results 14
def node6361 : Poly := rowAt compactBlock022Results 15
def node6362 : Poly := rowAt compactBlock022Results 16
def node6364 : Poly := rowAt compactBlock022Results 17
def node6365 : Poly := rowAt compactBlock022Results 18
def node6366 : Poly := rowAt compactBlock022Results 19
def node6367 : Poly := rowAt compactBlock022Results 20
def node6368 : Poly := rowAt compactBlock022Results 21
def node6370 : Poly := rowAt compactBlock022Results 22
def node6371 : Poly := rowAt compactBlock022Results 23
def node6372 : Poly := rowAt compactBlock022Results 24
def node6374 : Poly := rowAt compactBlock022Results 25
def node6375 : Poly := rowAt compactBlock022Results 26
def node6380 : Poly := rowAt compactBlock022Results 27
def node6382 : Poly := rowAt compactBlock022Results 28
def node6384 : Poly := rowAt compactBlock022Results 29
def node6392 : Poly := rowAt compactBlock022Results 30
def node6394 : Poly := rowAt compactBlock022Results 31
def node6396 : Poly := rowAt compactBlock022Results 32
def node6397 : Poly := rowAt compactBlock022Results 33
def node6399 : Poly := rowAt compactBlock022Results 34
def node6401 : Poly := rowAt compactBlock022Results 35
def node6402 : Poly := rowAt compactBlock022Results 36
def node6403 : Poly := rowAt compactBlock022Results 37
def node6404 : Poly := rowAt compactBlock022Results 38
def node6405 : Poly := rowAt compactBlock022Results 39
def node6410 : Poly := rowAt compactBlock022Results 40
def node6411 : Poly := rowAt compactBlock022Results 41
def node6412 : Poly := rowAt compactBlock022Results 42
def node6416 : Poly := rowAt compactBlock022Results 43
def node6419 : Poly := rowAt compactBlock022Results 44
def node6421 : Poly := rowAt compactBlock022Results 45
def node6423 : Poly := rowAt compactBlock022Results 46
def node6424 : Poly := rowAt compactBlock022Results 47
def node6425 : Poly := rowAt compactBlock022Results 48
def node6427 : Poly := rowAt compactBlock022Results 49
def node6429 : Poly := rowAt compactBlock022Results 50
def node6431 : Poly := rowAt compactBlock022Results 51
def node6435 : Poly := rowAt compactBlock022Results 52
def node6436 : Poly := rowAt compactBlock022Results 53
def node6440 : Poly := rowAt compactBlock022Results 54
def node6441 : Poly := rowAt compactBlock022Results 55
def node6443 : Poly := rowAt compactBlock022Results 56
def node6444 : Poly := rowAt compactBlock022Results 57
def node6450 : Poly := rowAt compactBlock022Results 58
def node6452 : Poly := rowAt compactBlock022Results 59
def node6453 : Poly := rowAt compactBlock022Results 60
def node6454 : Poly := rowAt compactBlock022Results 61
def node6457 : Poly := rowAt compactBlock022Results 62
def node6458 : Poly := rowAt compactBlock022Results 63
def node6459 : Poly := rowAt compactBlock022Results 64
def node6460 : Poly := rowAt compactBlock022Results 65
def node6461 : Poly := rowAt compactBlock022Results 66
def node6462 : Poly := rowAt compactBlock022Results 67
def node6466 : Poly := rowAt compactBlock022Results 68
def node6468 : Poly := rowAt compactBlock022Results 69
def node6469 : Poly := rowAt compactBlock022Results 70
def node6470 : Poly := rowAt compactBlock022Results 71

theorem compactBlock022_certificate : outputs compactBlock022Inputs compactBlock022Program compactBlock022Indices = compactBlock022Results := by
  decide +kernel

theorem compactBlock022_derived : ∀ p ∈ compactBlock022Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock022_inputs compactBlock022Program compactBlock022Indices compactBlock022_certificate

#print axioms compactBlock022_derived


def compactBlock023Inputs : List Poly := [node0884, node1031, node1046, node1061, node1062, node1090, node1127, node1134, node1144, node1164, node1177, node1180, node1182, node1184, node1189, node1190, node1191, node4655, node4656, node4835, node5100, node5348, node5475, node5476, node5479, node5490, node5500, node5611, node5613, node5619, node5679, node5691, node5732, node5764, node5766, node5879, node5881, node5886, node5888, node5890, node5901, node5917, node5918, node5922, node6070, node6071, node6103, node6104, node6129, node6136, node6154, node6173, node6187, node6214, node6215, node6222, node6223, node6236, node6247, node6248, node6256, node6262, node6274, node6296, node6297, node6298, node6300, node6324, node6348, node6349, node6350, node6361, node6365, node6366, node6367, node6368, node6370, node6371, node6372, node6384, node6396, node6410, node6411, node6412, node6423, node6425, node6431, node6436, node6443, node6444, node6452, node6454, node6458, node6466, node6468, node6470]

theorem compactBlock023_inputs : ∀ p ∈ compactBlock023Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0884, node1031, node1046, node1061, node1062, node1090, node1127, node1134, node1144, node1164, node1177, node1180, node1182, node1184, node1189, node1190, node1191, node4655, node4656, node4835, node5100, node5348, node5475, node5476, node5479, node5490, node5500, node5611, node5613, node5619, node5679, node5691, node5732, node5764, node5766, node5879, node5881, node5886, node5888, node5890, node5901, node5917, node5918, node5922, node6070, node6071, node6103, node6104, node6129, node6136, node6154, node6173, node6187, node6214, node6215, node6222, node6223, node6236, node6247, node6248, node6256, node6262, node6274, node6296, node6297, node6298, node6300, node6324, node6348, node6349, node6350, node6361, node6365, node6366, node6367, node6368, node6370, node6371, node6372, node6384, node6396, node6410, node6411, node6412, node6423, node6425, node6431, node6436, node6443, node6444, node6452, node6454, node6458, node6466, node6468, node6470], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 884 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1031 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1046 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1061 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1062 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1090 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1127 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1134 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1144 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1164 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1177 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1180 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1182 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1184 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1189 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1190 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock014_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 71)
  exact nil_derived _ _

def compactBlock023Program : List Instruction := [
  ⟨91, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 94, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨81, 18, [((10000/169),0,(-2,0,1,-2,0,0,0))]⟩,
  ⟨91, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨13, 1, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨19, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨64, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/4),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨33, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/81),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨12, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨69, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨100, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 103, [(1,0,(0,0,0,0,0,0,0)),
  ((-625),1,(0,0,0,-2,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨39, 28, [((13689/625),0,(0,-2,-1,2,0,0,0))]⟩,
  ⟨41, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨43, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨101, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨67, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨50, 35, [((50625/2704),0,(2,-2,1,-2,0,0,0))]⟩,
  ⟨107, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨91, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨101, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨12, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689/16),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨63, 61, [(1,0,(0,0,0,0,0,0,0)),
  ((-105625/16),1,(2,0,-1,-2,0,0,0))]⟩,
  ⟨66, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨69, 63, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/64),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨31, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨93, 65, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/16),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨95, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨54, 48, [((1296/169),0,(-2,-2,1,0,0,0,0))]⟩,
  ⟨4, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/64),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨2, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨68, 51, [((2704/625),0,(-2,0,-1,2,0,0,0))]⟩,
  ⟨70, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨108, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨105, 2, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨89, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨62, 57, [((625/169),0,(0,0,1,-2,0,0,0))]⟩,
  ⟨86, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-676/625),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨116, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689/625),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨47, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨139, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨52, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨117, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨58, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨121, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816),1,(-3,0,-1,0,0,0,0))]⟩,
  ⟨51, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨104, 71, [(1,0,(0,0,0,0,0,0,0)),
  ((-676),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨8, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((-676),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨109, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨128, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/81),1,(-3,2,-1,0,0,0,0))]⟩,
  ⟨130, 75, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨138, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨11, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨42, 78, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 79, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/81),1,(-3,2,0,-2,0,0,0))]⟩,
  ⟨42, 80, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨137, 81, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/9),1,(-1,1,0,-2,1,0,0))]⟩,
  ⟨139, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨152, 83, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/9),1,(-3,1,0,-2,1,0,0))]⟩,
  ⟨40, 84, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨122, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((-625),1,(0,0,0,-2,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨114, 112, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 113, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 115, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨64, 116, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨118, 87, [((10000/13689),0,(-2,2,1,-2,0,0,0))]⟩,
  ⟨124, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨69, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨88, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨93, 92, [((81/169),0,(0,-2,1,0,0,0,0))]⟩,
  ⟨95, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-105625/81),1,(0,2,-1,-2,0,0,0))]⟩,
  ⟨27, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨133, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-676),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨72, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/81),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨136, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨72, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨17, 6, [(1,0,(0,0,0,0,0,0,0)),
  (25,1,(0,0,0,-1,0,1,0))]⟩,
  ⟨129, 84, [(1,0,(0,0,0,0,0,0,0)),
  ((-676/625),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨104, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689/625),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨41, 86, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨95, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨156, 90, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨42, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨172, 108, [((625/2704),0,(2,0,1,-2,0,0,0))]⟩,
  ⟨144, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨38, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨33, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨31, 3, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨109, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨140, 121, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/64),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨180, 115, [((16/169),0,(-2,0,1,0,0,0,0))]⟩,
  ⟨138, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689/16),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨141, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-8555625/64),1,(3,-2,-1,-2,0,0,0))]⟩,
  ⟨3, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/64),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨73, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨165, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/16),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨17, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/64),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨174, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/64),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨84, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/64),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨18, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/64),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨74, 9, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨39, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-625),1,(0,0,0,-2,0,0,0)),
  (25,1,(0,0,0,-1,0,1,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨90, 142, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨50, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨198, 130, [((625/13689),0,(0,2,1,-2,0,0,0))]⟩,
  ⟨180, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/625),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨148, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨31, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨30, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 7, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨209, 139, [((81/2704),0,(2,-2,1,0,0,0,0))]⟩,
  ⟨148, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1690000/81),1,(-2,2,-1,-2,0,0,0))]⟩,
  ⟨150, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/81),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨185, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/4),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨118, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]

























































































































































def compactBlock023Indices : List ℕ := [127, 126, 121, 117, 114, 113, 111, 109, 103, 102, 101, 100, 97, 94, 91, 90, 89, 88, 87, 85, 78, 76, 75, 74, 73, 71, 69, 67, 61, 59, 58, 55, 54, 53, 52, 50, 49, 48, 47, 46, 45, 44, 43, 42, 34, 33, 32, 31, 30, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock023Results : List Poly :=
  program_results% (compactBlock023Inputs) (compactBlock023Program) (compactBlock023Indices)

def node6472 : Poly := rowAt compactBlock023Results 0
def node6473 : Poly := rowAt compactBlock023Results 1
def node6481 : Poly := rowAt compactBlock023Results 2
def node6486 : Poly := rowAt compactBlock023Results 3
def node6490 : Poly := rowAt compactBlock023Results 4
def node6491 : Poly := rowAt compactBlock023Results 5
def node6493 : Poly := rowAt compactBlock023Results 6
def node6497 : Poly := rowAt compactBlock023Results 7
def node6503 : Poly := rowAt compactBlock023Results 8
def node6504 : Poly := rowAt compactBlock023Results 9
def node6506 : Poly := rowAt compactBlock023Results 10
def node6507 : Poly := rowAt compactBlock023Results 11
def node6510 : Poly := rowAt compactBlock023Results 12
def node6515 : Poly := rowAt compactBlock023Results 13
def node6518 : Poly := rowAt compactBlock023Results 14
def node6519 : Poly := rowAt compactBlock023Results 15
def node6520 : Poly := rowAt compactBlock023Results 16
def node6521 : Poly := rowAt compactBlock023Results 17
def node6522 : Poly := rowAt compactBlock023Results 18
def node6524 : Poly := rowAt compactBlock023Results 19
def node6533 : Poly := rowAt compactBlock023Results 20
def node6537 : Poly := rowAt compactBlock023Results 21
def node6538 : Poly := rowAt compactBlock023Results 22
def node6542 : Poly := rowAt compactBlock023Results 23
def node6543 : Poly := rowAt compactBlock023Results 24
def node6546 : Poly := rowAt compactBlock023Results 25
def node6548 : Poly := rowAt compactBlock023Results 26
def node6550 : Poly := rowAt compactBlock023Results 27
def node6559 : Poly := rowAt compactBlock023Results 28
def node6561 : Poly := rowAt compactBlock023Results 29
def node6562 : Poly := rowAt compactBlock023Results 30
def node6565 : Poly := rowAt compactBlock023Results 31
def node6566 : Poly := rowAt compactBlock023Results 32
def node6567 : Poly := rowAt compactBlock023Results 33
def node6568 : Poly := rowAt compactBlock023Results 34
def node6571 : Poly := rowAt compactBlock023Results 35
def node6572 : Poly := rowAt compactBlock023Results 36
def node6573 : Poly := rowAt compactBlock023Results 37
def node6574 : Poly := rowAt compactBlock023Results 38
def node6576 : Poly := rowAt compactBlock023Results 39
def node6578 : Poly := rowAt compactBlock023Results 40
def node6580 : Poly := rowAt compactBlock023Results 41
def node6581 : Poly := rowAt compactBlock023Results 42
def node6582 : Poly := rowAt compactBlock023Results 43
def node6592 : Poly := rowAt compactBlock023Results 44
def node6595 : Poly := rowAt compactBlock023Results 45
def node6597 : Poly := rowAt compactBlock023Results 46
def node6598 : Poly := rowAt compactBlock023Results 47
def node6599 : Poly := rowAt compactBlock023Results 48
def node6606 : Poly := rowAt compactBlock023Results 49
def node6607 : Poly := rowAt compactBlock023Results 50
def node6608 : Poly := rowAt compactBlock023Results 51
def node6609 : Poly := rowAt compactBlock023Results 52
def node6610 : Poly := rowAt compactBlock023Results 53
def node6611 : Poly := rowAt compactBlock023Results 54
def node6612 : Poly := rowAt compactBlock023Results 55
def node6613 : Poly := rowAt compactBlock023Results 56
def node6614 : Poly := rowAt compactBlock023Results 57
def node6616 : Poly := rowAt compactBlock023Results 58
def node6618 : Poly := rowAt compactBlock023Results 59
def node6619 : Poly := rowAt compactBlock023Results 60
def node6620 : Poly := rowAt compactBlock023Results 61
def node6621 : Poly := rowAt compactBlock023Results 62
def node6624 : Poly := rowAt compactBlock023Results 63
def node6625 : Poly := rowAt compactBlock023Results 64
def node6626 : Poly := rowAt compactBlock023Results 65
def node6627 : Poly := rowAt compactBlock023Results 66
def node6630 : Poly := rowAt compactBlock023Results 67
def node6631 : Poly := rowAt compactBlock023Results 68
def node6632 : Poly := rowAt compactBlock023Results 69
def node6633 : Poly := rowAt compactBlock023Results 70
def node6634 : Poly := rowAt compactBlock023Results 71
def node6635 : Poly := rowAt compactBlock023Results 72
def node6636 : Poly := rowAt compactBlock023Results 73
def node6637 : Poly := rowAt compactBlock023Results 74
def node6640 : Poly := rowAt compactBlock023Results 75

theorem compactBlock023_certificate : outputs compactBlock023Inputs compactBlock023Program compactBlock023Indices = compactBlock023Results := by
  decide +kernel

theorem compactBlock023_derived : ∀ p ∈ compactBlock023Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock023_inputs compactBlock023Program compactBlock023Indices compactBlock023_certificate

#print axioms compactBlock023_derived


def compactBlock024Inputs : List Poly := [node1099, node1123, node1124, node1142, node1143, node1165, node1183, node1191, node4833, node5107, node5344, node5351, node5533, node5882, node5887, node5892, node5897, node5902, node5908, node5909, node5910, node5943, node5951, node6044, node6139, node6180, node6181, node6194, node6283, node6285, node6312, node6319, node6322, node6330, node6340, node6344, node6360, node6362, node6374, node6382, node6394, node6397, node6401, node6403, node6404, node6405, node6419, node6421, node6424, node6427, node6429, node6435, node6440, node6450, node6453, node6459, node6460, node6461, node6462, node6469, node6472, node6486, node6490, node6491, node6493, node6503, node6504, node6506, node6507, node6510, node6518, node6519, node6520, node6522, node6533, node6543, node6546, node6548, node6550, node6562, node6567, node6568, node6571, node6574, node6576, node6580, node6582, node6595, node6597, node6598, node6599, node6606, node6611, node6612, node6619, node6620, node6621, node6625, node6630, node6631, node6633, node6634, node6635]

theorem compactBlock024_inputs : ∀ p ∈ compactBlock024Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node1099, node1123, node1124, node1142, node1143, node1165, node1183, node1191, node4833, node5107, node5344, node5351, node5533, node5882, node5887, node5892, node5897, node5902, node5908, node5909, node5910, node5943, node5951, node6044, node6139, node6180, node6181, node6194, node6283, node6285, node6312, node6319, node6322, node6330, node6340, node6344, node6360, node6362, node6374, node6382, node6394, node6397, node6401, node6403, node6404, node6405, node6419, node6421, node6424, node6427, node6429, node6435, node6440, node6450, node6453, node6459, node6460, node6461, node6462, node6469, node6472, node6486, node6490, node6491, node6493, node6503, node6504, node6506, node6507, node6510, node6518, node6519, node6520, node6522, node6533, node6543, node6546, node6548, node6550, node6562, node6567, node6568, node6571, node6574, node6576, node6580, node6582, node6595, node6597, node6598, node6599, node6606, node6611, node6612, node6619, node6620, node6621, node6625, node6630, node6631, node6633, node6634, node6635], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1099 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1123 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1124 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1142 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1143 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1165 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1183 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock015_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock016_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock017_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock018_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock019_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock020_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock021_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock022_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock023_derived 72)
  exact nil_derived _ _

def compactBlock024Program : List Instruction := [
  ⟨76, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-169),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨79, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨67, 103, [(1,0,(0,0,0,0,0,0,0)),
  (25,1,(0,0,0,-1,0,1,0))]⟩,
  ⟨47, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨65, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨59, 71, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨10, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨87, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨65, 111, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨29, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨91, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨33, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨12, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨9, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨18, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨48, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨23, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨51, 26, [((625/219024),0,(2,2,1,-2,0,0,0))]⟩,
  ⟨106, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-13689/625),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨63, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨109, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨115, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨123, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨121, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨115, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨117, 7, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨79, 35, [((-625/4),0,(1,0,0,-2,0,0,0))]⟩,
  ⟨33, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨85, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨21, 39, [((-1/2500),0,(1,0,0,2,0,0,0))]⟩,
  ⟨117, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨95, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨22, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨63, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨65, 6, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨27, 47, [((-64/625),0,(-3,0,0,2,0,0,0))]⟩,
  ⟨20, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((81/16),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨20, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((625/2704),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨20, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((625/2704),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨80, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨21, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((625/2704),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨21, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨120, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨22, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((625/2704),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨22, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-5625/2704),1,(2,-1,1,-2,1,0,0))]⟩,
  ⟨37, 58, [((-1/4),0,(1,0,0,0,0,0,0))]⟩,
  ⟨7, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/169),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨130, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨118, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨17, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨108, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨17, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨121, 65, [((-64),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨65, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 67, [((202500/169),0,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨156, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨54, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨12, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨75, 72, [((3240000/169),0,(-3,-2,1,-2,0,0,0))]⟩,
  ⟨3, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨148, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨104, 75, [((81/625),0,(0,-2,0,2,0,0,0))]⟩,
  ⟨33, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨54, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨120, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨118, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨107, 80, [((1/625),0,(0,0,0,2,0,0,0))]⟩,
  ⟨127, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/64),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨169, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/2704),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨6, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/16),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨6, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/16),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨119, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨109, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨140, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/16),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨126, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨22, 8, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨141, 90, [((-1296),0,(-2,-2,0,0,0,0,0))]⟩,
  ⟨157, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨54, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨86, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 96, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨56, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨43, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨127, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨160, 99, [((-50625/64),0,(3,-2,0,-2,0,0,0))]⟩,
  ⟨17, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨187, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨195, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨181, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 104, [((-625/4),0,(1,0,0,-2,0,0,0))]⟩,
  ⟨148, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨132, 106, [((5184/625),0,(-3,-2,0,2,0,0,0))]⟩,
  ⟨139, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/5184),1,(3,2,0,-2,0,0,0))]⟩,
  ⟨144, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨142, 125, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨165, 110, [((-4/81),0,(-1,2,0,0,0,0,0))]⟩,
  ⟨187, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨174, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨52, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨70, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨52, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨30, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨37, 6, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨138, 133, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 134, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨137, 134, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨130, 121, [((-64/81),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨190, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨163, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨68, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨33, 3, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨189, 126, [((-625/2704),0,(2,0,1,-2,0,0,0))]⟩,
  ⟨148, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨218, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨78, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨194, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨222, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨213, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨78, 6, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨9, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-24336/625),1,(-2,-1,-1,2,1,0,0))]⟩
]







































































































































def compactBlock024Indices : List ℕ := [127, 124, 121, 119, 116, 111, 109, 98, 94, 93, 89, 86, 85, 81, 78, 75, 73, 71, 70, 66, 64, 63, 61, 60, 56, 51, 50, 48, 47, 45, 42, 41, 40, 39, 38, 37, 36, 34, 33, 32, 31, 29, 27, 26, 25, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 12, 11, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock024Results : List Poly :=
  program_results% (compactBlock024Inputs) (compactBlock024Program) (compactBlock024Indices)

def node6642 : Poly := rowAt compactBlock024Results 0
def node6647 : Poly := rowAt compactBlock024Results 1
def node6650 : Poly := rowAt compactBlock024Results 2
def node6653 : Poly := rowAt compactBlock024Results 3
def node6656 : Poly := rowAt compactBlock024Results 4
def node6663 : Poly := rowAt compactBlock024Results 5
def node6665 : Poly := rowAt compactBlock024Results 6
def node6679 : Poly := rowAt compactBlock024Results 7
def node6686 : Poly := rowAt compactBlock024Results 8
def node6687 : Poly := rowAt compactBlock024Results 9
def node6692 : Poly := rowAt compactBlock024Results 10
def node6695 : Poly := rowAt compactBlock024Results 11
def node6696 : Poly := rowAt compactBlock024Results 12
def node6700 : Poly := rowAt compactBlock024Results 13
def node6703 : Poly := rowAt compactBlock024Results 14
def node6706 : Poly := rowAt compactBlock024Results 15
def node6708 : Poly := rowAt compactBlock024Results 16
def node6711 : Poly := rowAt compactBlock024Results 17
def node6712 : Poly := rowAt compactBlock024Results 18
def node6720 : Poly := rowAt compactBlock024Results 19
def node6722 : Poly := rowAt compactBlock024Results 20
def node6723 : Poly := rowAt compactBlock024Results 21
def node6725 : Poly := rowAt compactBlock024Results 22
def node6726 : Poly := rowAt compactBlock024Results 23
def node6731 : Poly := rowAt compactBlock024Results 24
def node6736 : Poly := rowAt compactBlock024Results 25
def node6737 : Poly := rowAt compactBlock024Results 26
def node6739 : Poly := rowAt compactBlock024Results 27
def node6740 : Poly := rowAt compactBlock024Results 28
def node6742 : Poly := rowAt compactBlock024Results 29
def node6746 : Poly := rowAt compactBlock024Results 30
def node6747 : Poly := rowAt compactBlock024Results 31
def node6748 : Poly := rowAt compactBlock024Results 32
def node6749 : Poly := rowAt compactBlock024Results 33
def node6752 : Poly := rowAt compactBlock024Results 34
def node6753 : Poly := rowAt compactBlock024Results 35
def node6757 : Poly := rowAt compactBlock024Results 36
def node6761 : Poly := rowAt compactBlock024Results 37
def node6762 : Poly := rowAt compactBlock024Results 38
def node6763 : Poly := rowAt compactBlock024Results 39
def node6764 : Poly := rowAt compactBlock024Results 40
def node6767 : Poly := rowAt compactBlock024Results 41
def node6772 : Poly := rowAt compactBlock024Results 42
def node6773 : Poly := rowAt compactBlock024Results 43
def node6774 : Poly := rowAt compactBlock024Results 44
def node6777 : Poly := rowAt compactBlock024Results 45
def node6778 : Poly := rowAt compactBlock024Results 46
def node6779 : Poly := rowAt compactBlock024Results 47
def node6780 : Poly := rowAt compactBlock024Results 48
def node6781 : Poly := rowAt compactBlock024Results 49
def node6783 : Poly := rowAt compactBlock024Results 50
def node6786 : Poly := rowAt compactBlock024Results 51
def node6787 : Poly := rowAt compactBlock024Results 52
def node6788 : Poly := rowAt compactBlock024Results 53
def node6790 : Poly := rowAt compactBlock024Results 54
def node6793 : Poly := rowAt compactBlock024Results 55
def node6794 : Poly := rowAt compactBlock024Results 56
def node6796 : Poly := rowAt compactBlock024Results 57
def node6797 : Poly := rowAt compactBlock024Results 58
def node6798 : Poly := rowAt compactBlock024Results 59
def node6799 : Poly := rowAt compactBlock024Results 60
def node6800 : Poly := rowAt compactBlock024Results 61
def node6801 : Poly := rowAt compactBlock024Results 62
def node6802 : Poly := rowAt compactBlock024Results 63
def node6803 : Poly := rowAt compactBlock024Results 64
def node6804 : Poly := rowAt compactBlock024Results 65
def node6805 : Poly := rowAt compactBlock024Results 66

theorem compactBlock024_certificate : outputs compactBlock024Inputs compactBlock024Program compactBlock024Indices = compactBlock024Results := by
  decide +kernel

theorem compactBlock024_derived : ∀ p ∈ compactBlock024Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock024_inputs compactBlock024Program compactBlock024Indices compactBlock024_certificate

#print axioms compactBlock024_derived


}
end SmallLevelTwentySixGermDAG
end
