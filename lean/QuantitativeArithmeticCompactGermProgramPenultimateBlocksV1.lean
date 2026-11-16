module
public import QuantitativeArithmeticCompactGermProgramTransitionBlocksV1
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

def compactBlock028Inputs : List Poly := [node1191, node6663, node6919, node6926, node6933, node6940, node6942, node6946, node6996, node7025, node7102, node7128, node7135, node7147, node7169, node7174, node7176, node7181, node7185, node7187, node7194, node7195, node7212, node7214, node7215, node7216, node7218, node7220, node7222, node7223, node7224, node7225, node7238, node7239, node7241, node7243, node7244, node7245, node7249, node7252, node7255, node7256, node7258, node7259, node7264, node7265, node7266, node7267, node7270, node7272, node7273, node7274, node7275, node7276, node7277, node7278, node7283, node7284, node7285, node7290, node7291, node7294, node7299, node7300, node7301, node7302, node7303, node7304, node7305, node7306, node7309, node7310, node7314, node7316, node7319, node7320]

theorem compactBlock028_inputs : ∀ p ∈ compactBlock028Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node1191, node6663, node6919, node6926, node6933, node6940, node6942, node6946, node6996, node7025, node7102, node7128, node7135, node7147, node7169, node7174, node7176, node7181, node7185, node7187, node7194, node7195, node7212, node7214, node7215, node7216, node7218, node7220, node7222, node7223, node7224, node7225, node7238, node7239, node7241, node7243, node7244, node7245, node7249, node7252, node7255, node7256, node7258, node7259, node7264, node7265, node7266, node7267, node7270, node7272, node7273, node7274, node7275, node7276, node7277, node7278, node7283, node7284, node7285, node7290, node7291, node7294, node7299, node7300, node7301, node7302, node7303, node7304, node7305, node7306, node7309, node7310, node7314, node7316, node7319, node7320], Derived sourceRows 1191 p
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock024_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock025_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock026_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock027_derived 70)
  exact nil_derived _ _

def compactBlock028Program : List Instruction := [
  ⟨22, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨15, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨43, 71, [(1,0,(0,0,0,0,0,0,0)),
  (64,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨54, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨48, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/1521),1,(-1,1,1,-2,1,0,0))]⟩,
  ⟨14, 74, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨58, 75, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/9),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨53, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((64/9),1,(-3,1,0,0,1,0,0))]⟩,
  ⟨12, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 78, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/1521),1,(-1,1,1,-2,1,0,0))]⟩,
  ⟨57, 79, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨47, 80, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨27, 81, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨68, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/13689),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨46, 14, [((16/625),0,(-2,0,0,2,0,0,0))]⟩,
  ⟨60, 0, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨5, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨1, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 57, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨15, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨73, 59, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨63, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨47, 24, [((-625/10816),0,(3,0,1,-2,0,0,0))]⟩,
  ⟨81, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨28, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨102, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨62, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/5625),1,(-3,1,-1,2,1,0,0))]⟩,
  ⟨17, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((10816/50625),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨4, 30, [((676/50625),0,(-1,2,-1,2,0,0,0))]⟩,
  ⟨49, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨48, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨53, 2, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨55, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨92, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨94, 5, [(1,0,(0,0,0,0,0,0,0)),
  (324,1,(-1,-2,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨107, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨109, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨56, 8, [(1,0,(0,0,0,0,0,0,0)),
  (40000,1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨99, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨90, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨102, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨116, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((160000/169),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨94, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-16),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨78, 14, [(1,0,(0,0,0,0,0,0,0)),
  (16,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨120, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-160000/169),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨108, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/4),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨88, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((160000/169),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨47, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-202500/169),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨112, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨27, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((256/9),1,(-4,1,0,0,1,0,0))]⟩,
  ⟨76, 21, [(1,0,(0,0,0,0,0,0,0)),
  (324,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨78, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨34, 23, [(1,0,(0,0,0,0,0,0,0)),
  (256,1,(-4,0,0,0,0,0,0))]⟩,
  ⟨26, 24, [(1,0,(0,0,0,0,0,0,0)),
  (256,1,(-4,0,0,0,0,0,0))]⟩,
  ⟨119, 25, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨39, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((256/9),1,(-4,1,0,0,1,0,0))]⟩,
  ⟨52, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨123, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨125, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨88, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0)),
  ((-36),1,(-1,-1,0,0,1,0,0))]⟩,
  ⟨53, 31, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨42, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-256/9),1,(-4,1,0,0,1,0,0))]⟩,
  ⟨130, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0))]⟩,
  ⟨132, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨44, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-256),1,(-4,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨95, 36, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨79, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-5184/169),1,(-3,-2,1,0,0,0,0)),
  ((-576/169),1,(-3,-1,1,0,1,0,0)),
  ((-64/169),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨104, 38, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨47, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-256),1,(-4,0,0,0,0,0,0)),
  (1296,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨100, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨102, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨92, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-256/9),1,(-4,1,0,0,1,0,0))]⟩,
  ⟨143, 44, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨63, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((202500/169),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨114, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-160000/169),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨83, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨91, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0)),
  ((-1600/169),1,(-3,0,1,-1,0,1,0)),
  ((64/169),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨66, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((202500/169),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨44, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨95, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨21, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨49, 55, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000),1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨34, 56, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨29, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨27, 59, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨68, 59, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨54, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨52, 61, [(1,0,(0,0,0,0,0,0,0)),
  ((10816/50625),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨46, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((10816/50625),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨125, 63, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨5, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/5625),1,(-3,1,-1,2,1,0,0))]⟩,
  ⟨132, 65, [(1,0,(0,0,0,0,0,0,0)),
  ((10816/625),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨23, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨113, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-676/625),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨152, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨100, 9, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨35, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨27, 12, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 109, [((-169/2500),0,(1,0,-1,2,0,0,0))]⟩,
  ⟨148, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨68, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨68, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨85, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨66, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨65, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨53, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨80, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨127, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨26, 9, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨193, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨9, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
  ⟨24, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨54, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨47, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨6, 126, [((-13689/10000),0,(2,-2,-1,2,0,0,0))]⟩,
  ⟨39, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]





















































































































def compactBlock028Indices : List ℕ := [127, 121, 118, 109, 87, 82, 81, 79, 77, 75, 74, 73, 70, 69, 68, 67, 64, 62, 60, 59, 57, 55, 54, 53, 52, 51, 48, 44, 41, 38, 37, 36, 35, 31, 30, 28, 27, 26, 25, 24, 22, 21, 20, 16, 14, 13, 12, 11, 10, 9, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock028Results : List Poly :=
  program_results% (compactBlock028Inputs) (compactBlock028Program) (compactBlock028Indices)

def node7322 : Poly := rowAt compactBlock028Results 0
def node7328 : Poly := rowAt compactBlock028Results 1
def node7331 : Poly := rowAt compactBlock028Results 2
def node7344 : Poly := rowAt compactBlock028Results 3
def node7371 : Poly := rowAt compactBlock028Results 4
def node7378 : Poly := rowAt compactBlock028Results 5
def node7379 : Poly := rowAt compactBlock028Results 6
def node7382 : Poly := rowAt compactBlock028Results 7
def node7384 : Poly := rowAt compactBlock028Results 8
def node7387 : Poly := rowAt compactBlock028Results 9
def node7388 : Poly := rowAt compactBlock028Results 10
def node7389 : Poly := rowAt compactBlock028Results 11
def node7394 : Poly := rowAt compactBlock028Results 12
def node7395 : Poly := rowAt compactBlock028Results 13
def node7397 : Poly := rowAt compactBlock028Results 14
def node7398 : Poly := rowAt compactBlock028Results 15
def node7401 : Poly := rowAt compactBlock028Results 16
def node7403 : Poly := rowAt compactBlock028Results 17
def node7405 : Poly := rowAt compactBlock028Results 18
def node7406 : Poly := rowAt compactBlock028Results 19
def node7408 : Poly := rowAt compactBlock028Results 20
def node7410 : Poly := rowAt compactBlock028Results 21
def node7411 : Poly := rowAt compactBlock028Results 22
def node7412 : Poly := rowAt compactBlock028Results 23
def node7413 : Poly := rowAt compactBlock028Results 24
def node7414 : Poly := rowAt compactBlock028Results 25
def node7420 : Poly := rowAt compactBlock028Results 26
def node7424 : Poly := rowAt compactBlock028Results 27
def node7429 : Poly := rowAt compactBlock028Results 28
def node7432 : Poly := rowAt compactBlock028Results 29
def node7434 : Poly := rowAt compactBlock028Results 30
def node7435 : Poly := rowAt compactBlock028Results 31
def node7436 : Poly := rowAt compactBlock028Results 32
def node7442 : Poly := rowAt compactBlock028Results 33
def node7444 : Poly := rowAt compactBlock028Results 34
def node7446 : Poly := rowAt compactBlock028Results 35
def node7447 : Poly := rowAt compactBlock028Results 36
def node7448 : Poly := rowAt compactBlock028Results 37
def node7449 : Poly := rowAt compactBlock028Results 38
def node7450 : Poly := rowAt compactBlock028Results 39
def node7453 : Poly := rowAt compactBlock028Results 40
def node7454 : Poly := rowAt compactBlock028Results 41
def node7455 : Poly := rowAt compactBlock028Results 42
def node7460 : Poly := rowAt compactBlock028Results 43
def node7463 : Poly := rowAt compactBlock028Results 44
def node7464 : Poly := rowAt compactBlock028Results 45
def node7465 : Poly := rowAt compactBlock028Results 46
def node7466 : Poly := rowAt compactBlock028Results 47
def node7467 : Poly := rowAt compactBlock028Results 48
def node7468 : Poly := rowAt compactBlock028Results 49
def node7470 : Poly := rowAt compactBlock028Results 50
def node7471 : Poly := rowAt compactBlock028Results 51
def node7472 : Poly := rowAt compactBlock028Results 52
def node7473 : Poly := rowAt compactBlock028Results 53
def node7475 : Poly := rowAt compactBlock028Results 54
def node7476 : Poly := rowAt compactBlock028Results 55
def node7478 : Poly := rowAt compactBlock028Results 56
def node7479 : Poly := rowAt compactBlock028Results 57

private def compactBlock028Stage00Code : List Instruction := [
⟨22, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨15, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨43, 71, [(1,0,(0,0,0,0,0,0,0)),
  (64,1,(-3,0,0,0,0,0,0))]⟩,
⟨54, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((64/81),1,(-3,2,0,0,0,0,0))]⟩,
⟨48, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/1521),1,(-1,1,1,-2,1,0,0))]⟩,
⟨14, 74, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨58, 75, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/9),1,(-3,1,0,0,1,0,0))]⟩,
⟨53, 76, [(1,0,(0,0,0,0,0,0,0)),
  ((64/9),1,(-3,1,0,0,1,0,0))]⟩,
⟨12, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨63, 78, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/1521),1,(-1,1,1,-2,1,0,0))]⟩,
⟨57, 79, [(1,0,(0,0,0,0,0,0,0)),
  ((-64/81),1,(-3,2,0,0,0,0,0))]⟩,
⟨47, 80, [(1,0,(0,0,0,0,0,0,0)),
  ((-64),1,(-3,0,0,0,0,0,0))]⟩,
⟨27, 81, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨68, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/13689),1,(-1,2,1,-2,0,0,0))]⟩,
⟨46, 14, [((16/625),0,(-2,0,0,2,0,0,0))]⟩,
⟨60, 0, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩
]

private def compactBlock028Stage00State : List Poly := program_state% (compactBlock028Inputs) (compactBlock028Stage00Code)

private theorem compactBlock028Stage00_checked : run compactBlock028Inputs compactBlock028Stage00Code = compactBlock028Stage00State := by
  decide +kernel

private def compactBlock028Stage01Code : List Instruction := [
⟨5, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
⟨1, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨61, 57, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨15, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
⟨73, 59, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
⟨63, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨5, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨20, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨47, 24, [((-625/10816),0,(3,0,1,-2,0,0,0))]⟩,
⟨81, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨28, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨102, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨62, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/5625),1,(-3,1,-1,2,1,0,0))]⟩,
⟨17, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((10816/50625),1,(-3,2,-1,2,0,0,0))]⟩,
⟨4, 30, [((676/50625),0,(-1,2,-1,2,0,0,0))]⟩,
⟨49, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]

private def compactBlock028Stage01State : List Poly := program_state% (compactBlock028Stage00State) (compactBlock028Stage01Code)

private theorem compactBlock028Stage01_checked : run compactBlock028Stage00State compactBlock028Stage01Code = compactBlock028Stage01State := by
  decide +kernel

private def compactBlock028Stage02Code : List Instruction := [
⟨48, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨53, 2, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨55, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨92, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/676),1,(1,-2,1,-2,0,0,0))]⟩,
⟨94, 5, [(1,0,(0,0,0,0,0,0,0)),
  (324,1,(-1,-2,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨107, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨109, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨56, 8, [(1,0,(0,0,0,0,0,0,0)),
  (40000,1,(-3,0,0,-2,0,0,0))]⟩,
⟨99, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((625/4),1,(1,0,0,-2,0,0,0))]⟩,
⟨90, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
⟨102, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨116, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((160000/169),1,(-4,0,1,-2,0,0,0))]⟩,
⟨94, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-16),1,(-2,0,0,0,0,0,0))]⟩,
⟨78, 14, [(1,0,(0,0,0,0,0,0,0)),
  (16,1,(-2,0,0,0,0,0,0))]⟩,
⟨120, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-160000/169),1,(-4,0,1,-2,0,0,0))]⟩,
⟨108, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-625/4),1,(1,0,0,-2,0,0,0))]⟩
]

private def compactBlock028Stage02State : List Poly := program_state% (compactBlock028Stage01State) (compactBlock028Stage02Code)

private theorem compactBlock028Stage02_checked : run compactBlock028Stage01State compactBlock028Stage02Code = compactBlock028Stage02State := by
  decide +kernel

private def compactBlock028Stage03Code : List Instruction := [
⟨88, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((160000/169),1,(-4,0,1,-2,0,0,0))]⟩,
⟨47, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-202500/169),1,(-1,-2,1,-2,0,0,0))]⟩,
⟨112, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
⟨27, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((256/9),1,(-4,1,0,0,1,0,0))]⟩,
⟨76, 21, [(1,0,(0,0,0,0,0,0,0)),
  (324,1,(-1,-2,0,0,0,0,0))]⟩,
⟨78, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
⟨34, 23, [(1,0,(0,0,0,0,0,0,0)),
  (256,1,(-4,0,0,0,0,0,0))]⟩,
⟨26, 24, [(1,0,(0,0,0,0,0,0,0)),
  (256,1,(-4,0,0,0,0,0,0))]⟩,
⟨119, 25, [(1,0,(0,0,0,0,0,0,0)),
  (9,1,(0,-1,0,0,1,0,0))]⟩,
⟨39, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((256/9),1,(-4,1,0,0,1,0,0))]⟩,
⟨52, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0))]⟩,
⟨123, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
⟨125, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((810000/169),1,(-2,-2,1,-2,0,0,0))]⟩,
⟨88, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0)),
  ((-36),1,(-1,-1,0,0,1,0,0))]⟩,
⟨53, 31, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
⟨42, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-256/9),1,(-4,1,0,0,1,0,0))]⟩
]

private def compactBlock028Stage03State : List Poly := program_state% (compactBlock028Stage02State) (compactBlock028Stage03Code)

private theorem compactBlock028Stage03_checked : run compactBlock028Stage02State compactBlock028Stage03Code = compactBlock028Stage03State := by
  decide +kernel

private def compactBlock028Stage04Code : List Instruction := [
⟨130, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0))]⟩,
⟨132, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((81/4),1,(1,-2,0,0,0,0,0))]⟩,
⟨44, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-256),1,(-4,0,0,0,0,0,0)),
  ((-1296),1,(-2,-2,0,0,0,0,0))]⟩,
⟨95, 36, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨79, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-5184/169),1,(-3,-2,1,0,0,0,0)),
  ((-576/169),1,(-3,-1,1,0,1,0,0)),
  ((-64/169),1,(-3,0,1,0,0,0,0))]⟩,
⟨104, 38, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨47, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-256),1,(-4,0,0,0,0,0,0)),
  (1296,1,(-2,-2,0,0,0,0,0))]⟩,
⟨100, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
⟨102, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-324),1,(-1,-2,0,0,0,0,0))]⟩,
⟨92, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-81),1,(0,-2,0,0,0,0,0)),
  ((-9),1,(0,-1,0,0,1,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨44, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-256/9),1,(-4,1,0,0,1,0,0))]⟩,
⟨143, 44, [(1,0,(0,0,0,0,0,0,0)),
  (81,1,(0,-2,0,0,0,0,0))]⟩,
⟨63, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((202500/169),1,(-1,-2,1,-2,0,0,0))]⟩,
⟨114, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-160000/169),1,(-4,0,1,-2,0,0,0))]⟩,
⟨83, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-50625/169),1,(0,-2,1,-2,0,0,0))]⟩,
⟨91, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0)),
  ((-1600/169),1,(-3,0,1,-1,0,1,0)),
  ((64/169),1,(-3,0,1,0,0,0,0))]⟩
]

private def compactBlock028Stage04State : List Poly := program_state% (compactBlock028Stage03State) (compactBlock028Stage04Code)

private theorem compactBlock028Stage04_checked : run compactBlock028Stage03State compactBlock028Stage04Code = compactBlock028Stage04State := by
  decide +kernel

private def compactBlock028Stage05Code : List Instruction := [
⟨66, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((202500/169),1,(-1,-2,1,-2,0,0,0))]⟩,
⟨44, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨95, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨26, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨45, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨2, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨21, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨5, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨2, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨49, 55, [(1,0,(0,0,0,0,0,0,0)),
  ((-10000),1,(-2,0,0,-2,0,0,0))]⟩,
⟨34, 56, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨29, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨7, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨4, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨27, 59, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-1,0,0,0,0,0,0))]⟩,
⟨68, 59, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]

private def compactBlock028Stage05State : List Poly := program_state% (compactBlock028Stage04State) (compactBlock028Stage05Code)

private theorem compactBlock028Stage05_checked : run compactBlock028Stage04State compactBlock028Stage05Code = compactBlock028Stage05State := by
  decide +kernel

private def compactBlock028Stage06Code : List Instruction := [
⟨54, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨52, 61, [(1,0,(0,0,0,0,0,0,0)),
  ((10816/50625),1,(-3,2,-1,2,0,0,0))]⟩,
⟨46, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((10816/50625),1,(-3,2,-1,2,0,0,0))]⟩,
⟨125, 63, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨5, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-10816/5625),1,(-3,1,-1,2,1,0,0))]⟩,
⟨132, 65, [(1,0,(0,0,0,0,0,0,0)),
  ((10816/625),1,(-3,0,-1,2,0,0,0))]⟩,
⟨23, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨113, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-676/625),1,(-1,0,-1,2,0,0,0))]⟩,
⟨152, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨100, 9, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨98, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-2704/625),1,(-2,0,-1,2,0,0,0))]⟩,
⟨35, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨27, 12, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨4, 109, [((-169/2500),0,(1,0,-1,2,0,0,0))]⟩,
⟨148, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨68, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩
]

private def compactBlock028Stage06State : List Poly := program_state% (compactBlock028Stage05State) (compactBlock028Stage06Code)

private theorem compactBlock028Stage06_checked : run compactBlock028Stage05State compactBlock028Stage06Code = compactBlock028Stage06State := by
  decide +kernel

private def compactBlock028Stage07Code : List Instruction := [
⟨68, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((10000/169),1,(-2,0,1,-2,0,0,0))]⟩,
⟨85, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨66, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-2500/81),1,(-1,2,0,-2,0,0,0))]⟩,
⟨65, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨53, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨8, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((2500/169),1,(-1,0,1,-2,0,0,0))]⟩,
⟨80, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨127, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
⟨26, 9, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
⟨193, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨9, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-40000/13689),1,(-3,2,1,-2,0,0,0))]⟩,
⟨24, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-1,0,0,0,0,0,0))]⟩,
⟨54, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
⟨47, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((40000/169),1,(-3,0,1,-2,0,0,0))]⟩,
⟨6, 126, [((-13689/10000),0,(2,-2,-1,2,0,0,0))]⟩,
⟨39, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]

private def compactBlock028Stage07State : List Poly := program_state% (compactBlock028Stage06State) (compactBlock028Stage07Code)

private theorem compactBlock028Stage07_checked : run compactBlock028Stage06State compactBlock028Stage07Code = compactBlock028Stage07State := by
  decide +kernel

theorem compactBlock028_certificate : outputs compactBlock028Inputs compactBlock028Program compactBlock028Indices = compactBlock028Results := by
  apply outputs_of_run_result (last := compactBlock028Stage07State)
  · change run compactBlock028Inputs (((((((compactBlock028Stage00Code ++ compactBlock028Stage01Code) ++ compactBlock028Stage02Code) ++ compactBlock028Stage03Code) ++ compactBlock028Stage04Code) ++ compactBlock028Stage05Code) ++ compactBlock028Stage06Code) ++ compactBlock028Stage07Code) = _
    exact run_append_of_results (run_append_of_results (run_append_of_results (run_append_of_results (run_append_of_results (run_append_of_results (run_append_of_results (compactBlock028Stage00_checked) compactBlock028Stage01_checked) compactBlock028Stage02_checked) compactBlock028Stage03_checked) compactBlock028Stage04_checked) compactBlock028Stage05_checked) compactBlock028Stage06_checked) compactBlock028Stage07_checked
  · decide +kernel

theorem compactBlock028_derived : ∀ p ∈ compactBlock028Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock028_inputs compactBlock028Program compactBlock028Indices compactBlock028_certificate

#print axioms compactBlock028_derived


}
end SmallLevelTwentySixGermDAG
end
