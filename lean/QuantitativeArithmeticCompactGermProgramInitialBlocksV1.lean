module
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

def node1191 : Poly := []
theorem node1191_derived : Derived sourceRows 1191 node1191 := Derived.zero

def compactBlock000Inputs : List Poly := [node0005, node0010, node0020, node0023, node0025, node0036, node0041, node0046, node0047, node0070, node0076, node0098, node0105, node0167, node0191, node0194, node0229, node0233, node0235, node0238, node0239, node0240, node0246, node0253, node0254, node0256, node0257, node0258, node0271, node0272, node0286, node0287, node0290, node0291, node0292, node0293, node0297, node0300, node0313, node0314, node0385, node0407, node0420, node0422, node0433, node0443, node0444, node0467, node0473, node0495, node0502, node0588, node0591, node0626, node0630, node0632, node0635, node0636, node0637, node0638, node0643, node0650, node0651, node0653, node0654, node0655, node0668, node0669, node0670, node0683, node0684, node0688, node0689, node0690, node0804, node0817, node0819, node0830, node0840, node0841, node0864, node0870, node0892, node0899, node0985, node0988, node1023, node1027, node1029, node1032, node1033, node1034, node1035, node1040, node1050, node1067, node1085, node1086, node1087, node1092, node1191]

theorem compactBlock000_inputs : ∀ p ∈ compactBlock000Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0005, node0010, node0020, node0023, node0025, node0036, node0041, node0046, node0047, node0070, node0076, node0098, node0105, node0167, node0191, node0194, node0229, node0233, node0235, node0238, node0239, node0240, node0246, node0253, node0254, node0256, node0257, node0258, node0271, node0272, node0286, node0287, node0290, node0291, node0292, node0293, node0297, node0300, node0313, node0314, node0385, node0407, node0420, node0422, node0433, node0443, node0444, node0467, node0473, node0495, node0502, node0588, node0591, node0626, node0630, node0632, node0635, node0636, node0637, node0638, node0643, node0650, node0651, node0653, node0654, node0655, node0668, node0669, node0670, node0683, node0684, node0688, node0689, node0690, node0804, node0817, node0819, node0830, node0840, node0841, node0864, node0870, node0892, node0899, node0985, node0988, node1023, node1027, node1029, node1032, node1033, node1034, node1035, node1040, node1050, node1067, node1085, node1086, node1087, node1092, node1191], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 5 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 10 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 20 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 23 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 25 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 36 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 41 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 46 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 47 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 70 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 76 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 98 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 105 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 167 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 191 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 194 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 229 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 233 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 235 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 238 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 239 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 240 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 246 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 253 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 254 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 256 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 257 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 258 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 271 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 272 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 286 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 287 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 290 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 291 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 292 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 293 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 297 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 300 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 313 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 314 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 385 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 407 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 420 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 422 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 433 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 443 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 444 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 467 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 473 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 495 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 502 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 588 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 591 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 626 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 630 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 632 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 635 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 636 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 637 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 638 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 643 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 650 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 651 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 653 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 654 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 655 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 668 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 669 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 670 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 683 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 684 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 688 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 689 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 690 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 804 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 817 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 819 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 830 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 840 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 841 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 864 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 870 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 892 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 899 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 985 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 988 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1023 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1027 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1029 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1032 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1033 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1034 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1035 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1040 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1050 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1067 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1085 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1086 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1087 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1092 (by decide))
  apply cons_derived node1191_derived
  exact nil_derived _ _

def compactBlock000Program : List Instruction := [
  ⟨8, 6, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨12, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨17, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨24, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨35, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨37, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨39, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨42, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨54, 14, [(1,0,(0,0,0,0,0,0,0)),
  (130,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨58, 15, [(1,0,(0,0,0,0,0,0,0)),
  (30,1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨62, 16, [(1,0,(0,0,0,0,0,0,0)),
  (338,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨69, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨83, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨86, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨93, 20, [(1,0,(0,0,0,0,0,0,0)),
  (8450,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨97, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨101, 22, [(1,0,(0,0,0,0,0,0,0)),
  (57122,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨108, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨114, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨117, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨119, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨35, 20, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,0,2,0,0,0))]⟩,
  ⟨61, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨74, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-507/5),1,(1,-2,0,2,0,0,0))]⟩,
  ⟨108, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((257049/50),1,(1,-2,0,2,0,0,0))]⟩,
  ⟨62, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨27, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨30, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨64, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 129, [((-1),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨46, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨107, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨2, 133, [((-1),0,(0,-2,0,0,0,0,0))]⟩,
  ⟨87, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-208/3),1,(0,2,0,0,0,0,0))]⟩,
  ⟨121, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((21632/9),1,(0,2,0,0,0,0,0))]⟩,
  ⟨9, 136, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨79, 1, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(0,0,0,0,0,0,0))]⟩,
  ⟨113, 2, [(1,0,(0,0,0,0,0,0,0)),
  (3042,1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨76, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨106, 40, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨112, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨117, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨140, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨142, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨145, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨28, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨9, 150, [((-1),0,(1,0,0,0,0,0,0))]⟩,
  ⟨60, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨62, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,0,0,0,0))]⟩,
  ⟨71, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨13, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨50, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨50, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨50, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨99, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨103, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨109, 10, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(0,0,1,0,0,0,0))]⟩,
  ⟨122, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-30),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨19, 12, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨51, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨51, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨142, 15, [(1,0,(0,0,0,0,0,0,0)),
  (338,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨148, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(0,0,1,0,0,0,0))]⟩,
  ⟨161, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨22, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨51, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨51, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨22, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨19, 173, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨79, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨105, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨19, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨122, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨134, 5, [(1,0,(0,0,0,0,0,0,0)),
  (208,1,(0,0,0,0,0,0,0))]⟩,
  ⟨139, 6, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨16, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨159, 8, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨171, 9, [(1,0,(0,0,0,0,0,0,0)),
  (21632,1,(0,0,0,0,0,0,0))]⟩,
  ⟨176, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨14, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨13, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨125, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨36, 188, [((-1),0,(-3,-2,0,0,0,0,0))]⟩,
  ⟨136, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((13/6),1,(3,2,0,0,0,0,0))]⟩,
  ⟨170, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((169/72),1,(3,2,0,0,0,0,0))]⟩,
  ⟨93, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨99, 39, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨105, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨107, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 42, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨115, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨117, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨121, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨123, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨126, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨128, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨130, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨132, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨28, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨100, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨28, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨48, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨153, 55, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨159, 56, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨164, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((-3120),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨167, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨169, 59, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨174, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨176, 61, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨179, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨181, 63, [(1,0,(0,0,0,0,0,0,0)),
  (52,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨183, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨185, 65, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨188, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨190, 67, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨39, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨56, 69, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨201, 70, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨207, 71, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨212, 72, [(1,0,(0,0,0,0,0,0,0)),
  (4867200,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨215, 73, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨217, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,0,-1,0,0,0,0))]⟩
]

















































































































































































def compactBlock000Indices : List ℕ := [126, 124, 119, 118, 117, 116, 113, 112, 111, 110, 105, 104, 103, 102, 96, 95, 93, 92, 90, 89, 88, 85, 83, 82, 80, 79, 75, 73, 72, 68, 67, 66, 65, 64, 61, 60, 59, 58, 56, 51, 49, 48, 47, 45, 44, 43, 42, 41, 40, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock000Results : List Poly :=
  program_results% (compactBlock000Inputs) (compactBlock000Program) (compactBlock000Indices)

def node1194 : Poly := rowAt compactBlock000Results 0
def node1196 : Poly := rowAt compactBlock000Results 1
def node1204 : Poly := rowAt compactBlock000Results 2
def node1205 : Poly := rowAt compactBlock000Results 3
def node1206 : Poly := rowAt compactBlock000Results 4
def node1207 : Poly := rowAt compactBlock000Results 5
def node1211 : Poly := rowAt compactBlock000Results 6
def node1212 : Poly := rowAt compactBlock000Results 7
def node1213 : Poly := rowAt compactBlock000Results 8
def node1214 : Poly := rowAt compactBlock000Results 9
def node1220 : Poly := rowAt compactBlock000Results 10
def node1221 : Poly := rowAt compactBlock000Results 11
def node1222 : Poly := rowAt compactBlock000Results 12
def node1225 : Poly := rowAt compactBlock000Results 13
def node1244 : Poly := rowAt compactBlock000Results 14
def node1245 : Poly := rowAt compactBlock000Results 15
def node1248 : Poly := rowAt compactBlock000Results 16
def node1249 : Poly := rowAt compactBlock000Results 17
def node1254 : Poly := rowAt compactBlock000Results 18
def node1255 : Poly := rowAt compactBlock000Results 19
def node1256 : Poly := rowAt compactBlock000Results 20
def node1263 : Poly := rowAt compactBlock000Results 21
def node1271 : Poly := rowAt compactBlock000Results 22
def node1272 : Poly := rowAt compactBlock000Results 23
def node1277 : Poly := rowAt compactBlock000Results 24
def node1278 : Poly := rowAt compactBlock000Results 25
def node1282 : Poly := rowAt compactBlock000Results 26
def node1284 : Poly := rowAt compactBlock000Results 27
def node1285 : Poly := rowAt compactBlock000Results 28
def node1292 : Poly := rowAt compactBlock000Results 29
def node1293 : Poly := rowAt compactBlock000Results 30
def node1294 : Poly := rowAt compactBlock000Results 31
def node1295 : Poly := rowAt compactBlock000Results 32
def node1296 : Poly := rowAt compactBlock000Results 33
def node1300 : Poly := rowAt compactBlock000Results 34
def node1301 : Poly := rowAt compactBlock000Results 35
def node1302 : Poly := rowAt compactBlock000Results 36
def node1303 : Poly := rowAt compactBlock000Results 37
def node1305 : Poly := rowAt compactBlock000Results 38
def node1314 : Poly := rowAt compactBlock000Results 39
def node1320 : Poly := rowAt compactBlock000Results 40
def node1322 : Poly := rowAt compactBlock000Results 41
def node1323 : Poly := rowAt compactBlock000Results 42
def node1327 : Poly := rowAt compactBlock000Results 43
def node1329 : Poly := rowAt compactBlock000Results 44
def node1330 : Poly := rowAt compactBlock000Results 45
def node1331 : Poly := rowAt compactBlock000Results 46
def node1332 : Poly := rowAt compactBlock000Results 47
def node1333 : Poly := rowAt compactBlock000Results 48
def node1337 : Poly := rowAt compactBlock000Results 49
def node1338 : Poly := rowAt compactBlock000Results 50
def node1342 : Poly := rowAt compactBlock000Results 51
def node1343 : Poly := rowAt compactBlock000Results 52
def node1344 : Poly := rowAt compactBlock000Results 53
def node1352 : Poly := rowAt compactBlock000Results 54
def node1356 : Poly := rowAt compactBlock000Results 55
def node1357 : Poly := rowAt compactBlock000Results 56
def node1358 : Poly := rowAt compactBlock000Results 57
def node1359 : Poly := rowAt compactBlock000Results 58
def node1360 : Poly := rowAt compactBlock000Results 59
def node1361 : Poly := rowAt compactBlock000Results 60
def node1362 : Poly := rowAt compactBlock000Results 61
def node1365 : Poly := rowAt compactBlock000Results 62
def node1366 : Poly := rowAt compactBlock000Results 63
def node1371 : Poly := rowAt compactBlock000Results 64
def node1372 : Poly := rowAt compactBlock000Results 65
def node1373 : Poly := rowAt compactBlock000Results 66
def node1374 : Poly := rowAt compactBlock000Results 67
def node1377 : Poly := rowAt compactBlock000Results 68
def node1378 : Poly := rowAt compactBlock000Results 69
def node1389 : Poly := rowAt compactBlock000Results 70
def node1390 : Poly := rowAt compactBlock000Results 71
def node1391 : Poly := rowAt compactBlock000Results 72
def node1392 : Poly := rowAt compactBlock000Results 73
def node1393 : Poly := rowAt compactBlock000Results 74
def node1394 : Poly := rowAt compactBlock000Results 75
def node1395 : Poly := rowAt compactBlock000Results 76
def node1398 : Poly := rowAt compactBlock000Results 77
def node1399 : Poly := rowAt compactBlock000Results 78
def node1404 : Poly := rowAt compactBlock000Results 79
def node1405 : Poly := rowAt compactBlock000Results 80
def node1406 : Poly := rowAt compactBlock000Results 81
def node1407 : Poly := rowAt compactBlock000Results 82
def node1409 : Poly := rowAt compactBlock000Results 83
def node1410 : Poly := rowAt compactBlock000Results 84
def node1421 : Poly := rowAt compactBlock000Results 85
def node1422 : Poly := rowAt compactBlock000Results 86
def node1423 : Poly := rowAt compactBlock000Results 87

theorem compactBlock000_certificate : outputs compactBlock000Inputs compactBlock000Program compactBlock000Indices = compactBlock000Results := by
  decide +kernel

theorem compactBlock000_derived : ∀ p ∈ compactBlock000Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock000_inputs compactBlock000Program compactBlock000Indices compactBlock000_certificate

#print axioms compactBlock000_derived


def compactBlock001Inputs : List Poly := [node0009, node0017, node0022, node0026, node0069, node0097, node0123, node0126, node0127, node0140, node0211, node0226, node0228, node0230, node0231, node0232, node0234, node0242, node0243, node0244, node0247, node0255, node0275, node0276, node0294, node0309, node0394, node0406, node0414, node0417, node0419, node0466, node0494, node0535, node0564, node0608, node0623, node0625, node0627, node0639, node0640, node0641, node0642, node0644, node0652, node0671, node0672, node0673, node0803, node0811, node0814, node0816, node0863, node0891, node0932, node0961, node1005, node1020, node1022, node1024, node1036, node1037, node1038, node1039, node1041, node1047, node1048, node1049, node1051, node1052, node1065, node1066, node1068, node1069, node1070, node1080, node1081, node1191, node1194, node1225, node1254, node1263, node1272, node1278, node1282, node1305, node1314, node1331, node1332, node1342, node1343, node1344, node1352, node1356, node1359, node1360, node1361, node1362, node1371, node1372, node1373, node1374, node1392, node1393, node1394, node1395, node1404, node1405, node1406, node1407]

theorem compactBlock001_inputs : ∀ p ∈ compactBlock001Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0009, node0017, node0022, node0026, node0069, node0097, node0123, node0126, node0127, node0140, node0211, node0226, node0228, node0230, node0231, node0232, node0234, node0242, node0243, node0244, node0247, node0255, node0275, node0276, node0294, node0309, node0394, node0406, node0414, node0417, node0419, node0466, node0494, node0535, node0564, node0608, node0623, node0625, node0627, node0639, node0640, node0641, node0642, node0644, node0652, node0671, node0672, node0673, node0803, node0811, node0814, node0816, node0863, node0891, node0932, node0961, node1005, node1020, node1022, node1024, node1036, node1037, node1038, node1039, node1041, node1047, node1048, node1049, node1051, node1052, node1065, node1066, node1068, node1069, node1070, node1080, node1081, node1191, node1194, node1225, node1254, node1263, node1272, node1278, node1282, node1305, node1314, node1331, node1332, node1342, node1343, node1344, node1352, node1356, node1359, node1360, node1361, node1362, node1371, node1372, node1373, node1374, node1392, node1393, node1394, node1395, node1404, node1405, node1406, node1407], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 9 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 17 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 22 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 26 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 69 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 97 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 123 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 126 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 127 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 140 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 211 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 226 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 228 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 230 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 231 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 232 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 234 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 242 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 243 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 244 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 247 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 255 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 275 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 276 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 294 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 309 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 394 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 406 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 414 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 417 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 419 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 466 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 494 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 535 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 564 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 608 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 623 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 625 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 627 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 639 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 640 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 641 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 642 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 644 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 652 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 671 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 672 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 673 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 803 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 811 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 814 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 816 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 863 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 891 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 932 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 961 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1005 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1020 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1022 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1024 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1036 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1037 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1038 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1039 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1041 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1047 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1048 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1049 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1051 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1052 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1065 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1066 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1068 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1069 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1070 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1080 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1081 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 82)
  exact nil_derived _ _

def compactBlock001Program : List Instruction := [
  ⟨65, 84, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨67, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨70, 86, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨72, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨74, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨76, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨81, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨83, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨95, 92, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨94, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨98, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨30, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨36, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨39, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨77, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨105, 93, [((-1),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨34, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨36, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨113, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨115, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨117, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨119, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨121, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨123, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨106, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨127, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(1,0,0,0,0,0,0))]⟩,
  ⟨67, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨69, 12, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(1,0,-1,0,0,0,0))]⟩,
  ⟨132, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨134, 14, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨136, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨138, 16, [(1,0,(0,0,0,0,0,0,0)),
  (52,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨140, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨142, 18, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨118, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨87, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((169/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨98, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨100, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨39, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨39, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,-1,0,0,0,0))]⟩,
  ⟨39, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨39, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨37, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨37, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨129, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨36, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨70, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨95, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨123, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨143, 128, [(1,0,(-1,0,-1,0,0,0,0))]⟩,
  ⟨52, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨54, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨75, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨29, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨29, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨84, 5, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨92, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-27),1,(1,0,1,0,0,0,0))]⟩,
  ⟨103, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨105, 8, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨24, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨110, 10, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨118, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-729/2),1,(1,0,1,0,0,0,0))]⟩,
  ⟨131, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨137, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-2,0,1,-2,0,0,0))]⟩,
  ⟨19, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨19, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨70, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 146, [((-1),0,(3,-2,0,0,0,0,0))]⟩,
  ⟨150, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨101, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/3),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨123, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨19, 150, [((-1),0,(1,-2,0,-2,0,0,0))]⟩,
  ⟨86, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,2,0,2,0,0,0))]⟩,
  ⟨103, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/15),1,(-1,2,0,2,0,0,0))]⟩,
  ⟨113, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-208/15),1,(0,2,0,2,0,0,0))]⟩,
  ⟨126, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((338/225),1,(-1,2,0,2,0,0,0))]⟩,
  ⟨136, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((21632/225),1,(0,2,0,2,0,0,0))]⟩,
  ⟨83, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨100, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨26, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨168, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨183, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨27, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨118, 10, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨129, 11, [(1,0,(0,0,0,0,0,0,0)),
  (30,1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨27, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨196, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨198, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨144, 15, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨155, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨27, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨84, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨84, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨27, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨16, 173, [((-1),0,(-1,0,0,-2,0,0,0))]⟩,
  ⟨102, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((13/5),1,(1,0,0,2,0,0,0))]⟩,
  ⟨151, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((169/50),1,(1,0,0,2,0,0,0))]⟩,
  ⟨2, 177, [(1,0,(-2,-2,1,2,0,0,0))]⟩,
  ⟨124, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨134, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((65/3),1,(2,2,-1,-2,0,0,0))]⟩,
  ⟨150, 2, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(2,0,-1,0,0,0,0))]⟩,
  ⟨157, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-4225/18),1,(2,2,-1,-2,0,0,0))]⟩,
  ⟨179, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨93, 184, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨149, 185, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨171, 186, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨119, 200, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨54, 201, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨40, 202, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 189, [((-1),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨192, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨149, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,0,0,0,0,0,0))]⟩,
  ⟨171, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨129, 193, [((-1),0,(0,2,0,-2,0,0,0))]⟩,
  ⟨155, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-624/5),1,(0,-2,0,2,0,0,0))]⟩,
  ⟨177, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((194688/25),1,(0,-2,0,2,0,0,0))]⟩,
  ⟨126, 133, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨126, 135, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨133, 138, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(2,-2,0,2,0,0,0))]⟩,
  ⟨159, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((507/5),1,(2,-2,0,2,0,0,0))]⟩,
  ⟨181, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((257049/50),1,(2,-2,0,2,0,0,0))]⟩,
  ⟨128, 202, [((-1),0,(3,2,0,-2,0,0,0))]⟩,
  ⟨135, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨152, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]























































































































































































def compactBlock001Indices : List ℕ := [123, 122, 116, 114, 113, 112, 110, 109, 108, 107, 106, 105, 104, 103, 100, 99, 98, 97, 96, 95, 94, 93, 92, 90, 89, 88, 87, 86, 85, 84, 83, 82, 79, 78, 77, 70, 69, 67, 66, 65, 64, 62, 61, 56, 55, 52, 51, 50, 49, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 29, 28, 26, 25, 24, 23, 22, 21, 20, 19, 17, 16, 14, 13, 12, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock001Results : List Poly :=
  program_results% (compactBlock001Inputs) (compactBlock001Program) (compactBlock001Indices)

def node1430 : Poly := rowAt compactBlock001Results 0
def node1431 : Poly := rowAt compactBlock001Results 1
def node1441 : Poly := rowAt compactBlock001Results 2
def node1443 : Poly := rowAt compactBlock001Results 3
def node1444 : Poly := rowAt compactBlock001Results 4
def node1445 : Poly := rowAt compactBlock001Results 5
def node1456 : Poly := rowAt compactBlock001Results 6
def node1457 : Poly := rowAt compactBlock001Results 7
def node1458 : Poly := rowAt compactBlock001Results 8
def node1459 : Poly := rowAt compactBlock001Results 9
def node1460 : Poly := rowAt compactBlock001Results 10
def node1461 : Poly := rowAt compactBlock001Results 11
def node1464 : Poly := rowAt compactBlock001Results 12
def node1465 : Poly := rowAt compactBlock001Results 13
def node1470 : Poly := rowAt compactBlock001Results 14
def node1480 : Poly := rowAt compactBlock001Results 15
def node1481 : Poly := rowAt compactBlock001Results 16
def node1482 : Poly := rowAt compactBlock001Results 17
def node1483 : Poly := rowAt compactBlock001Results 18
def node1484 : Poly := rowAt compactBlock001Results 19
def node1485 : Poly := rowAt compactBlock001Results 20
def node1488 : Poly := rowAt compactBlock001Results 21
def node1489 : Poly := rowAt compactBlock001Results 22
def node1492 : Poly := rowAt compactBlock001Results 23
def node1502 : Poly := rowAt compactBlock001Results 24
def node1503 : Poly := rowAt compactBlock001Results 25
def node1504 : Poly := rowAt compactBlock001Results 26
def node1505 : Poly := rowAt compactBlock001Results 27
def node1506 : Poly := rowAt compactBlock001Results 28
def node1507 : Poly := rowAt compactBlock001Results 29
def node1510 : Poly := rowAt compactBlock001Results 30
def node1511 : Poly := rowAt compactBlock001Results 31
def node1515 : Poly := rowAt compactBlock001Results 32
def node1517 : Poly := rowAt compactBlock001Results 33
def node1518 : Poly := rowAt compactBlock001Results 34
def node1530 : Poly := rowAt compactBlock001Results 35
def node1531 : Poly := rowAt compactBlock001Results 36
def node1533 : Poly := rowAt compactBlock001Results 37
def node1534 : Poly := rowAt compactBlock001Results 38
def node1536 : Poly := rowAt compactBlock001Results 39
def node1537 : Poly := rowAt compactBlock001Results 40
def node1539 : Poly := rowAt compactBlock001Results 41
def node1540 : Poly := rowAt compactBlock001Results 42
def node1548 : Poly := rowAt compactBlock001Results 43
def node1549 : Poly := rowAt compactBlock001Results 44
def node1552 : Poly := rowAt compactBlock001Results 45
def node1553 : Poly := rowAt compactBlock001Results 46
def node1554 : Poly := rowAt compactBlock001Results 47
def node1555 : Poly := rowAt compactBlock001Results 48
def node1558 : Poly := rowAt compactBlock001Results 49
def node1559 : Poly := rowAt compactBlock001Results 50
def node1560 : Poly := rowAt compactBlock001Results 51
def node1561 : Poly := rowAt compactBlock001Results 52
def node1562 : Poly := rowAt compactBlock001Results 53
def node1567 : Poly := rowAt compactBlock001Results 54
def node1568 : Poly := rowAt compactBlock001Results 55
def node1569 : Poly := rowAt compactBlock001Results 56
def node1570 : Poly := rowAt compactBlock001Results 57
def node1571 : Poly := rowAt compactBlock001Results 58
def node1573 : Poly := rowAt compactBlock001Results 59
def node1574 : Poly := rowAt compactBlock001Results 60
def node1575 : Poly := rowAt compactBlock001Results 61
def node1576 : Poly := rowAt compactBlock001Results 62
def node1577 : Poly := rowAt compactBlock001Results 63
def node1578 : Poly := rowAt compactBlock001Results 64
def node1581 : Poly := rowAt compactBlock001Results 65
def node1582 : Poly := rowAt compactBlock001Results 66
def node1587 : Poly := rowAt compactBlock001Results 67
def node1589 : Poly := rowAt compactBlock001Results 68
def node1590 : Poly := rowAt compactBlock001Results 69
def node1591 : Poly := rowAt compactBlock001Results 70
def node1592 : Poly := rowAt compactBlock001Results 71
def node1594 : Poly := rowAt compactBlock001Results 72
def node1597 : Poly := rowAt compactBlock001Results 73
def node1598 : Poly := rowAt compactBlock001Results 74
def node1600 : Poly := rowAt compactBlock001Results 75
def node1601 : Poly := rowAt compactBlock001Results 76
def node1609 : Poly := rowAt compactBlock001Results 77
def node1610 : Poly := rowAt compactBlock001Results 78
def node1612 : Poly := rowAt compactBlock001Results 79
def node1629 : Poly := rowAt compactBlock001Results 80
def node1630 : Poly := rowAt compactBlock001Results 81
def node1631 : Poly := rowAt compactBlock001Results 82
def node1633 : Poly := rowAt compactBlock001Results 83
def node1636 : Poly := rowAt compactBlock001Results 84
def node1637 : Poly := rowAt compactBlock001Results 85
def node1638 : Poly := rowAt compactBlock001Results 86
def node1639 : Poly := rowAt compactBlock001Results 87
def node1644 : Poly := rowAt compactBlock001Results 88
def node1645 : Poly := rowAt compactBlock001Results 89
def node1646 : Poly := rowAt compactBlock001Results 90

theorem compactBlock001_certificate : outputs compactBlock001Inputs compactBlock001Program compactBlock001Indices = compactBlock001Results := by
  decide +kernel

theorem compactBlock001_derived : ∀ p ∈ compactBlock001Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock001_inputs compactBlock001Program compactBlock001Indices compactBlock001_certificate

#print axioms compactBlock001_derived


def compactBlock002Inputs : List Poly := [node0003, node0004, node0008, node0028, node0029, node0030, node0031, node0032, node0034, node0045, node0049, node0051, node0052, node0053, node0054, node0055, node0056, node0057, node0060, node0061, node0062, node0063, node0064, node0066, node0067, node0074, node0078, node0079, node0091, node0093, node0095, node0096, node0124, node0195, node0196, node0201, node0207, node0210, node0212, node0224, node0259, node0279, node0281, node0288, node0289, node0295, node0302, node0303, node0310, node0351, node0400, node0401, node0423, node0454, node0457, node0458, node0459, node0460, node0461, node0463, node0464, node0476, node0496, node0521, node0523, node0524, node0592, node0593, node0598, node0604, node0609, node0621, node0656, node0674, node0676, node0685, node0686, node0797, node0798, node0820, node0851, node0854, node0855, node0856, node0857, node0858, node0860, node0861, node0873, node0893, node0918, node0920, node0921, node0989, node0990, node0995, node1001, node1006, node1018, node1053, node1071, node1073, node1082, node1083, node1191, node1464, node1534, node1540, node1561, node1562, node1578, node1594, node1600, node1601, node1609, node1631, node1636, node1637, node1644, node1646]

theorem compactBlock002_inputs : ∀ p ∈ compactBlock002Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0003, node0004, node0008, node0028, node0029, node0030, node0031, node0032, node0034, node0045, node0049, node0051, node0052, node0053, node0054, node0055, node0056, node0057, node0060, node0061, node0062, node0063, node0064, node0066, node0067, node0074, node0078, node0079, node0091, node0093, node0095, node0096, node0124, node0195, node0196, node0201, node0207, node0210, node0212, node0224, node0259, node0279, node0281, node0288, node0289, node0295, node0302, node0303, node0310, node0351, node0400, node0401, node0423, node0454, node0457, node0458, node0459, node0460, node0461, node0463, node0464, node0476, node0496, node0521, node0523, node0524, node0592, node0593, node0598, node0604, node0609, node0621, node0656, node0674, node0676, node0685, node0686, node0797, node0798, node0820, node0851, node0854, node0855, node0856, node0857, node0858, node0860, node0861, node0873, node0893, node0918, node0920, node0921, node0989, node0990, node0995, node1001, node1006, node1018, node1053, node1071, node1073, node1082, node1083, node1191, node1464, node1534, node1540, node1561, node1562, node1578, node1594, node1600, node1601, node1609, node1631, node1636, node1637, node1644, node1646], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 3 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 4 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 8 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 28 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 29 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 30 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 31 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 32 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 34 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 45 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 49 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 51 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 52 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 53 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 54 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 55 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 56 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 57 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 60 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 61 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 62 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 63 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 64 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 66 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 67 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 74 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 78 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 79 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 91 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 93 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 95 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 96 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 124 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 195 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 196 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 201 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 207 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 210 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 212 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 224 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 259 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 279 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 281 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 288 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 289 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 295 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 302 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 303 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 310 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 351 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 400 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 401 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 423 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 454 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 457 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 458 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 459 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 460 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 461 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 463 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 464 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 476 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 496 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 521 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 523 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 524 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 592 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 593 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 598 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 604 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 609 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 621 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 656 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 674 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 676 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 685 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 686 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 797 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 798 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 820 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 851 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 854 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 855 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 856 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 857 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 858 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 860 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 861 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 873 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 893 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 918 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 920 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 921 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 989 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 990 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 995 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1001 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1006 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1018 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1053 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1071 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1073 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1082 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1083 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 90)
  exact nil_derived _ _

def compactBlock002Program : List Instruction := [
  ⟨52, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨80, 119, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨2, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨46, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨117, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-390),1,(0,0,0,-2,0,0,0))]⟩,
  ⟨81, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨84, 10, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨110, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨128, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨43, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨59, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 19, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨127, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨79, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((1820/3),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨107, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((1656200/9),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨60, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 27, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,2,0,2,0,0,0))]⟩,
  ⟨85, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((676/15),1,(-3,2,0,2,0,0,0))]⟩,
  ⟨113, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((228488/225),1,(-3,2,0,2,0,0,0))]⟩,
  ⟨126, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨130, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨9, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨139, 35, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(2,0,0,-2,0,0,0))]⟩,
  ⟨74, 36, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨90, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-455),1,(2,0,0,-2,0,0,0))]⟩,
  ⟨118, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((207025/2),1,(2,0,0,-2,0,0,0))]⟩,
  ⟨68, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨71, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨93, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨104, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨106, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨123, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨134, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨136, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨75, 50, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨79, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨151, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨35, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨111, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((-390),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨116, 55, [(1,0,(0,0,0,0,0,0,0)),
  ((-30),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨140, 56, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨145, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨35, 59, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨47, 61, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨73, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨31, 63, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨9, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨159, 65, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨102, 66, [(1,0,(0,0,0,0,0,0,0)),
  ((-780),1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨128, 67, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨159, 68, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨132, 69, [(1,0,(0,0,0,0,0,0,0)),
  (304200,1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨158, 70, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨163, 71, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨167, 72, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨46, 74, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨76, 163, [((-1),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨88, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨114, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨142, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨81, 167, [((-1),0,(-1,0,0,0,0,0,0))]⟩,
  ⟨93, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨43, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨16, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨16, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨122, 4, [(1,0,(0,0,0,0,0,0,0)),
  (13,1,(1,0,0,0,0,0,0))]⟩,
  ⟨15, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨151, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((169/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨14, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨14, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨92, 177, [((-1),0,(-3,-2,0,2,0,0,0))]⟩,
  ⟨129, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((65/6),1,(3,2,0,-2,0,0,0))]⟩,
  ⟨157, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/72),1,(3,2,0,-2,0,0,0))]⟩,
  ⟨96, 180, [((-1),0,(1,-2,0,0,0,0,0))]⟩,
  ⟨107, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨113, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨38, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨136, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((26/3),1,(-1,2,0,0,0,0,0))]⟩,
  ⟨149, 4, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨165, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((338/9),1,(-1,2,0,0,0,0,0))]⟩,
  ⟨178, 6, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨105, 188, [((-1),0,(-1,2,0,-2,0,0,0))]⟩,
  ⟨142, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((39/5),1,(1,-2,0,2,0,0,0))]⟩,
  ⟨170, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/50),1,(1,-2,0,2,0,0,0))]⟩,
  ⟨109, 191, [((-1),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨119, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨147, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((13/2),1,(3,0,0,0,0,0,0))]⟩,
  ⟨175, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((169/8),1,(3,0,0,0,0,0,0))]⟩,
  ⟨114, 195, [((-1),0,(-1,-2,0,0,0,0,0))]⟩,
  ⟨129, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨70, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨154, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(1,2,0,0,0,0,0))]⟩,
  ⟨43, 4, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨183, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((169/18),1,(1,2,0,0,0,0,0))]⟩,
  ⟨42, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨123, 203, [((-1),0,(-3,2,0,-2,0,0,0))]⟩,
  ⟨145, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((39/10),1,(3,-2,0,2,0,0,0))]⟩,
  ⟨189, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/200),1,(3,-2,0,2,0,0,0))]⟩,
  ⟨135, 142, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,2,0,2,0,0,0))]⟩,
  ⟨167, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/15),1,(1,2,0,2,0,0,0))]⟩,
  ⟨195, 144, [(1,0,(0,0,0,0,0,0,0)),
  ((169/450),1,(1,2,0,2,0,0,0))]⟩,
  ⟨140, 223, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,0,0,-2,0,0,0))]⟩,
  ⟨76, 224, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨85, 225, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 226, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨177, 227, [(1,0,(0,0,0,0,0,0,0)),
  ((-195),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨104, 228, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨206, 229, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨104, 230, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨10, 218, [((-1),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨140, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨143, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,-2,1,0,0,0,0))]⟩,
  ⟨178, 2, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(2,-2,1,0,0,0,0))]⟩,
  ⟨13, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/15),1,(3,0,0,0,0,0,0))]⟩,
  ⟨190, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-2535),1,(2,-2,0,-2,0,0,0))]⟩,
  ⟨208, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(2,-2,1,0,0,0,0))]⟩,
  ⟨15, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((169/450),1,(3,0,0,0,0,0,0))]⟩,
  ⟨220, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((6426225/2),1,(2,-2,0,-2,0,0,0))]⟩,
  ⟨169, 120, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨171, 77, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 127, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,2,0,2,0,0,0))]⟩,
  ⟨195, 128, [(1,0,(0,0,0,0,0,0,0)),
  ((52/15),1,(0,2,0,2,0,0,0))]⟩,
  ⟨223, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/225),1,(0,2,0,2,0,0,0))]⟩
]





















































































































































































def compactBlock002Indices : List ℕ := [127, 126, 122, 120, 115, 113, 112, 110, 109, 108, 107, 103, 102, 101, 100, 99, 98, 96, 95, 94, 93, 92, 91, 90, 89, 86, 85, 84, 83, 82, 80, 76, 73, 69, 67, 66, 65, 63, 62, 61, 60, 59, 58, 57, 56, 55, 53, 52, 50, 49, 48, 47, 46, 45, 44, 42, 41, 39, 38, 37, 35, 34, 32, 31, 30, 29, 27, 26, 25, 21, 20, 19, 18, 17, 16, 15, 14, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock002Results : List Poly :=
  program_results% (compactBlock002Inputs) (compactBlock002Program) (compactBlock002Indices)

def node1647 : Poly := rowAt compactBlock002Results 0
def node1648 : Poly := rowAt compactBlock002Results 1
def node1653 : Poly := rowAt compactBlock002Results 2
def node1655 : Poly := rowAt compactBlock002Results 3
def node1661 : Poly := rowAt compactBlock002Results 4
def node1668 : Poly := rowAt compactBlock002Results 5
def node1670 : Poly := rowAt compactBlock002Results 6
def node1673 : Poly := rowAt compactBlock002Results 7
def node1677 : Poly := rowAt compactBlock002Results 8
def node1679 : Poly := rowAt compactBlock002Results 9
def node1680 : Poly := rowAt compactBlock002Results 10
def node1687 : Poly := rowAt compactBlock002Results 11
def node1689 : Poly := rowAt compactBlock002Results 12
def node1692 : Poly := rowAt compactBlock002Results 13
def node1693 : Poly := rowAt compactBlock002Results 14
def node1695 : Poly := rowAt compactBlock002Results 15
def node1697 : Poly := rowAt compactBlock002Results 16
def node1702 : Poly := rowAt compactBlock002Results 17
def node1703 : Poly := rowAt compactBlock002Results 18
def node1704 : Poly := rowAt compactBlock002Results 19
def node1705 : Poly := rowAt compactBlock002Results 20
def node1706 : Poly := rowAt compactBlock002Results 21
def node1707 : Poly := rowAt compactBlock002Results 22
def node1709 : Poly := rowAt compactBlock002Results 23
def node1710 : Poly := rowAt compactBlock002Results 24
def node1717 : Poly := rowAt compactBlock002Results 25
def node1718 : Poly := rowAt compactBlock002Results 26
def node1721 : Poly := rowAt compactBlock002Results 27
def node1722 : Poly := rowAt compactBlock002Results 28
def node1725 : Poly := rowAt compactBlock002Results 29
def node1727 : Poly := rowAt compactBlock002Results 30
def node1737 : Poly := rowAt compactBlock002Results 31
def node1741 : Poly := rowAt compactBlock002Results 32
def node1745 : Poly := rowAt compactBlock002Results 33
def node1747 : Poly := rowAt compactBlock002Results 34
def node1752 : Poly := rowAt compactBlock002Results 35
def node1753 : Poly := rowAt compactBlock002Results 36
def node1765 : Poly := rowAt compactBlock002Results 37
def node1766 : Poly := rowAt compactBlock002Results 38
def node1767 : Poly := rowAt compactBlock002Results 39
def node1768 : Poly := rowAt compactBlock002Results 40
def node1775 : Poly := rowAt compactBlock002Results 41
def node1776 : Poly := rowAt compactBlock002Results 42
def node1778 : Poly := rowAt compactBlock002Results 43
def node1779 : Poly := rowAt compactBlock002Results 44
def node1780 : Poly := rowAt compactBlock002Results 45
def node1783 : Poly := rowAt compactBlock002Results 46
def node1784 : Poly := rowAt compactBlock002Results 47
def node1786 : Poly := rowAt compactBlock002Results 48
def node1787 : Poly := rowAt compactBlock002Results 49
def node1788 : Poly := rowAt compactBlock002Results 50
def node1791 : Poly := rowAt compactBlock002Results 51
def node1792 : Poly := rowAt compactBlock002Results 52
def node1793 : Poly := rowAt compactBlock002Results 53
def node1794 : Poly := rowAt compactBlock002Results 54
def node1797 : Poly := rowAt compactBlock002Results 55
def node1798 : Poly := rowAt compactBlock002Results 56
def node1800 : Poly := rowAt compactBlock002Results 57
def node1802 : Poly := rowAt compactBlock002Results 58
def node1803 : Poly := rowAt compactBlock002Results 59
def node1808 : Poly := rowAt compactBlock002Results 60
def node1809 : Poly := rowAt compactBlock002Results 61
def node1815 : Poly := rowAt compactBlock002Results 62
def node1816 : Poly := rowAt compactBlock002Results 63
def node1818 : Poly := rowAt compactBlock002Results 64
def node1819 : Poly := rowAt compactBlock002Results 65
def node1822 : Poly := rowAt compactBlock002Results 66
def node1825 : Poly := rowAt compactBlock002Results 67
def node1826 : Poly := rowAt compactBlock002Results 68
def node1839 : Poly := rowAt compactBlock002Results 69
def node1840 : Poly := rowAt compactBlock002Results 70
def node1841 : Poly := rowAt compactBlock002Results 71
def node1842 : Poly := rowAt compactBlock002Results 72
def node1844 : Poly := rowAt compactBlock002Results 73
def node1845 : Poly := rowAt compactBlock002Results 74
def node1846 : Poly := rowAt compactBlock002Results 75
def node1847 : Poly := rowAt compactBlock002Results 76
def node1852 : Poly := rowAt compactBlock002Results 77
def node1853 : Poly := rowAt compactBlock002Results 78
def node1855 : Poly := rowAt compactBlock002Results 79
def node1856 : Poly := rowAt compactBlock002Results 80
def node1857 : Poly := rowAt compactBlock002Results 81
def node1860 : Poly := rowAt compactBlock002Results 82
def node1861 : Poly := rowAt compactBlock002Results 83
def node1862 : Poly := rowAt compactBlock002Results 84
def node1864 : Poly := rowAt compactBlock002Results 85
def node1865 : Poly := rowAt compactBlock002Results 86
def node1867 : Poly := rowAt compactBlock002Results 87
def node1869 : Poly := rowAt compactBlock002Results 88
def node1870 : Poly := rowAt compactBlock002Results 89

theorem compactBlock002_certificate : outputs compactBlock002Inputs compactBlock002Program compactBlock002Indices = compactBlock002Results := by
  decide +kernel

theorem compactBlock002_derived : ∀ p ∈ compactBlock002Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock002_inputs compactBlock002Program compactBlock002Indices compactBlock002_certificate

#print axioms compactBlock002_derived


def compactBlock003Inputs : List Poly := [node0080, node0081, node0082, node0083, node0084, node0085, node0086, node0087, node0088, node0089, node0100, node0119, node0121, node0128, node0142, node0146, node0219, node0237, node0248, node0250, node0252, node0263, node0267, node0268, node0296, node0350, node0395, node0396, node0442, node0449, node0475, node0477, node0478, node0480, node0481, node0482, node0485, node0486, node0497, node0516, node0518, node0645, node0647, node0660, node0839, node0846, node0872, node0874, node0875, node0877, node0878, node0879, node0882, node0883, node0894, node0913, node0915, node1042, node1044, node1057, node1191, node1196, node1357, node1358, node1365, node1366, node1390, node1391, node1398, node1399, node1422, node1423, node1430, node1431, node1443, node1456, node1465, node1480, node1488, node1489, node1502, node1510, node1511, node1587, node1590, node1592, node1677, node1679, node1680, node1695, node1697, node1702, node1703, node1704, node1705, node1706, node1707, node1727, node1766, node1767, node1768, node1780, node1788, node1809, node1822, node1825, node1826, node1840, node1841, node1845, node1847, node1853]

theorem compactBlock003_inputs : ∀ p ∈ compactBlock003Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0080, node0081, node0082, node0083, node0084, node0085, node0086, node0087, node0088, node0089, node0100, node0119, node0121, node0128, node0142, node0146, node0219, node0237, node0248, node0250, node0252, node0263, node0267, node0268, node0296, node0350, node0395, node0396, node0442, node0449, node0475, node0477, node0478, node0480, node0481, node0482, node0485, node0486, node0497, node0516, node0518, node0645, node0647, node0660, node0839, node0846, node0872, node0874, node0875, node0877, node0878, node0879, node0882, node0883, node0894, node0913, node0915, node1042, node1044, node1057, node1191, node1196, node1357, node1358, node1365, node1366, node1390, node1391, node1398, node1399, node1422, node1423, node1430, node1431, node1443, node1456, node1465, node1480, node1488, node1489, node1502, node1510, node1511, node1587, node1590, node1592, node1677, node1679, node1680, node1695, node1697, node1702, node1703, node1704, node1705, node1706, node1707, node1727, node1766, node1767, node1768, node1780, node1788, node1809, node1822, node1825, node1826, node1840, node1841, node1845, node1847, node1853], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 80 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 81 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 82 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 83 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 84 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 85 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 86 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 87 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 88 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 89 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 100 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 119 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 121 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 128 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 142 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 146 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 219 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 237 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 248 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 250 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 252 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 263 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 267 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 268 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 296 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 350 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 395 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 396 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 442 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 449 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 475 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 477 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 478 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 480 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 481 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 482 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 485 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 486 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 497 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 516 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 518 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 645 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 647 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 660 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 839 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 846 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 872 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 874 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 875 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 877 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 878 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 879 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 882 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 883 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 894 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 913 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 915 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1042 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1044 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1057 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 78)
  exact nil_derived _ _

def compactBlock003Program : List Instruction := [
  ⟨86, 60, [((-1),0,(2,0,0,0,0,0,0))]⟩,
  ⟨108, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨102, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨31, 2, [(1,0,(0,0,0,0,0,0,0)),
  (195,1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨91, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((676/15),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨114, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨50, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/2),1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨95, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((228488/225),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨118, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨110, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨107, 70, [(1,0,(-2,0,1,-2,0,0,0))]⟩,
  ⟨115, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨38, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨43, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((13/5),1,(2,0,-1,2,0,0,0))]⟩,
  ⟨60, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/50),1,(2,0,-1,2,0,0,0))]⟩,
  ⟨90, 126, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨37, 127, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨40, 128, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨127, 130, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨47, 131, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,-2,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨98, 132, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨65, 133, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/3),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨102, 134, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨104, 135, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨84, 136, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/9),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨108, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨27, 87, [(1,0,(0,-2,-1,2,0,0,0))]⟩,
  ⟨42, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨45, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨133, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((10/3),1,(0,2,1,-2,0,0,0))]⟩,
  ⟨80, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-50/9),1,(0,2,1,-2,0,0,0))]⟩,
  ⟨35, 94, [(1,0,(2,-2,1,-2,0,0,0))]⟩,
  ⟨138, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨60, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨16, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨70, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((52/15),1,(-2,2,-1,2,0,0,0))]⟩,
  ⟨87, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/225),1,(-2,2,-1,2,0,0,0))]⟩,
  ⟨50, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨52, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,0,-1,-2,0,0,0))]⟩,
  ⟨55, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨64, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨84, 48, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨86, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-65),1,(2,0,-1,-2,0,0,0))]⟩,
  ⟨89, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨133, 51, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(2,0,-1,0,0,0,0))]⟩,
  ⟨104, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨106, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-4225/2),1,(2,0,-1,-2,0,0,0))]⟩,
  ⟨109, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨138, 55, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨57, 114, [(1,0,(-2,-2,1,0,0,0,0))]⟩,
  ⟨11, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨89, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(2,2,-1,0,0,0,0))]⟩,
  ⟨8, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨107, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/18),1,(2,2,-1,0,0,0,0))]⟩,
  ⟨6, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨64, 120, [(1,0,(-2,0,-1,2,0,0,0))]⟩,
  ⟨76, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨96, 1, [(1,0,(0,0,0,0,0,0,0)),
  (5,1,(2,0,1,-2,0,0,0))]⟩,
  ⟨113, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/2),1,(2,0,1,-2,0,0,0))]⟩,
  ⟨69, 124, [(1,0,(0,0,1,-2,0,0,0))]⟩,
  ⟨84, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨155, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨89, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨104, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((26/5),1,(0,0,-1,2,0,0,0))]⟩,
  ⟨112, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-78/5),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨163, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨123, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-338/25),1,(0,0,-1,2,0,0,0))]⟩,
  ⟨131, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨169, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨92, 81, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨138, 82, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨10, 83, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨143, 84, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨169, 85, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨178, 86, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨12, 87, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨51, 88, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨71, 89, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-3,2,0,-2,0,0,0))]⟩,
  ⟨158, 90, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,-2,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨114, 91, [(1,0,(0,0,0,0,0,0,0)),
  ((130/3),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨191, 92, [(1,0,(0,0,0,0,0,0,0)),
  ((39/10),1,(0,0,0,0,0,0,0))]⟩,
  ⟨178, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-3,0,-1,0,0,0,0))]⟩,
  ⟨154, 94, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨17, 95, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨159, 96, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨184, 97, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-3,2,-1,0,0,0,0))]⟩,
  ⟨170, 98, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨138, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((8450/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨200, 100, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/200),1,(0,0,0,0,0,0,0))]⟩,
  ⟨189, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-3,0,-1,0,0,0,0))]⟩,
  ⟨166, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨22, 103, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨171, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨195, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-3,2,-1,0,0,0,0))]⟩,
  ⟨181, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨162, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨18, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 110, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨91, 111, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨113, 165, [(1,0,(-2,2,1,-2,0,0,0))]⟩,
  ⟨3, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨143, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((39/5),1,(2,-2,-1,2,0,0,0))]⟩,
  ⟨160, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/50),1,(2,-2,-1,2,0,0,0))]⟩,
  ⟨118, 169, [(1,0,(0,-2,1,0,0,0,0))]⟩,
  ⟨122, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,2,-1,-2,0,0,0))]⟩,
  ⟨35, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨175, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨96, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨178, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨96, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨31, 6, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,-1,0,1,0))]⟩,
  ⟨154, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((26/3),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨158, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-130/3),1,(0,2,-1,-2,0,0,0))]⟩,
  ⟨186, 9, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨97, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/3),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨189, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨98, 12, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(0,0,-1,0,0,0,0))]⟩,
  ⟨176, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-338/9),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨180, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-8450/9),1,(0,2,-1,-2,0,0,0))]⟩,
  ⟨196, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,0,-1,0,0,0,0))]⟩,
  ⟨100, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/9),1,(0,2,-1,0,0,0,0))]⟩,
  ⟨199, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(0,0,-1,0,0,0,0))]⟩
]







































































































































































































def compactBlock003Indices : List ℕ := [125, 124, 123, 122, 121, 120, 119, 118, 114, 113, 112, 110, 108, 106, 103, 101, 99, 98, 96, 95, 94, 92, 91, 90, 89, 88, 87, 86, 85, 83, 82, 81, 80, 78, 77, 76, 74, 72, 71, 70, 69, 68, 66, 65, 64, 62, 60, 58, 57, 55, 54, 51, 50, 49, 48, 47, 46, 45, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 24, 23, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock003Results : List Poly :=
  program_results% (compactBlock003Inputs) (compactBlock003Program) (compactBlock003Indices)

def node1880 : Poly := rowAt compactBlock003Results 0
def node1885 : Poly := rowAt compactBlock003Results 1
def node1886 : Poly := rowAt compactBlock003Results 2
def node1887 : Poly := rowAt compactBlock003Results 3
def node1889 : Poly := rowAt compactBlock003Results 4
def node1890 : Poly := rowAt compactBlock003Results 5
def node1891 : Poly := rowAt compactBlock003Results 6
def node1892 : Poly := rowAt compactBlock003Results 7
def node1903 : Poly := rowAt compactBlock003Results 8
def node1904 : Poly := rowAt compactBlock003Results 9
def node1906 : Poly := rowAt compactBlock003Results 10
def node1908 : Poly := rowAt compactBlock003Results 11
def node1911 : Poly := rowAt compactBlock003Results 12
def node1915 : Poly := rowAt compactBlock003Results 13
def node1920 : Poly := rowAt compactBlock003Results 14
def node1923 : Poly := rowAt compactBlock003Results 15
def node1925 : Poly := rowAt compactBlock003Results 16
def node1926 : Poly := rowAt compactBlock003Results 17
def node1928 : Poly := rowAt compactBlock003Results 18
def node1933 : Poly := rowAt compactBlock003Results 19
def node1935 : Poly := rowAt compactBlock003Results 20
def node1938 : Poly := rowAt compactBlock003Results 21
def node1939 : Poly := rowAt compactBlock003Results 22
def node1942 : Poly := rowAt compactBlock003Results 23
def node1943 : Poly := rowAt compactBlock003Results 24
def node1944 : Poly := rowAt compactBlock003Results 25
def node1945 : Poly := rowAt compactBlock003Results 26
def node1947 : Poly := rowAt compactBlock003Results 27
def node1948 : Poly := rowAt compactBlock003Results 28
def node1950 : Poly := rowAt compactBlock003Results 29
def node1951 : Poly := rowAt compactBlock003Results 30
def node1955 : Poly := rowAt compactBlock003Results 31
def node1957 : Poly := rowAt compactBlock003Results 32
def node1959 : Poly := rowAt compactBlock003Results 33
def node1960 : Poly := rowAt compactBlock003Results 34
def node1962 : Poly := rowAt compactBlock003Results 35
def node1964 : Poly := rowAt compactBlock003Results 36
def node1966 : Poly := rowAt compactBlock003Results 37
def node1968 : Poly := rowAt compactBlock003Results 38
def node1969 : Poly := rowAt compactBlock003Results 39
def node1970 : Poly := rowAt compactBlock003Results 40
def node1971 : Poly := rowAt compactBlock003Results 41
def node1973 : Poly := rowAt compactBlock003Results 42
def node1978 : Poly := rowAt compactBlock003Results 43
def node1979 : Poly := rowAt compactBlock003Results 44
def node1981 : Poly := rowAt compactBlock003Results 45
def node1983 : Poly := rowAt compactBlock003Results 46
def node1989 : Poly := rowAt compactBlock003Results 47
def node1990 : Poly := rowAt compactBlock003Results 48
def node1993 : Poly := rowAt compactBlock003Results 49
def node1994 : Poly := rowAt compactBlock003Results 50
def node2002 : Poly := rowAt compactBlock003Results 51
def node2003 : Poly := rowAt compactBlock003Results 52
def node2007 : Poly := rowAt compactBlock003Results 53
def node2009 : Poly := rowAt compactBlock003Results 54
def node2011 : Poly := rowAt compactBlock003Results 55
def node2012 : Poly := rowAt compactBlock003Results 56
def node2013 : Poly := rowAt compactBlock003Results 57
def node2024 : Poly := rowAt compactBlock003Results 58
def node2025 : Poly := rowAt compactBlock003Results 59
def node2026 : Poly := rowAt compactBlock003Results 60
def node2030 : Poly := rowAt compactBlock003Results 61
def node2031 : Poly := rowAt compactBlock003Results 62
def node2034 : Poly := rowAt compactBlock003Results 63
def node2035 : Poly := rowAt compactBlock003Results 64
def node2037 : Poly := rowAt compactBlock003Results 65
def node2039 : Poly := rowAt compactBlock003Results 66
def node2040 : Poly := rowAt compactBlock003Results 67
def node2041 : Poly := rowAt compactBlock003Results 68
def node2045 : Poly := rowAt compactBlock003Results 69
def node2046 : Poly := rowAt compactBlock003Results 70
def node2049 : Poly := rowAt compactBlock003Results 71
def node2050 : Poly := rowAt compactBlock003Results 72
def node2052 : Poly := rowAt compactBlock003Results 73
def node2054 : Poly := rowAt compactBlock003Results 74
def node2056 : Poly := rowAt compactBlock003Results 75
def node2058 : Poly := rowAt compactBlock003Results 76
def node2061 : Poly := rowAt compactBlock003Results 77
def node2065 : Poly := rowAt compactBlock003Results 78
def node2066 : Poly := rowAt compactBlock003Results 79
def node2067 : Poly := rowAt compactBlock003Results 80
def node2068 : Poly := rowAt compactBlock003Results 81
def node2069 : Poly := rowAt compactBlock003Results 82
def node2070 : Poly := rowAt compactBlock003Results 83
def node2071 : Poly := rowAt compactBlock003Results 84
def node2073 : Poly := rowAt compactBlock003Results 85
def node2075 : Poly := rowAt compactBlock003Results 86
def node2077 : Poly := rowAt compactBlock003Results 87
def node2078 : Poly := rowAt compactBlock003Results 88
def node2079 : Poly := rowAt compactBlock003Results 89
def node2080 : Poly := rowAt compactBlock003Results 90
def node2081 : Poly := rowAt compactBlock003Results 91
def node2083 : Poly := rowAt compactBlock003Results 92
def node2085 : Poly := rowAt compactBlock003Results 93
def node2086 : Poly := rowAt compactBlock003Results 94
def node2087 : Poly := rowAt compactBlock003Results 95
def node2088 : Poly := rowAt compactBlock003Results 96
def node2089 : Poly := rowAt compactBlock003Results 97
def node2091 : Poly := rowAt compactBlock003Results 98

theorem compactBlock003_certificate : outputs compactBlock003Inputs compactBlock003Program compactBlock003Indices = compactBlock003Results := by
  decide +kernel

theorem compactBlock003_derived : ∀ p ∈ compactBlock003Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock003_inputs compactBlock003Program compactBlock003Indices compactBlock003_certificate

#print axioms compactBlock003_derived


def compactBlock004Inputs : List Poly := [node0090, node0092, node0094, node0118, node0122, node0206, node0214, node0216, node0217, node0249, node0251, node0260, node0261, node0280, node0388, node0431, node0488, node0490, node0492, node0493, node0515, node0519, node0520, node0603, node0607, node0611, node0613, node0614, node0616, node0629, node0646, node0648, node0657, node0675, node0828, node0885, node0887, node0889, node0890, node0912, node0916, node0917, node0955, node1000, node1004, node1008, node1010, node1011, node1013, node1026, node1043, node1045, node1054, node1072, node1191, node1284, node1292, node1457, node1481, node1503, node1515, node1517, node1518, node1560, node1570, node1571, node1576, node1577, node1597, node1598, node1629, node1630, node1633, node1673, node1709, node1747, node1765, node1786, node1800, node1808, node1816, node1819, node1842, node1864, node1865, node1880, node1892, node1908, node1911, node1923, node1926, node1928, node1938, node1939, node1942, node1945, node1947, node1950, node1983, node2009, node2011, node2012, node2013, node2037, node2052, node2058, node2067, node2068, node2073]

theorem compactBlock004_inputs : ∀ p ∈ compactBlock004Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0090, node0092, node0094, node0118, node0122, node0206, node0214, node0216, node0217, node0249, node0251, node0260, node0261, node0280, node0388, node0431, node0488, node0490, node0492, node0493, node0515, node0519, node0520, node0603, node0607, node0611, node0613, node0614, node0616, node0629, node0646, node0648, node0657, node0675, node0828, node0885, node0887, node0889, node0890, node0912, node0916, node0917, node0955, node1000, node1004, node1008, node1010, node1011, node1013, node1026, node1043, node1045, node1054, node1072, node1191, node1284, node1292, node1457, node1481, node1503, node1515, node1517, node1518, node1560, node1570, node1571, node1576, node1577, node1597, node1598, node1629, node1630, node1633, node1673, node1709, node1747, node1765, node1786, node1800, node1808, node1816, node1819, node1842, node1864, node1865, node1880, node1892, node1908, node1911, node1923, node1926, node1928, node1938, node1939, node1942, node1945, node1947, node1950, node1983, node2009, node2011, node2012, node2013, node2037, node2052, node2058, node2067, node2068, node2073], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 90 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 92 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 94 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 118 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 122 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 206 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 214 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 216 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 217 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 249 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 251 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 260 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 261 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 280 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 388 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 431 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 488 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 490 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 492 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 493 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 515 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 519 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 520 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 603 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 607 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 611 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 613 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 614 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 616 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 629 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 646 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 648 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 657 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 675 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 828 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 885 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 887 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 889 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 890 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 912 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 916 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 917 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 955 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1000 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1004 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1008 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1010 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1011 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1013 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1026 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1043 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1045 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1054 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1072 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 85)
  exact nil_derived _ _

def compactBlock004Program : List Instruction := [
  ⟨89, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨11, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨13, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨101, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨96, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨36, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((78/5),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨38, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨58, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042/25),1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨60, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨84, 63, [(1,0,(2,0,1,-2,0,0,0))]⟩,
  ⟨65, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨110, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨29, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((52/5),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨49, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨24, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨46, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨67, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨94, 72, [(1,0,(-2,0,1,0,0,0,0))]⟩,
  ⟨23, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨4, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨118, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨82, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨18, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨97, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨130, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,-2,0,0,0)),
  (1,1,(0,0,0,-1,0,1,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-195/2),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨44, 8, [(1,0,(0,0,0,0,0,0,0)),
  (13,1,(2,0,-1,0,0,0,0))]⟩,
  ⟨49, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨12, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨91, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨65, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/8),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨68, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/2),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨73, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(2,-2,-1,0,0,0,0))]⟩,
  ⟨76, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-38025/8),1,(3,-2,-1,-2,0,0,0))]⟩,
  ⟨17, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(3,0,-1,0,0,0,0))]⟩,
  ⟨98, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(2,0,-1,0,0,0,0))]⟩,
  ⟨138, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨131, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨116, 93, [(1,0,(0,2,1,-2,0,0,0))]⟩,
  ⟨52, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨37, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨55, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((78/5),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨112, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨82, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨115, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨125, 101, [(1,0,(2,-2,1,0,0,0,0))]⟩,
  ⟨51, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-2,2,-1,-2,0,0,0))]⟩,
  ⟨54, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨107, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨138, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨152, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨147, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,-1,0,1,0))]⟩,
  ⟨73, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((52/3),1,(-2,2,-1,0,0,0,0))]⟩,
  ⟨75, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-260/3),1,(-2,2,-1,-2,0,0,0))]⟩,
  ⟨79, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((260/3),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨115, 9, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(1,0,-1,0,0,0,0))]⟩,
  ⟨161, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨97, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/9),1,(-2,2,-1,0,0,0,0))]⟩,
  ⟨99, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-33800/9),1,(-2,2,-1,-2,0,0,0))]⟩,
  ⟨104, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((33800/9),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨121, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,0,-1,0,0,0,0))]⟩,
  ⟨167, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,0,-1,0,0,0,0))]⟩,
  ⟨152, 159, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨147, 160, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨150, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 163, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨75, 175, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 49, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨141, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-624/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨143, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((194688/25),1,(0,0,0,0,0,0,0))]⟩,
  ⟨145, 127, [(1,0,(2,2,1,-2,0,0,0))]⟩,
  ⟨71, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨63, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨52, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨64, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨100, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨72, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨113, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨122, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,-2,-1,2,0,0,0))]⟩,
  ⟨73, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨136, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨163, 138, [((-1),0,(1,0,0,-2,0,0,0))]⟩,
  ⟨109, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-78/5),1,(-1,0,0,2,0,0,0))]⟩,
  ⟨130, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((3042/25),1,(-1,0,0,2,0,0,0))]⟩,
  ⟨170, 161, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨20, 142, [((-1),0,(1,0,0,2,0,0,0))]⟩,
  ⟨197, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨153, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨177, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨149, 4, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨119, 5, [(1,0,(0,0,0,0,0,0,0)),
  (390,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨159, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨161, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨142, 8, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨164, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨166, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨186, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨32, 155, [((-1),0,(-3,0,0,2,0,0,0))]⟩,
  ⟨27, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(2,-2,0,0,0,0,0))]⟩,
  ⟨27, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(2,0,1,-2,0,0,0))]⟩,
  ⟨27, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(2,0,1,-2,0,0,0))]⟩,
  ⟨27, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,-1,1,-2,1,0,0))]⟩,
  ⟨27, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨133, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((195/2),1,(3,0,0,-2,0,0,0))]⟩,
  ⟨137, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-624),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨29, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨29, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨29, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨158, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/8),1,(3,0,0,-2,0,0,0))]⟩,
  ⟨162, 11, [(1,0,(0,0,0,0,0,0,0)),
  (194688,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨31, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨31, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(0,0,0,0,0,0,0))]⟩,
  ⟨46, 170, [((-1),0,(1,0,0,0,0,0,0))]⟩,
  ⟨12, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨220, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨210, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨148, 4, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨202, 5, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨170, 6, [(1,0,(0,0,0,0,0,0,0)),
  (3042,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨205, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨215, 179, [((-1),0,(-3,0,0,0,0,0,0))]⟩,
  ⟨154, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(3,0,0,0,0,0,0))]⟩,
  ⟨175, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(3,0,0,0,0,0,0))]⟩
]

















































































































































































def compactBlock004Indices : List ℕ := [127, 126, 122, 120, 117, 114, 113, 107, 106, 105, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 87, 86, 85, 84, 83, 82, 81, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 61, 57, 56, 55, 42, 41, 40, 38, 37, 36, 35, 33, 32, 31, 30, 29, 28, 27, 25, 24, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 10, 9, 8, 7, 6, 5, 4, 3, 1, 0]
def compactBlock004Results : List Poly :=
  program_results% (compactBlock004Inputs) (compactBlock004Program) (compactBlock004Indices)

def node2093 : Poly := rowAt compactBlock004Results 0
def node2094 : Poly := rowAt compactBlock004Results 1
def node2104 : Poly := rowAt compactBlock004Results 2
def node2107 : Poly := rowAt compactBlock004Results 3
def node2111 : Poly := rowAt compactBlock004Results 4
def node2119 : Poly := rowAt compactBlock004Results 5
def node2121 : Poly := rowAt compactBlock004Results 6
def node2133 : Poly := rowAt compactBlock004Results 7
def node2134 : Poly := rowAt compactBlock004Results 8
def node2135 : Poly := rowAt compactBlock004Results 9
def node2137 : Poly := rowAt compactBlock004Results 10
def node2143 : Poly := rowAt compactBlock004Results 11
def node2144 : Poly := rowAt compactBlock004Results 12
def node2145 : Poly := rowAt compactBlock004Results 13
def node2148 : Poly := rowAt compactBlock004Results 14
def node2150 : Poly := rowAt compactBlock004Results 15
def node2151 : Poly := rowAt compactBlock004Results 16
def node2152 : Poly := rowAt compactBlock004Results 17
def node2153 : Poly := rowAt compactBlock004Results 18
def node2156 : Poly := rowAt compactBlock004Results 19
def node2157 : Poly := rowAt compactBlock004Results 20
def node2158 : Poly := rowAt compactBlock004Results 21
def node2159 : Poly := rowAt compactBlock004Results 22
def node2160 : Poly := rowAt compactBlock004Results 23
def node2161 : Poly := rowAt compactBlock004Results 24
def node2166 : Poly := rowAt compactBlock004Results 25
def node2167 : Poly := rowAt compactBlock004Results 26
def node2168 : Poly := rowAt compactBlock004Results 27
def node2175 : Poly := rowAt compactBlock004Results 28
def node2176 : Poly := rowAt compactBlock004Results 29
def node2179 : Poly := rowAt compactBlock004Results 30
def node2180 : Poly := rowAt compactBlock004Results 31
def node2185 : Poly := rowAt compactBlock004Results 32
def node2186 : Poly := rowAt compactBlock004Results 33
def node2189 : Poly := rowAt compactBlock004Results 34
def node2191 : Poly := rowAt compactBlock004Results 35
def node2195 : Poly := rowAt compactBlock004Results 36
def node2196 : Poly := rowAt compactBlock004Results 37
def node2197 : Poly := rowAt compactBlock004Results 38
def node2198 : Poly := rowAt compactBlock004Results 39
def node2199 : Poly := rowAt compactBlock004Results 40
def node2202 : Poly := rowAt compactBlock004Results 41
def node2204 : Poly := rowAt compactBlock004Results 42
def node2205 : Poly := rowAt compactBlock004Results 43
def node2206 : Poly := rowAt compactBlock004Results 44
def node2207 : Poly := rowAt compactBlock004Results 45
def node2210 : Poly := rowAt compactBlock004Results 46
def node2219 : Poly := rowAt compactBlock004Results 47
def node2226 : Poly := rowAt compactBlock004Results 48
def node2233 : Poly := rowAt compactBlock004Results 49
def node2237 : Poly := rowAt compactBlock004Results 50
def node2265 : Poly := rowAt compactBlock004Results 51
def node2266 : Poly := rowAt compactBlock004Results 52
def node2267 : Poly := rowAt compactBlock004Results 53
def node2273 : Poly := rowAt compactBlock004Results 54
def node2274 : Poly := rowAt compactBlock004Results 55
def node2275 : Poly := rowAt compactBlock004Results 56
def node2276 : Poly := rowAt compactBlock004Results 57
def node2284 : Poly := rowAt compactBlock004Results 58
def node2286 : Poly := rowAt compactBlock004Results 59
def node2287 : Poly := rowAt compactBlock004Results 60
def node2292 : Poly := rowAt compactBlock004Results 61
def node2294 : Poly := rowAt compactBlock004Results 62
def node2295 : Poly := rowAt compactBlock004Results 63
def node2296 : Poly := rowAt compactBlock004Results 64
def node2298 : Poly := rowAt compactBlock004Results 65
def node2300 : Poly := rowAt compactBlock004Results 66
def node2307 : Poly := rowAt compactBlock004Results 67
def node2308 : Poly := rowAt compactBlock004Results 68
def node2309 : Poly := rowAt compactBlock004Results 69
def node2310 : Poly := rowAt compactBlock004Results 70
def node2311 : Poly := rowAt compactBlock004Results 71
def node2312 : Poly := rowAt compactBlock004Results 72
def node2313 : Poly := rowAt compactBlock004Results 73
def node2314 : Poly := rowAt compactBlock004Results 74
def node2315 : Poly := rowAt compactBlock004Results 75
def node2316 : Poly := rowAt compactBlock004Results 76
def node2317 : Poly := rowAt compactBlock004Results 77
def node2319 : Poly := rowAt compactBlock004Results 78
def node2320 : Poly := rowAt compactBlock004Results 79
def node2321 : Poly := rowAt compactBlock004Results 80
def node2325 : Poly := rowAt compactBlock004Results 81
def node2326 : Poly := rowAt compactBlock004Results 82
def node2327 : Poly := rowAt compactBlock004Results 83
def node2329 : Poly := rowAt compactBlock004Results 84
def node2330 : Poly := rowAt compactBlock004Results 85
def node2334 : Poly := rowAt compactBlock004Results 86
def node2335 : Poly := rowAt compactBlock004Results 87

theorem compactBlock004_certificate : outputs compactBlock004Inputs compactBlock004Program compactBlock004Indices = compactBlock004Results := by
  decide +kernel

theorem compactBlock004_derived : ∀ p ∈ compactBlock004Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock004_inputs compactBlock004Program compactBlock004Indices compactBlock004_certificate

#print axioms compactBlock004_derived


def compactBlock005Inputs : List Poly := [node0000, node0130, node0141, node0143, node0144, node0145, node0147, node0149, node0151, node0157, node0173, node0174, node0175, node0176, node0177, node0179, node0180, node0197, node0227, node0397, node0405, node0471, node0525, node0527, node0539, node0542, node0544, node0546, node0548, node0554, node0571, node0573, node0576, node0577, node0628, node0631, node0677, node0794, node0802, node0813, node0868, node0922, node0924, node0936, node0939, node0941, node0943, node0945, node0951, node0968, node0970, node0973, node0974, node1025, node1028, node1074, node1191, node1220, node1333, node1558, node1638, node1639, node1645, node1647, node1648, node1661, node1687, node1689, node1725, node1745, node1776, node1779, node1787, node1839, node1844, node1846, node1852, node1867, node1869, node1870, node1887, node1891, node1925, node1948, node1951, node1973, node1978, node1979, node2002, node2003, node2007, node2056, node2061, node2069, node2071, node2075, node2077, node2133, node2137, node2143, node2160, node2161, node2166, node2168, node2185, node2191, node2195, node2219, node2226, node2267, node2274, node2275, node2276, node2296, node2300, node2307, node2319, node2320, node2321, node2325]

theorem compactBlock005_inputs : ∀ p ∈ compactBlock005Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0000, node0130, node0141, node0143, node0144, node0145, node0147, node0149, node0151, node0157, node0173, node0174, node0175, node0176, node0177, node0179, node0180, node0197, node0227, node0397, node0405, node0471, node0525, node0527, node0539, node0542, node0544, node0546, node0548, node0554, node0571, node0573, node0576, node0577, node0628, node0631, node0677, node0794, node0802, node0813, node0868, node0922, node0924, node0936, node0939, node0941, node0943, node0945, node0951, node0968, node0970, node0973, node0974, node1025, node1028, node1074, node1191, node1220, node1333, node1558, node1638, node1639, node1645, node1647, node1648, node1661, node1687, node1689, node1725, node1745, node1776, node1779, node1787, node1839, node1844, node1846, node1852, node1867, node1869, node1870, node1887, node1891, node1925, node1948, node1951, node1973, node1978, node1979, node2002, node2003, node2007, node2056, node2061, node2069, node2071, node2075, node2077, node2133, node2137, node2143, node2160, node2161, node2166, node2168, node2185, node2191, node2195, node2219, node2226, node2267, node2274, node2275, node2276, node2296, node2300, node2307, node2319, node2320, node2321, node2325], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 0 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 130 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 141 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 143 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 144 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 145 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 147 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 149 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 151 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 157 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 173 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 174 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 175 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 176 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 177 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 179 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 180 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 197 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 227 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 397 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 405 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 471 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 525 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 527 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 539 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 542 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 544 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 546 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 548 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 554 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 571 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 573 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 576 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 577 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 628 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 631 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 677 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 794 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 802 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 813 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 868 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 922 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 924 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 936 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 939 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 941 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 943 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 945 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 951 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 968 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 970 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 973 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 974 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1025 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1028 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1074 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 89)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 89)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 81)
  exact nil_derived _ _

def compactBlock005Program : List Instruction := [
  ⟨15, 56, [(1,0,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨102, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨117, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨109, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨36, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/15),1,(1,2,-1,2,0,0,0))]⟩,
  ⟨56, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/450),1,(1,2,-1,2,0,0,0))]⟩,
  ⟨6, 62, [(1,0,(-3,-2,1,-2,0,0,0))]⟩,
  ⟨26, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/30),1,(3,2,-1,2,0,0,0))]⟩,
  ⟨45, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/1800),1,(3,2,-1,2,0,0,0))]⟩,
  ⟨75, 65, [(1,0,(0,-2,0,2,0,0,0))]⟩,
  ⟨121, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨119, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨46, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1040/3),1,(0,2,0,-2,0,0,0))]⟩,
  ⟨66, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((540800/9),1,(0,2,0,-2,0,0,0))]⟩,
  ⟨79, 70, [(1,0,(0,0,0,2,0,0,0))]⟩,
  ⟨88, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨116, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨6, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨6, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨93, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-195),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨80, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((507/5),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨56, 6, [(1,0,(0,0,0,0,0,0,0)),
  (1040,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨102, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨98, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/2),1,(3,-2,0,-2,0,0,0))]⟩,
  ⟨85, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((257049/50),1,(2,-2,0,0,0,0,0))]⟩,
  ⟨79, 10, [(1,0,(0,0,0,0,0,0,0)),
  (540800,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨107, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨104, 83, [((-1),0,(-2,-2,0,0,0,0,0))]⟩,
  ⟨48, 0, [(1,0,(0,0,0,0,0,0,0)),
  (195,1,(2,0,0,-2,0,0,0))]⟩,
  ⟨107, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((52/15),1,(2,2,0,0,0,0,0))]⟩,
  ⟨68, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/2),1,(2,0,0,-2,0,0,0))]⟩,
  ⟨110, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/225),1,(2,2,0,0,0,0,0))]⟩,
  ⟨141, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨140, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨101, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨118, 91, [((-1),0,(3,-2,0,-2,0,0,0))]⟩,
  ⟨19, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨135, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨134, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨61, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(-3,2,0,2,0,0,0))]⟩,
  ⟨81, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/225),1,(-3,2,0,2,0,0,0))]⟩,
  ⟨42, 97, [((-1),0,(1,0,0,-2,0,0,0))]⟩,
  ⟨65, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/5),1,(-1,0,0,2,0,0,0))]⟩,
  ⟨85, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((338/25),1,(-1,0,0,2,0,0,0))]⟩,
  ⟨106, 100, [(1,0,(-3,-2,0,2,0,0,0))]⟩,
  ⟨113, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(3,2,0,-2,0,0,0))]⟩,
  ⟨109, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨111, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(0,0,0,0,0,0,0))]⟩,
  ⟨117, 50, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨131, 105, [((-1),0,(-1,2,0,0,0,0,0))]⟩,
  ⟨144, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨135, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨169, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨165, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨78, 4, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨125, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨99, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨128, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨171, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨117, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨117, 64, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 117, [((-1),0,(-3,2,0,0,0,0,0))]⟩,
  ⟨87, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨107, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(3,-2,0,0,0,0,0))]⟩,
  ⟨149, 120, [((-1),0,(2,0,1,-2,0,0,0))]⟩,
  ⟨124, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨168, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨181, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨65, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨155, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨157, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((25/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 127, [((-1),0,(1,2,0,-2,0,0,0))]⟩,
  ⟨98, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((78/5),1,(-1,-2,0,2,0,0,0))]⟩,
  ⟨118, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((3042/25),1,(-1,-2,0,2,0,0,0))]⟩,
  ⟨81, 130, [((-1),0,(1,-2,0,0,0,0,0))]⟩,
  ⟨178, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨194, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨104, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((26/3),1,(-1,2,0,0,0,0,0))]⟩,
  ⟨114, 3, [(1,0,(0,0,0,0,0,0,0)),
  (30,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨118, 4, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨126, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((338/9),1,(-1,2,0,0,0,0,0))]⟩,
  ⟨136, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨90, 138, [((-1),0,(-1,-2,0,0,0,0,0))]⟩,
  ⟨178, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨65, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨113, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(1,2,0,0,0,0,0))]⟩,
  ⟨133, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((169/18),1,(1,2,0,0,0,0,0))]⟩,
  ⟨85, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨164, 144, [(1,0,(0,0,1,-2,0,0,0))]⟩,
  ⟨181, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨189, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-312/5),1,(0,0,-1,2,0,0,0))]⟩,
  ⟨132, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-48672/25),1,(0,0,-1,2,0,0,0))]⟩,
  ⟨102, 149, [((-1),0,(-2,0,0,-2,0,0,0))]⟩,
  ⟨123, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/5),1,(2,0,0,2,0,0,0))]⟩,
  ⟨143, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((169/50),1,(2,0,0,2,0,0,0))]⟩,
  ⟨6, 200, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨188, 201, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-1,0,0,1,0,0))]⟩,
  ⟨0, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨110, 155, [(1,0,(-3,2,-1,2,0,0,0))]⟩,
  ⟨130, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-15/2),1,(3,-2,1,-2,0,0,0))]⟩,
  ⟨150, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/8),1,(3,-2,1,-2,0,0,0))]⟩,
  ⟨5, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨4, 115, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨13, 116, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨118, 161, [(1,0,(-3,2,1,-2,0,0,0))]⟩,
  ⟨3, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨138, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/10),1,(3,-2,-1,2,0,0,0))]⟩,
  ⟨158, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/200),1,(3,-2,-1,2,0,0,0))]⟩,
  ⟨74, 123, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨126, 166, [((-1),0,(0,-2,0,-2,0,0,0))]⟩,
  ⟨144, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(0,2,0,2,0,0,0))]⟩,
  ⟨164, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/225),1,(0,2,0,2,0,0,0))]⟩,
  ⟨206, 169, [((-1),0,(0,2,-1,0,0,0,0))]⟩,
  ⟨202, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨212, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨205, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨207, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨50, 4, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨224, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨236, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨231, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨104, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨70, 9, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,1,0,0,0,0))]⟩,
  ⟨70, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨18, 11, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨92, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-2,0,0,-2,0,0,0))]⟩,
  ⟨246, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]



















































































































































































def compactBlock005Indices : List ℕ := [124, 123, 122, 120, 119, 115, 114, 108, 107, 106, 105, 104, 103, 102, 101, 99, 98, 97, 96, 95, 91, 90, 89, 88, 87, 85, 84, 82, 81, 80, 79, 77, 76, 73, 72, 71, 70, 69, 68, 67, 65, 64, 62, 61, 59, 58, 57, 55, 54, 52, 51, 50, 49, 48, 47, 46, 44, 43, 42, 41, 40, 36, 35, 33, 32, 27, 26, 24, 23, 20, 19, 18, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock005Results : List Poly :=
  program_results% (compactBlock005Inputs) (compactBlock005Program) (compactBlock005Indices)

def node2350 : Poly := rowAt compactBlock005Results 0
def node2351 : Poly := rowAt compactBlock005Results 1
def node2352 : Poly := rowAt compactBlock005Results 2
def node2356 : Poly := rowAt compactBlock005Results 3
def node2357 : Poly := rowAt compactBlock005Results 4
def node2364 : Poly := rowAt compactBlock005Results 5
def node2365 : Poly := rowAt compactBlock005Results 6
def node2376 : Poly := rowAt compactBlock005Results 7
def node2377 : Poly := rowAt compactBlock005Results 8
def node2378 : Poly := rowAt compactBlock005Results 9
def node2379 : Poly := rowAt compactBlock005Results 10
def node2380 : Poly := rowAt compactBlock005Results 11
def node2381 : Poly := rowAt compactBlock005Results 12
def node2382 : Poly := rowAt compactBlock005Results 13
def node2383 : Poly := rowAt compactBlock005Results 14
def node2387 : Poly := rowAt compactBlock005Results 15
def node2388 : Poly := rowAt compactBlock005Results 16
def node2389 : Poly := rowAt compactBlock005Results 17
def node2390 : Poly := rowAt compactBlock005Results 18
def node2391 : Poly := rowAt compactBlock005Results 19
def node2412 : Poly := rowAt compactBlock005Results 20
def node2413 : Poly := rowAt compactBlock005Results 21
def node2415 : Poly := rowAt compactBlock005Results 22
def node2416 : Poly := rowAt compactBlock005Results 23
def node2417 : Poly := rowAt compactBlock005Results 24
def node2423 : Poly := rowAt compactBlock005Results 25
def node2424 : Poly := rowAt compactBlock005Results 26
def node2433 : Poly := rowAt compactBlock005Results 27
def node2436 : Poly := rowAt compactBlock005Results 28
def node2438 : Poly := rowAt compactBlock005Results 29
def node2439 : Poly := rowAt compactBlock005Results 30
def node2442 : Poly := rowAt compactBlock005Results 31
def node2443 : Poly := rowAt compactBlock005Results 32
def node2452 : Poly := rowAt compactBlock005Results 33
def node2454 : Poly := rowAt compactBlock005Results 34
def node2456 : Poly := rowAt compactBlock005Results 35
def node2458 : Poly := rowAt compactBlock005Results 36
def node2459 : Poly := rowAt compactBlock005Results 37
def node2460 : Poly := rowAt compactBlock005Results 38
def node2463 : Poly := rowAt compactBlock005Results 39
def node2470 : Poly := rowAt compactBlock005Results 40
def node2471 : Poly := rowAt compactBlock005Results 41
def node2473 : Poly := rowAt compactBlock005Results 42
def node2474 : Poly := rowAt compactBlock005Results 43
def node2483 : Poly := rowAt compactBlock005Results 44
def node2484 : Poly := rowAt compactBlock005Results 45
def node2485 : Poly := rowAt compactBlock005Results 46
def node2488 : Poly := rowAt compactBlock005Results 47
def node2489 : Poly := rowAt compactBlock005Results 48
def node2499 : Poly := rowAt compactBlock005Results 49
def node2500 : Poly := rowAt compactBlock005Results 50
def node2504 : Poly := rowAt compactBlock005Results 51
def node2505 : Poly := rowAt compactBlock005Results 52
def node2506 : Poly := rowAt compactBlock005Results 53
def node2507 : Poly := rowAt compactBlock005Results 54
def node2508 : Poly := rowAt compactBlock005Results 55
def node2514 : Poly := rowAt compactBlock005Results 56
def node2517 : Poly := rowAt compactBlock005Results 57
def node2519 : Poly := rowAt compactBlock005Results 58
def node2522 : Poly := rowAt compactBlock005Results 59
def node2528 : Poly := rowAt compactBlock005Results 60
def node2538 : Poly := rowAt compactBlock005Results 61
def node2539 : Poly := rowAt compactBlock005Results 62
def node2545 : Poly := rowAt compactBlock005Results 63
def node2546 : Poly := rowAt compactBlock005Results 64
def node2557 : Poly := rowAt compactBlock005Results 65
def node2558 : Poly := rowAt compactBlock005Results 66
def node2561 : Poly := rowAt compactBlock005Results 67
def node2563 : Poly := rowAt compactBlock005Results 68
def node2570 : Poly := rowAt compactBlock005Results 69
def node2571 : Poly := rowAt compactBlock005Results 70
def node2572 : Poly := rowAt compactBlock005Results 71
def node2589 : Poly := rowAt compactBlock005Results 72
def node2590 : Poly := rowAt compactBlock005Results 73
def node2597 : Poly := rowAt compactBlock005Results 74
def node2598 : Poly := rowAt compactBlock005Results 75
def node2599 : Poly := rowAt compactBlock005Results 76
def node2600 : Poly := rowAt compactBlock005Results 77
def node2604 : Poly := rowAt compactBlock005Results 78
def node2606 : Poly := rowAt compactBlock005Results 79
def node2607 : Poly := rowAt compactBlock005Results 80
def node2608 : Poly := rowAt compactBlock005Results 81
def node2609 : Poly := rowAt compactBlock005Results 82
def node2610 : Poly := rowAt compactBlock005Results 83
def node2611 : Poly := rowAt compactBlock005Results 84
def node2612 : Poly := rowAt compactBlock005Results 85
def node2613 : Poly := rowAt compactBlock005Results 86
def node2616 : Poly := rowAt compactBlock005Results 87
def node2624 : Poly := rowAt compactBlock005Results 88

theorem compactBlock005_certificate : outputs compactBlock005Inputs compactBlock005Program compactBlock005Indices = compactBlock005Results := by
  decide +kernel

theorem compactBlock005_derived : ∀ p ∈ compactBlock005Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock005_inputs compactBlock005Program compactBlock005Indices compactBlock005_certificate

#print axioms compactBlock005_derived


def compactBlock006Inputs : List Poly := [node0425, node0427, node0479, node0483, node0489, node0537, node0594, node0624, node0822, node0824, node0876, node0880, node0886, node0934, node0991, node1021, node1191, node1285, node1458, node1459, node1460, node1461, node1559, node1653, node1655, node1885, node1886, node1889, node1890, node1955, node1957, node1959, node1960, node1962, node1964, node1966, node1968, node1969, node1970, node1971, node1981, node2024, node2025, node2026, node2030, node2031, node2034, node2035, node2039, node2040, node2041, node2045, node2046, node2049, node2050, node2094, node2134, node2150, node2158, node2186, node2189, node2202, node2210, node2273, node2284, node2286, node2287, node2292, node2294, node2295, node2312, node2317, node2327, node2330, node2350, node2379, node2383, node2387, node2388, node2389, node2390, node2391, node2413, node2415, node2416, node2417, node2433, node2436, node2438, node2443, node2454, node2458, node2459, node2499, node2500, node2514, node2517, node2528, node2597, node2599, node2609, node2610, node2611, node2612, node2624]

theorem compactBlock006_inputs : ∀ p ∈ compactBlock006Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0425, node0427, node0479, node0483, node0489, node0537, node0594, node0624, node0822, node0824, node0876, node0880, node0886, node0934, node0991, node1021, node1191, node1285, node1458, node1459, node1460, node1461, node1559, node1653, node1655, node1885, node1886, node1889, node1890, node1955, node1957, node1959, node1960, node1962, node1964, node1966, node1968, node1969, node1970, node1971, node1981, node2024, node2025, node2026, node2030, node2031, node2034, node2035, node2039, node2040, node2041, node2045, node2046, node2049, node2050, node2094, node2134, node2150, node2158, node2186, node2189, node2202, node2210, node2273, node2284, node2286, node2287, node2292, node2294, node2295, node2312, node2317, node2327, node2330, node2350, node2379, node2383, node2387, node2388, node2389, node2390, node2391, node2413, node2415, node2416, node2417, node2433, node2436, node2438, node2443, node2454, node2458, node2459, node2499, node2500, node2514, node2517, node2528, node2597, node2599, node2609, node2610, node2611, node2612, node2624], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 425 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 427 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 479 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 483 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 489 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 537 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 594 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 624 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 822 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 824 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 876 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 880 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 886 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 934 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 991 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1021 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 88)
  exact nil_derived _ _

def compactBlock006Program : List Instruction := [
  ⟨83, 98, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,1,-2,0,0,0)),
  (1,1,(0,-2,1,0,0,0,0))]⟩,
  ⟨2, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-52),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨27, 100, [(1,0,(0,0,0,0,0,0,0)),
  (195,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨44, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-130/3),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨46, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/10),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨8, 103, [(1,0,(0,0,0,0,0,0,0)),
  (6,1,(0,-2,1,0,0,0,0))]⟩,
  ⟨49, 104, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨33, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((676/15),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨14, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-390),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨53, 107, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨55, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨57, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨59, 110, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨74, 111, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨89, 112, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨87, 113, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨81, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨83, 115, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨27, 116, [(1,0,(0,0,0,0,0,0,0)),
  (1352,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨46, 117, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/2),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨68, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((-8450/9),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨70, 119, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/200),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨33, 120, [(1,0,(0,0,0,0,0,0,0)),
  ((-18),1,(0,-2,1,0,0,0,0))]⟩,
  ⟨73, 121, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-3,-2,0,0,0,0,0))]⟩,
  ⟨52, 122, [(1,0,(0,0,0,0,0,0,0)),
  ((228488/225),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨39, 123, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨77, 124, [(1,0,(0,0,0,0,0,0,0)),
  (3042,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨79, 125, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨81, 126, [(1,0,(0,0,0,0,0,0,0)),
  (3042,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨83, 127, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨92, 128, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨107, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨105, 130, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨101, 131, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨103, 132, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨127, 133, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(-1,-2,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨92, 52, [((-1),0,(2,0,-1,0,0,0,0))]⟩,
  ⟨72, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,0,0,0,0,0,0))]⟩,
  ⟨101, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,0,0,0,0,0))]⟩,
  ⟨128, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨135, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨141, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,0,0,0,0,0))]⟩,
  ⟨143, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨145, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨147, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨127, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨143, 9, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨141, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨144, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨130, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨154, 13, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-1,0,0,1,0,0))]⟩,
  ⟨50, 14, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨75, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-390),1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨53, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨56, 17, [(1,0,(0,0,0,0,0,0,0)),
  (4,1,(-2,0,1,0,0,0,0))]⟩,
  ⟨84, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨86, 19, [(1,0,(0,0,0,0,0,0,0)),
  (65,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨141, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((52/15),1,(-2,0,1,0,0,0,0))]⟩,
  ⟨122, 21, [(1,0,(0,0,0,0,0,0,0)),
  (390,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨66, 22, [(1,0,(0,0,0,0,0,0,0)),
  (420,1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨97, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(1,0,0,0,0,0,0))]⟩,
  ⟨92, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(0,0,0,0,0,0,0))]⟩,
  ⟨47, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨46, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨154, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨47, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(0,0,0,0,0,0,0))]⟩,
  ⟨90, 29, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(1,-2,0,-2,0,0,0))]⟩,
  ⟨75, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨78, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-8),1,(-2,0,1,0,0,0,0))]⟩,
  ⟨101, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨103, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/2),1,(0,0,0,-2,0,0,0))]⟩,
  ⟨156, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/225),1,(-2,0,1,0,0,0,0))]⟩,
  ⟨139, 35, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(0,0,0,-2,0,0,0))]⟩,
  ⟨88, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((-88200),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨113, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(1,0,0,0,0,0,0))]⟩,
  ⟨109, 38, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨43, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨169, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨44, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(0,0,0,0,0,0,0))]⟩,
  ⟨44, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0)),
  ((-12168),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨32, 99, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨39, 101, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 102, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨37, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨159, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨57, 109, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨3, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨159, 106, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨161, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,0,-1,2,0,0,0))]⟩,
  ⟨53, 111, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨147, 112, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨49, 113, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨49, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨172, 115, [(1,0,(0,0,0,0,0,0,0)),
  (195,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨132, 116, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨175, 117, [(1,0,(0,0,0,0,0,0,0)),
  ((52/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨37, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨34, 119, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨179, 120, [(1,0,(0,0,0,0,0,0,0)),
  ((38025/2),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨139, 121, [(1,0,(0,0,0,0,0,0,0)),
  ((169/18),1,(0,0,0,0,0,0,0))]⟩,
  ⟨182, 122, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/225),1,(0,0,0,0,0,0,0))]⟩,
  ⟨28, 123, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨25, 124, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨24, 125, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨205, 127, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨147, 128, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨14, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨14, 130, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨196, 131, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨198, 132, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨116, 133, [(1,0,(0,0,0,0,0,0,0)),
  (12,1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨118, 134, [(1,0,(0,0,0,0,0,0,0)),
  (65,1,(1,0,0,-2,0,0,0))]⟩,
  ⟨171, 135, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨15, 136, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨204, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨129, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((-72),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨131, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨177, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨15, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨15, 142, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨182, 138, [((-1),0,(1,2,-1,0,0,0,0))]⟩,
  ⟨182, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨17, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨17, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨219, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨85, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩
]

































































































































































































def compactBlock006Indices : List ℕ := [126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 114, 112, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 97, 95, 89, 88, 87, 82, 80, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 66, 65, 64, 62, 61, 60, 59, 58, 57, 56, 55, 54, 52, 51, 50, 48, 45, 44, 42, 41, 40, 39, 38, 37, 36, 35, 32, 31, 30, 29, 27, 26, 25, 24, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock006Results : List Poly :=
  program_results% (compactBlock006Inputs) (compactBlock006Program) (compactBlock006Indices)

def node2629 : Poly := rowAt compactBlock006Results 0
def node2631 : Poly := rowAt compactBlock006Results 1
def node2632 : Poly := rowAt compactBlock006Results 2
def node2633 : Poly := rowAt compactBlock006Results 3
def node2635 : Poly := rowAt compactBlock006Results 4
def node2636 : Poly := rowAt compactBlock006Results 5
def node2641 : Poly := rowAt compactBlock006Results 6
def node2642 : Poly := rowAt compactBlock006Results 7
def node2643 : Poly := rowAt compactBlock006Results 8
def node2644 : Poly := rowAt compactBlock006Results 9
def node2647 : Poly := rowAt compactBlock006Results 10
def node2650 : Poly := rowAt compactBlock006Results 11
def node2652 : Poly := rowAt compactBlock006Results 12
def node2657 : Poly := rowAt compactBlock006Results 13
def node2659 : Poly := rowAt compactBlock006Results 14
def node2660 : Poly := rowAt compactBlock006Results 15
def node2661 : Poly := rowAt compactBlock006Results 16
def node2663 : Poly := rowAt compactBlock006Results 17
def node2664 : Poly := rowAt compactBlock006Results 18
def node2669 : Poly := rowAt compactBlock006Results 19
def node2670 : Poly := rowAt compactBlock006Results 20
def node2671 : Poly := rowAt compactBlock006Results 21
def node2672 : Poly := rowAt compactBlock006Results 22
def node2675 : Poly := rowAt compactBlock006Results 23
def node2678 : Poly := rowAt compactBlock006Results 24
def node2680 : Poly := rowAt compactBlock006Results 25
def node2689 : Poly := rowAt compactBlock006Results 26
def node2690 : Poly := rowAt compactBlock006Results 27
def node2691 : Poly := rowAt compactBlock006Results 28
def node2696 : Poly := rowAt compactBlock006Results 29
def node2698 : Poly := rowAt compactBlock006Results 30
def node2702 : Poly := rowAt compactBlock006Results 31
def node2714 : Poly := rowAt compactBlock006Results 32
def node2717 : Poly := rowAt compactBlock006Results 33
def node2718 : Poly := rowAt compactBlock006Results 34
def node2719 : Poly := rowAt compactBlock006Results 35
def node2722 : Poly := rowAt compactBlock006Results 36
def node2723 : Poly := rowAt compactBlock006Results 37
def node2725 : Poly := rowAt compactBlock006Results 38
def node2727 : Poly := rowAt compactBlock006Results 39
def node2729 : Poly := rowAt compactBlock006Results 40
def node2731 : Poly := rowAt compactBlock006Results 41
def node2734 : Poly := rowAt compactBlock006Results 42
def node2735 : Poly := rowAt compactBlock006Results 43
def node2736 : Poly := rowAt compactBlock006Results 44
def node2738 : Poly := rowAt compactBlock006Results 45
def node2740 : Poly := rowAt compactBlock006Results 46
def node2741 : Poly := rowAt compactBlock006Results 47
def node2744 : Poly := rowAt compactBlock006Results 48
def node2745 : Poly := rowAt compactBlock006Results 49
def node2747 : Poly := rowAt compactBlock006Results 50
def node2749 : Poly := rowAt compactBlock006Results 51
def node2751 : Poly := rowAt compactBlock006Results 52
def node2753 : Poly := rowAt compactBlock006Results 53
def node2756 : Poly := rowAt compactBlock006Results 54
def node2757 : Poly := rowAt compactBlock006Results 55
def node2758 : Poly := rowAt compactBlock006Results 56
def node2760 : Poly := rowAt compactBlock006Results 57
def node2765 : Poly := rowAt compactBlock006Results 58
def node2766 : Poly := rowAt compactBlock006Results 59
def node2772 : Poly := rowAt compactBlock006Results 60
def node2773 : Poly := rowAt compactBlock006Results 61
def node2774 : Poly := rowAt compactBlock006Results 62
def node2776 : Poly := rowAt compactBlock006Results 63
def node2779 : Poly := rowAt compactBlock006Results 64
def node2780 : Poly := rowAt compactBlock006Results 65
def node2781 : Poly := rowAt compactBlock006Results 66
def node2782 : Poly := rowAt compactBlock006Results 67
def node2795 : Poly := rowAt compactBlock006Results 68
def node2798 : Poly := rowAt compactBlock006Results 69
def node2799 : Poly := rowAt compactBlock006Results 70
def node2800 : Poly := rowAt compactBlock006Results 71
def node2803 : Poly := rowAt compactBlock006Results 72
def node2806 : Poly := rowAt compactBlock006Results 73
def node2807 : Poly := rowAt compactBlock006Results 74
def node2808 : Poly := rowAt compactBlock006Results 75
def node2814 : Poly := rowAt compactBlock006Results 76
def node2815 : Poly := rowAt compactBlock006Results 77
def node2818 : Poly := rowAt compactBlock006Results 78
def node2825 : Poly := rowAt compactBlock006Results 79
def node2826 : Poly := rowAt compactBlock006Results 80
def node2827 : Poly := rowAt compactBlock006Results 81
def node2829 : Poly := rowAt compactBlock006Results 82
def node2830 : Poly := rowAt compactBlock006Results 83
def node2833 : Poly := rowAt compactBlock006Results 84
def node2834 : Poly := rowAt compactBlock006Results 85
def node2835 : Poly := rowAt compactBlock006Results 86
def node2837 : Poly := rowAt compactBlock006Results 87
def node2838 : Poly := rowAt compactBlock006Results 88
def node2839 : Poly := rowAt compactBlock006Results 89
def node2840 : Poly := rowAt compactBlock006Results 90
def node2841 : Poly := rowAt compactBlock006Results 91
def node2842 : Poly := rowAt compactBlock006Results 92
def node2843 : Poly := rowAt compactBlock006Results 93
def node2846 : Poly := rowAt compactBlock006Results 94
def node2849 : Poly := rowAt compactBlock006Results 95

theorem compactBlock006_certificate : outputs compactBlock006Inputs compactBlock006Program compactBlock006Indices = compactBlock006Results := by
  decide +kernel

theorem compactBlock006_derived : ∀ p ∈ compactBlock006Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock006_inputs compactBlock006Program compactBlock006Indices compactBlock006_certificate

#print axioms compactBlock006_derived


def compactBlock007Inputs : List Poly := [node0318, node0446, node0448, node0450, node0517, node0843, node0845, node0847, node0914, node0981, node1191, node1441, node1444, node1445, node1692, node1693, node1710, node1717, node1718, node1721, node1722, node1752, node1753, node1802, node1803, node1815, node1818, node1906, node1933, node1935, node1989, node1990, node1993, node1994, node2111, node2119, node2121, node2167, node2196, node2197, node2198, node2199, node2204, node2205, node2206, node2207, node2265, node2266, node2334, node2335, node2356, node2357, node2364, node2365, node2412, node2423, node2424, node2442, node2452, node2456, node2483, node2505, node2508, node2561, node2572, node2598, node2600, node2606, node2608, node2613, node2616, node2644, node2650, node2652, node2672, node2678, node2680, node2690, node2698, node2702, node2736, node2738, node2758, node2760, node2765, node2766, node2772, node2781, node2782, node2814, node2815, node2818, node2825, node2826, node2827, node2829, node2830, node2833, node2834, node2835, node2837, node2838, node2839, node2840, node2841, node2842, node2843, node2849]

theorem compactBlock007_inputs : ∀ p ∈ compactBlock007Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0318, node0446, node0448, node0450, node0517, node0843, node0845, node0847, node0914, node0981, node1191, node1441, node1444, node1445, node1692, node1693, node1710, node1717, node1718, node1721, node1722, node1752, node1753, node1802, node1803, node1815, node1818, node1906, node1933, node1935, node1989, node1990, node1993, node1994, node2111, node2119, node2121, node2167, node2196, node2197, node2198, node2199, node2204, node2205, node2206, node2207, node2265, node2266, node2334, node2335, node2356, node2357, node2364, node2365, node2412, node2423, node2424, node2442, node2452, node2456, node2483, node2505, node2508, node2561, node2572, node2598, node2600, node2606, node2608, node2613, node2616, node2644, node2650, node2652, node2672, node2678, node2680, node2690, node2698, node2702, node2736, node2738, node2758, node2760, node2765, node2766, node2772, node2781, node2782, node2814, node2815, node2818, node2825, node2826, node2827, node2829, node2830, node2833, node2834, node2835, node2837, node2838, node2839, node2840, node2841, node2842, node2843, node2849], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 318 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 446 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 448 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 450 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 517 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 843 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 845 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 847 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 914 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 981 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock001_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 55)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 44)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 56)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 87)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 89)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 90)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 91)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 92)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 93)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 95)
  exact nil_derived _ _

def compactBlock007Program : List Instruction := [
  ⟨84, 103, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨90, 104, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨92, 105, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 106, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨89, 107, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨75, 108, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨97, 109, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,0,0,-2,0,0,0))]⟩,
  ⟨70, 110, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨94, 111, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,1,-1,0,1,0))]⟩,
  ⟨101, 112, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨11, 113, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨34, 114, [(1,0,(0,0,0,0,0,0,0)),
  ((13/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨105, 115, [(1,0,(0,0,0,0,0,0,0)),
  ((-12),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨51, 116, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/3),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨53, 117, [(1,0,(0,0,0,0,0,0,0)),
  ((260/3),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨109, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((-65),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨56, 119, [(1,0,(0,0,0,0,0,0,0)),
  ((-260/3),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨58, 120, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨113, 121, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨80, 122, [(1,0,(0,0,0,0,0,0,0)),
  (30,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨92, 123, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨101, 124, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨118, 125, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨104, 126, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨121, 127, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨30, 128, [(1,0,(0,0,0,0,0,0,0)),
  (3042,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨50, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((169/8),1,(0,0,0,0,0,0,0))]⟩,
  ⟨125, 130, [(1,0,(0,0,0,0,0,0,0)),
  (72,1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨70, 131, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/9),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨72, 132, [(1,0,(0,0,0,0,0,0,0)),
  ((33800/9),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨129, 133, [(1,0,(0,0,0,0,0,0,0)),
  ((-4225/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨75, 134, [(1,0,(0,0,0,0,0,0,0)),
  ((-33800/9),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨77, 135, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨133, 136, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨96, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨110, 138, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨118, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨138, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨121, 141, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨106, 49, [((-1),0,(1,-2,-1,2,0,0,0))]⟩,
  ⟨74, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨119, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨42, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨103, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨65, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨80, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/5),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨68, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(0,0,0,0,0,0,0))]⟩,
  ⟨83, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/25),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨152, 155, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨155, 156, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨116, 157, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨108, 158, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨89, 159, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨107, 160, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨122, 161, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨54, 162, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨53, 163, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨52, 164, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨122, 165, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,-1,0,0,1,0,0))]⟩,
  ⟨109, 166, [(1,0,(0,0,0,0,0,0,0)),
  ((13/30),1,(0,0,0,0,0,0,0))]⟩,
  ⟨62, 167, [(1,0,(0,0,0,0,0,0,0)),
  (52,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨86, 168, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨92, 169, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨77, 170, [(1,0,(0,0,0,0,0,0,0)),
  ((-455),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨110, 171, [(1,0,(0,0,0,0,0,0,0)),
  ((-78/5),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨117, 172, [(1,0,(0,0,0,0,0,0,0)),
  ((-1040/3),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨97, 173, [(1,0,(0,0,0,0,0,0,0)),
  ((78/5),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨138, 174, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨141, 175, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨47, 176, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨46, 177, [(1,0,(0,0,0,0,0,0,0)),
  ((-26),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨122, 178, [(1,0,(0,0,0,0,0,0,0)),
  ((169/1800),1,(0,0,0,0,0,0,0))]⟩,
  ⟨78, 179, [(1,0,(0,0,0,0,0,0,0)),
  (1352,1,(-3,0,0,0,0,0,0))]⟩,
  ⟨99, 180, [(1,0,(0,0,0,0,0,0,0)),
  ((169/18),1,(0,0,0,0,0,0,0))]⟩,
  ⟨106, 181, [(1,0,(0,0,0,0,0,0,0)),
  ((338/25),1,(0,0,0,0,0,0,0))]⟩,
  ⟨90, 182, [(1,0,(0,0,0,0,0,0,0)),
  ((207025/2),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨85, 183, [(1,0,(0,0,0,0,0,0,0)),
  (33800,1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨124, 184, [(1,0,(0,0,0,0,0,0,0)),
  ((3042/25),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨131, 185, [(1,0,(0,0,0,0,0,0,0)),
  ((540800/9),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨112, 186, [(1,0,(0,0,0,0,0,0,0)),
  ((3042/25),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨154, 187, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨157, 188, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨45, 189, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨44, 190, [(1,0,(0,0,0,0,0,0,0)),
  ((-338),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨186, 191, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨96, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨34, 33, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨164, 34, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨104, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨87, 36, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨33, 37, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,-1,2,0,0,0))]⟩,
  ⟨49, 38, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨120, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-10/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨151, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨142, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨107, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨73, 43, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨126, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((50/9),1,(0,0,0,0,0,0,0))]⟩,
  ⟨157, 45, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨148, 46, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨113, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-3,0,-1,2,0,0,0))]⟩,
  ⟨63, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(0,-2,-1,2,0,0,0))]⟩,
  ⟨17, 49, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-1,-2,-1,2,0,0,0))]⟩,
  ⟨168, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨15, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨15, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨14, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨186, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨111, 17, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨113, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨165, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-390),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨130, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((-30),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨16, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨121, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨123, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨172, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((338/25),1,(0,0,0,0,0,0,0))]⟩,
  ⟨136, 26, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨138, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨17, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨17, 29, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨115, 131, [((-1),0,(3,0,0,2,0,0,0))]⟩,
  ⟨149, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨74, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨211, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨230, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨76, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨215, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩
]













































































































































































































def compactBlock007Indices : List ℕ := [124, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 87, 85, 84, 83, 82, 81, 80, 77, 74, 73, 72, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 42, 41, 40, 35, 34, 33, 32, 30, 29, 28, 27, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock007Results : List Poly :=
  program_results% (compactBlock007Inputs) (compactBlock007Program) (compactBlock007Indices)

def node2853 : Poly := rowAt compactBlock007Results 0
def node2858 : Poly := rowAt compactBlock007Results 1
def node2859 : Poly := rowAt compactBlock007Results 2
def node2869 : Poly := rowAt compactBlock007Results 3
def node2872 : Poly := rowAt compactBlock007Results 4
def node2874 : Poly := rowAt compactBlock007Results 5
def node2875 : Poly := rowAt compactBlock007Results 6
def node2876 : Poly := rowAt compactBlock007Results 7
def node2877 : Poly := rowAt compactBlock007Results 8
def node2878 : Poly := rowAt compactBlock007Results 9
def node2881 : Poly := rowAt compactBlock007Results 10
def node2886 : Poly := rowAt compactBlock007Results 11
def node2887 : Poly := rowAt compactBlock007Results 12
def node2888 : Poly := rowAt compactBlock007Results 13
def node2890 : Poly := rowAt compactBlock007Results 14
def node2892 : Poly := rowAt compactBlock007Results 15
def node2899 : Poly := rowAt compactBlock007Results 16
def node2901 : Poly := rowAt compactBlock007Results 17
def node2902 : Poly := rowAt compactBlock007Results 18
def node2903 : Poly := rowAt compactBlock007Results 19
def node2904 : Poly := rowAt compactBlock007Results 20
def node2905 : Poly := rowAt compactBlock007Results 21
def node2908 : Poly := rowAt compactBlock007Results 22
def node2913 : Poly := rowAt compactBlock007Results 23
def node2914 : Poly := rowAt compactBlock007Results 24
def node2915 : Poly := rowAt compactBlock007Results 25
def node2917 : Poly := rowAt compactBlock007Results 26
def node2919 : Poly := rowAt compactBlock007Results 27
def node2925 : Poly := rowAt compactBlock007Results 28
def node2930 : Poly := rowAt compactBlock007Results 29
def node2939 : Poly := rowAt compactBlock007Results 30
def node2940 : Poly := rowAt compactBlock007Results 31
def node2941 : Poly := rowAt compactBlock007Results 32
def node2943 : Poly := rowAt compactBlock007Results 33
def node2944 : Poly := rowAt compactBlock007Results 34
def node2948 : Poly := rowAt compactBlock007Results 35
def node2952 : Poly := rowAt compactBlock007Results 36
def node2953 : Poly := rowAt compactBlock007Results 37
def node2954 : Poly := rowAt compactBlock007Results 38
def node2958 : Poly := rowAt compactBlock007Results 39
def node2968 : Poly := rowAt compactBlock007Results 40
def node2977 : Poly := rowAt compactBlock007Results 41
def node2979 : Poly := rowAt compactBlock007Results 42
def node2980 : Poly := rowAt compactBlock007Results 43
def node2981 : Poly := rowAt compactBlock007Results 44
def node2982 : Poly := rowAt compactBlock007Results 45
def node2985 : Poly := rowAt compactBlock007Results 46
def node2986 : Poly := rowAt compactBlock007Results 47
def node2987 : Poly := rowAt compactBlock007Results 48
def node2988 : Poly := rowAt compactBlock007Results 49
def node2990 : Poly := rowAt compactBlock007Results 50
def node2991 : Poly := rowAt compactBlock007Results 51
def node2992 : Poly := rowAt compactBlock007Results 52
def node2995 : Poly := rowAt compactBlock007Results 53
def node2997 : Poly := rowAt compactBlock007Results 54
def node2998 : Poly := rowAt compactBlock007Results 55
def node2999 : Poly := rowAt compactBlock007Results 56
def node3000 : Poly := rowAt compactBlock007Results 57
def node3002 : Poly := rowAt compactBlock007Results 58
def node3003 : Poly := rowAt compactBlock007Results 59
def node3004 : Poly := rowAt compactBlock007Results 60
def node3005 : Poly := rowAt compactBlock007Results 61
def node3006 : Poly := rowAt compactBlock007Results 62
def node3008 : Poly := rowAt compactBlock007Results 63
def node3009 : Poly := rowAt compactBlock007Results 64
def node3010 : Poly := rowAt compactBlock007Results 65
def node3013 : Poly := rowAt compactBlock007Results 66
def node3015 : Poly := rowAt compactBlock007Results 67
def node3017 : Poly := rowAt compactBlock007Results 68
def node3036 : Poly := rowAt compactBlock007Results 69
def node3037 : Poly := rowAt compactBlock007Results 70
def node3040 : Poly := rowAt compactBlock007Results 71
def node3041 : Poly := rowAt compactBlock007Results 72
def node3048 : Poly := rowAt compactBlock007Results 73
def node3049 : Poly := rowAt compactBlock007Results 74
def node3052 : Poly := rowAt compactBlock007Results 75
def node3053 : Poly := rowAt compactBlock007Results 76
def node3060 : Poly := rowAt compactBlock007Results 77
def node3063 : Poly := rowAt compactBlock007Results 78
def node3064 : Poly := rowAt compactBlock007Results 79
def node3065 : Poly := rowAt compactBlock007Results 80
def node3068 : Poly := rowAt compactBlock007Results 81
def node3074 : Poly := rowAt compactBlock007Results 82
def node3075 : Poly := rowAt compactBlock007Results 83
def node3076 : Poly := rowAt compactBlock007Results 84
def node3079 : Poly := rowAt compactBlock007Results 85
def node3081 : Poly := rowAt compactBlock007Results 86
def node3082 : Poly := rowAt compactBlock007Results 87
def node3085 : Poly := rowAt compactBlock007Results 88
def node3086 : Poly := rowAt compactBlock007Results 89
def node3087 : Poly := rowAt compactBlock007Results 90
def node3090 : Poly := rowAt compactBlock007Results 91
def node3092 : Poly := rowAt compactBlock007Results 92
def node3093 : Poly := rowAt compactBlock007Results 93
def node3094 : Poly := rowAt compactBlock007Results 94
def node3096 : Poly := rowAt compactBlock007Results 95
def node3097 : Poly := rowAt compactBlock007Results 96
def node3098 : Poly := rowAt compactBlock007Results 97
def node3099 : Poly := rowAt compactBlock007Results 98
def node3100 : Poly := rowAt compactBlock007Results 99
def node3101 : Poly := rowAt compactBlock007Results 100
def node3102 : Poly := rowAt compactBlock007Results 101

theorem compactBlock007_certificate : outputs compactBlock007Inputs compactBlock007Program compactBlock007Indices = compactBlock007Results := by
  decide +kernel

theorem compactBlock007_derived : ∀ p ∈ compactBlock007Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock007_inputs compactBlock007Program compactBlock007Indices compactBlock007_certificate

#print axioms compactBlock007_derived


def compactBlock008Inputs : List Poly := [node0426, node0455, node0540, node0823, node0937, node0994, node1007, node1191, node1323, node1330, node1783, node1784, node1791, node1792, node1793, node1794, node1855, node1856, node1857, node1860, node1861, node1862, node1915, node1920, node2054, node2070, node2081, node2085, node2089, node2093, node2135, node2175, node2176, node2179, node2180, node2298, node2460, node2463, node2470, node2471, node2473, node2474, node2519, node2522, node2538, node2539, node2563, node2589, node2590, node2604, node2607, node2689, node2691, node2714, node2776, node2795, node2798, node2799, node2800, node2803, node2806, node2807, node2808, node2846, node2858, node2859, node2869, node2872, node2874, node2875, node2876, node2877, node2878, node2881, node2886, node2887, node2888, node2890, node2892, node2899, node2901, node2902, node2903, node2904, node2905, node2908, node2913, node2914, node2915, node2917, node2919, node2925, node2939, node2948, node2954, node2958, node2968, node2991, node3009, node3013, node3015, node3017, node3036, node3037, node3040, node3041, node3048, node3049, node3052, node3053, node3060, node3063, node3064, node3065, node3081, node3092, node3094, node3096, node3097, node3098, node3099, node3100]

theorem compactBlock008_inputs : ∀ p ∈ compactBlock008Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0426, node0455, node0540, node0823, node0937, node0994, node1007, node1191, node1323, node1330, node1783, node1784, node1791, node1792, node1793, node1794, node1855, node1856, node1857, node1860, node1861, node1862, node1915, node1920, node2054, node2070, node2081, node2085, node2089, node2093, node2135, node2175, node2176, node2179, node2180, node2298, node2460, node2463, node2470, node2471, node2473, node2474, node2519, node2522, node2538, node2539, node2563, node2589, node2590, node2604, node2607, node2689, node2691, node2714, node2776, node2795, node2798, node2799, node2800, node2803, node2806, node2807, node2808, node2846, node2858, node2859, node2869, node2872, node2874, node2875, node2876, node2877, node2878, node2881, node2886, node2887, node2888, node2890, node2892, node2899, node2901, node2902, node2903, node2904, node2905, node2908, node2913, node2914, node2915, node2917, node2919, node2925, node2939, node2948, node2954, node2958, node2968, node2991, node3009, node3013, node3015, node3017, node3036, node3037, node3040, node3041, node3048, node3049, node3052, node3053, node3060, node3063, node3064, node3065, node3081, node3092, node3094, node3096, node3097, node3098, node3099, node3100], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 426 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 455 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 540 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 823 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 937 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 994 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1007 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 52)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 91)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 93)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 97)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 58)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 59)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 94)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 2)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 3)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 4)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 6)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 7)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 8)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 10)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 11)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 15)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 21)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 26)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 27)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 73)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 74)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 75)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 76)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 77)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 78)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 79)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 80)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 86)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 92)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 94)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 95)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 96)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 97)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 98)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 99)
  exact nil_derived _ _

def compactBlock008Program : List Instruction := [
  ⟨100, 117, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨112, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨65, 119, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨97, 120, [(1,0,(0,0,0,0,0,0,0)),
  (2,1,(-1,-2,0,0,0,0,0)),
  (1,1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨68, 121, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨70, 122, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,-1,1,-2,1,0,0))]⟩,
  ⟨52, 123, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨73, 124, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,-2,1,-2,0,0,0)),
  (1,1,(-1,-2,1,-1,0,1,0)),
  (1,1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨63, 125, [(1,0,(0,0,0,0,0,0,0)),
  ((-195),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨76, 126, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨78, 127, [(1,0,(0,0,0,0,0,0,0)),
  ((-78),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨80, 128, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 129, [(1,0,(0,0,0,0,0,0,0)),
  ((312/5),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨29, 130, [(1,0,(0,0,0,0,0,0,0)),
  (3,1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨70, 131, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨85, 132, [(1,0,(0,0,0,0,0,0,0)),
  (12,1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨87, 133, [(1,0,(0,0,0,0,0,0,0)),
  ((52/3),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨89, 134, [(1,0,(0,0,0,0,0,0,0)),
  ((-260/3),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨35, 135, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨92, 136, [(1,0,(0,0,0,0,0,0,0)),
  (65,1,(1,0,0,-2,0,0,0))]⟩,
  ⟨62, 137, [(1,0,(0,0,0,0,0,0,0)),
  ((13/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨95, 138, [(1,0,(0,0,0,0,0,0,0)),
  ((260/3),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨79, 139, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨41, 140, [(1,0,(0,0,0,0,0,0,0)),
  ((-2535),1,(-1,-2,0,-2,0,0,0))]⟩,
  ⟨46, 141, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨100, 142, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨84, 143, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨103, 144, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨54, 145, [(1,0,(0,0,0,0,0,0,0)),
  ((52/3),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨143, 146, [(1,0,(0,0,0,0,0,0,0)),
  ((-30),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨107, 147, [(1,0,(0,0,0,0,0,0,0)),
  ((-30),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨109, 148, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨59, 149, [(1,0,(0,0,0,0,0,0,0)),
  ((-156),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨130, 150, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨93, 151, [(1,0,(0,0,0,0,0,0,0)),
  ((-38025/2),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨114, 152, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨116, 153, [(1,0,(0,0,0,0,0,0,0)),
  ((-3042),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨118, 154, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/8),1,(0,0,0,0,0,0,0))]⟩,
  ⟨83, 155, [(1,0,(0,0,0,0,0,0,0)),
  ((48672/25),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨58, 156, [(1,0,(0,0,0,0,0,0,0)),
  ((-9/2),1,(-1,-2,1,0,0,0,0))]⟩,
  ⟨100, 157, [(1,0,(0,0,0,0,0,0,0)),
  ((-169/18),1,(0,0,0,0,0,0,0))]⟩,
  ⟨123, 158, [(1,0,(0,0,0,0,0,0,0)),
  ((-72),1,(-2,-2,1,0,0,0,0))]⟩,
  ⟨125, 159, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/9),1,(-3,0,0,0,0,0,0))]⟩,
  ⟨127, 160, [(1,0,(0,0,0,0,0,0,0)),
  ((-33800/9),1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨64, 161, [(1,0,(0,0,0,0,0,0,0)),
  ((169/450),1,(0,0,0,0,0,0,0))]⟩,
  ⟨130, 162, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨89, 163, [(1,0,(0,0,0,0,0,0,0)),
  ((169/18),1,(0,0,0,0,0,0,0))]⟩,
  ⟨133, 164, [(1,0,(0,0,0,0,0,0,0)),
  ((33800/9),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨109, 165, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/225),1,(0,0,0,0,0,0,0))]⟩,
  ⟨70, 166, [(1,0,(0,0,0,0,0,0,0)),
  ((6426225/2),1,(-1,-2,0,-2,0,0,0))]⟩,
  ⟨73, 167, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨138, 168, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨114, 169, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨141, 170, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨82, 171, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/9),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨170, 172, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨145, 173, [(1,0,(0,0,0,0,0,0,0)),
  (450,1,(0,0,1,-2,0,0,0))]⟩,
  ⟨147, 174, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨87, 175, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨157, 176, [(1,0,(0,0,0,0,0,0,0)),
  (3042,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨96, 67, [(1,0,(3,2,0,-2,0,0,0))]⟩,
  ⟨63, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((156/5),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨66, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-3,-2,0,2,0,0,0))]⟩,
  ⟨100, 70, [(1,0,(1,0,0,0,0,0,0))]⟩,
  ⟨74, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((65/6),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/72),1,(0,0,0,0,0,0,0))]⟩,
  ⟨161, 176, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 92, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨63, 93, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨183, 188, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 189, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨184, 191, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 192, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨170, 173, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 166, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨68, 167, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨1, 117, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨170, 118, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨114, 199, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 200, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨7, 201, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 202, [(1,0,(0,0,0,0,0,0,0)),
  (304200,1,(-3,0,0,-2,0,0,0))]⟩,
  ⟨176, 204, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨2, 205, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨138, 206, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨85, 93, [((-1),0,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,0,1,-2,0,0,0))]⟩,
  ⟨118, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨190, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨88, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨88, 4, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,0,1,-2,0,0,0))]⟩,
  ⟨11, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨18, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-2,-2,0,0,0,0,0)),
  (1,1,(-2,0,0,0,0,0,0))]⟩,
  ⟨106, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((26/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨197, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-10/3),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨127, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-78/5),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨200, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨145, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 12, [(1,0,(0,0,0,0,0,0,0)),
  (156,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨204, 13, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨206, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨134, 15, [(1,0,(0,0,0,0,0,0,0)),
  ((-156/5),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨117, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((338/9),1,(0,0,0,0,0,0,0))]⟩,
  ⟨210, 17, [(1,0,(0,0,0,0,0,0,0)),
  ((50/9),1,(1,0,1,-2,0,0,0))]⟩,
  ⟨138, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((3042/25),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨213, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨155, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/225),1,(0,0,0,0,0,0,0))]⟩,
  ⟨123, 21, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(-2,-2,0,0,0,0,0))]⟩,
  ⟨217, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨219, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-12168/25),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨145, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((12168/25),1,(-2,0,0,0,0,0,0))]⟩,
  ⟨228, 25, [(1,0,(0,0,0,0,0,0,0)),
  (12168,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨20, 164, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨29, 165, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 164, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨0, 166, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨112, 167, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨118, 168, [(1,0,(0,0,0,0,0,0,0)),
  ((-130/3),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨157, 169, [(1,0,(0,0,0,0,0,0,0)),
  ((39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 170, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨124, 171, [(1,0,(0,0,0,0,0,0,0)),
  ((8450/9),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨161, 172, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/8),1,(0,0,0,0,0,0,0))]⟩,
  ⟨132, 173, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨10, 176, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨8, 177, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨56, 178, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨128, 179, [(1,0,(0,0,0,0,0,0,0)),
  ((52/3),1,(-3,2,0,0,0,0,0))]⟩
]















































































































































































































def compactBlock008Indices : List ℕ := [121, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 66, 65, 63, 62, 60, 59, 56, 51, 50, 49, 48, 45, 44, 42, 40, 39, 38, 37, 36, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock008Results : List Poly :=
  program_results% (compactBlock008Inputs) (compactBlock008Program) (compactBlock008Indices)

def node3134 : Poly := rowAt compactBlock008Results 0
def node3136 : Poly := rowAt compactBlock008Results 1
def node3139 : Poly := rowAt compactBlock008Results 2
def node3143 : Poly := rowAt compactBlock008Results 3
def node3145 : Poly := rowAt compactBlock008Results 4
def node3147 : Poly := rowAt compactBlock008Results 5
def node3148 : Poly := rowAt compactBlock008Results 6
def node3149 : Poly := rowAt compactBlock008Results 7
def node3150 : Poly := rowAt compactBlock008Results 8
def node3151 : Poly := rowAt compactBlock008Results 9
def node3153 : Poly := rowAt compactBlock008Results 10
def node3154 : Poly := rowAt compactBlock008Results 11
def node3157 : Poly := rowAt compactBlock008Results 12
def node3159 : Poly := rowAt compactBlock008Results 13
def node3164 : Poly := rowAt compactBlock008Results 14
def node3165 : Poly := rowAt compactBlock008Results 15
def node3168 : Poly := rowAt compactBlock008Results 16
def node3170 : Poly := rowAt compactBlock008Results 17
def node3171 : Poly := rowAt compactBlock008Results 18
def node3172 : Poly := rowAt compactBlock008Results 19
def node3173 : Poly := rowAt compactBlock008Results 20
def node3174 : Poly := rowAt compactBlock008Results 21
def node3176 : Poly := rowAt compactBlock008Results 22
def node3177 : Poly := rowAt compactBlock008Results 23
def node3180 : Poly := rowAt compactBlock008Results 24
def node3181 : Poly := rowAt compactBlock008Results 25
def node3182 : Poly := rowAt compactBlock008Results 26
def node3184 : Poly := rowAt compactBlock008Results 27
def node3187 : Poly := rowAt compactBlock008Results 28
def node3191 : Poly := rowAt compactBlock008Results 29
def node3193 : Poly := rowAt compactBlock008Results 30
def node3195 : Poly := rowAt compactBlock008Results 31
def node3196 : Poly := rowAt compactBlock008Results 32
def node3197 : Poly := rowAt compactBlock008Results 33
def node3198 : Poly := rowAt compactBlock008Results 34
def node3199 : Poly := rowAt compactBlock008Results 35
def node3201 : Poly := rowAt compactBlock008Results 36
def node3202 : Poly := rowAt compactBlock008Results 37
def node3205 : Poly := rowAt compactBlock008Results 38
def node3207 : Poly := rowAt compactBlock008Results 39
def node3212 : Poly := rowAt compactBlock008Results 40
def node3213 : Poly := rowAt compactBlock008Results 41
def node3216 : Poly := rowAt compactBlock008Results 42
def node3218 : Poly := rowAt compactBlock008Results 43
def node3219 : Poly := rowAt compactBlock008Results 44
def node3220 : Poly := rowAt compactBlock008Results 45
def node3221 : Poly := rowAt compactBlock008Results 46
def node3222 : Poly := rowAt compactBlock008Results 47
def node3224 : Poly := rowAt compactBlock008Results 48
def node3225 : Poly := rowAt compactBlock008Results 49
def node3228 : Poly := rowAt compactBlock008Results 50
def node3229 : Poly := rowAt compactBlock008Results 51
def node3230 : Poly := rowAt compactBlock008Results 52
def node3235 : Poly := rowAt compactBlock008Results 53
def node3236 : Poly := rowAt compactBlock008Results 54
def node3240 : Poly := rowAt compactBlock008Results 55
def node3241 : Poly := rowAt compactBlock008Results 56
def node3247 : Poly := rowAt compactBlock008Results 57
def node3248 : Poly := rowAt compactBlock008Results 58
def node3259 : Poly := rowAt compactBlock008Results 59
def node3277 : Poly := rowAt compactBlock008Results 60
def node3278 : Poly := rowAt compactBlock008Results 61
def node3281 : Poly := rowAt compactBlock008Results 62
def node3283 : Poly := rowAt compactBlock008Results 63
def node3296 : Poly := rowAt compactBlock008Results 64
def node3298 : Poly := rowAt compactBlock008Results 65
def node3300 : Poly := rowAt compactBlock008Results 66
def node3306 : Poly := rowAt compactBlock008Results 67
def node3309 : Poly := rowAt compactBlock008Results 68
def node3310 : Poly := rowAt compactBlock008Results 69
def node3311 : Poly := rowAt compactBlock008Results 70
def node3312 : Poly := rowAt compactBlock008Results 71
def node3324 : Poly := rowAt compactBlock008Results 72
def node3336 : Poly := rowAt compactBlock008Results 73
def node3337 : Poly := rowAt compactBlock008Results 74
def node3338 : Poly := rowAt compactBlock008Results 75
def node3339 : Poly := rowAt compactBlock008Results 76
def node3342 : Poly := rowAt compactBlock008Results 77
def node3344 : Poly := rowAt compactBlock008Results 78
def node3345 : Poly := rowAt compactBlock008Results 79
def node3346 : Poly := rowAt compactBlock008Results 80
def node3347 : Poly := rowAt compactBlock008Results 81
def node3352 : Poly := rowAt compactBlock008Results 82
def node3353 : Poly := rowAt compactBlock008Results 83
def node3354 : Poly := rowAt compactBlock008Results 84
def node3355 : Poly := rowAt compactBlock008Results 85
def node3358 : Poly := rowAt compactBlock008Results 86
def node3360 : Poly := rowAt compactBlock008Results 87
def node3361 : Poly := rowAt compactBlock008Results 88
def node3362 : Poly := rowAt compactBlock008Results 89
def node3363 : Poly := rowAt compactBlock008Results 90
def node3366 : Poly := rowAt compactBlock008Results 91
def node3386 : Poly := rowAt compactBlock008Results 92
def node3394 : Poly := rowAt compactBlock008Results 93
def node3395 : Poly := rowAt compactBlock008Results 94
def node3396 : Poly := rowAt compactBlock008Results 95
def node3397 : Poly := rowAt compactBlock008Results 96
def node3398 : Poly := rowAt compactBlock008Results 97
def node3399 : Poly := rowAt compactBlock008Results 98
def node3402 : Poly := rowAt compactBlock008Results 99
def node3403 : Poly := rowAt compactBlock008Results 100
def node3409 : Poly := rowAt compactBlock008Results 101
def node3413 : Poly := rowAt compactBlock008Results 102

theorem compactBlock008_certificate : outputs compactBlock008Inputs compactBlock008Program compactBlock008Indices = compactBlock008Results := by
  decide +kernel

theorem compactBlock008_derived : ∀ p ∈ compactBlock008Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock008_inputs compactBlock008Program compactBlock008Indices compactBlock008_certificate

#print axioms compactBlock008_derived


def compactBlock009Inputs : List Poly := [node0428, node0451, node0491, node0500, node0543, node0574, node0658, node0825, node0848, node0852, node0888, node0897, node0940, node0971, node1055, node1191, node1207, node1214, node1775, node1778, node1943, node1944, node2144, node2145, node2148, node2151, node2152, node2153, node2233, node2326, node2351, node2439, node2484, node2485, node2504, node2506, node2507, node2545, node2546, node2691, node2696, node2717, node2718, node2719, node2722, node2723, node2725, node2727, node2729, node2731, node2734, node2735, node2740, node2741, node2744, node2745, node2930, node2940, node2941, node2943, node2944, node2952, node2953, node2990, node3068, node3074, node3075, node3076, node3079, node3085, node3086, node3087, node3090, node3134, node3172, node3173, node3176, node3177, node3224, node3225, node3247, node3277, node3278, node3281, node3283, node3298, node3300, node3306, node3309, node3310, node3311, node3312, node3324, node3386, node3394, node3395, node3396, node3397, node3402, node3409, node3413]

theorem compactBlock009_inputs : ∀ p ∈ compactBlock009Inputs, Derived sourceRows 1191 p := by
  change ∀ p ∈ [node0428, node0451, node0491, node0500, node0543, node0574, node0658, node0825, node0848, node0852, node0888, node0897, node0940, node0971, node1055, node1191, node1207, node1214, node1775, node1778, node1943, node1944, node2144, node2145, node2148, node2151, node2152, node2153, node2233, node2326, node2351, node2439, node2484, node2485, node2504, node2506, node2507, node2545, node2546, node2691, node2696, node2717, node2718, node2719, node2722, node2723, node2725, node2727, node2729, node2731, node2734, node2735, node2740, node2741, node2744, node2745, node2930, node2940, node2941, node2943, node2944, node2952, node2953, node2990, node3068, node3074, node3075, node3076, node3079, node3085, node3086, node3087, node3090, node3134, node3172, node3173, node3176, node3177, node3224, node3225, node3247, node3277, node3278, node3281, node3283, node3298, node3300, node3306, node3309, node3310, node3311, node3312, node3324, node3386, node3394, node3395, node3396, node3397, node3402, node3409, node3413], Derived sourceRows 1191 p
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 428 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 451 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 491 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 500 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 543 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 574 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 658 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 825 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 848 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 852 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 888 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 897 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 940 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 971 (by decide))
  apply cons_derived (Derived.source (sources := sourceRows) (initial := 1191) 1055 (by decide))
  apply cons_derived node1191_derived
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 5)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock000_derived 9)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock002_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 24)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock003_derived 25)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 12)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 13)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 14)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 16)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 17)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 18)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock004_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 1)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 30)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 45)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 51)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 53)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 54)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock005_derived 64)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 28)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 35)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 38)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 39)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 40)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 41)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 42)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 43)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 46)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 47)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock006_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 29)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 31)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 32)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 33)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 34)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 36)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 37)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 50)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 81)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 82)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 83)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 84)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 85)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 88)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 89)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 90)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock007_derived 91)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 0)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 19)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 20)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 22)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 23)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 48)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 49)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 57)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 60)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 61)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 62)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 63)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 65)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 66)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 67)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 68)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 69)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 70)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 71)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 72)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 92)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 93)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 94)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 95)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 96)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 99)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 101)
  apply cons_derived (QuantitativeArithmeticLaurentProgram.rowAt_derived SmallLevelTwentySixGermDAG.compactBlock008_derived 102)
  exact nil_derived _ _

def compactBlock009Program : List Instruction := [
  ⟨16, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨10, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨19, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-3,0,1,-2,0,0,0))]⟩,
  ⟨64, 18, [((-1),0,(-2,2,-1,2,0,0,0))]⟩,
  ⟨86, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨7, 1, [(1,0,(0,0,0,0,0,0,0)),
  (15,1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨16, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-225/2),1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨69, 22, [((-1),0,(-2,2,-1,2,0,0,0))]⟩,
  ⟨3, 0, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨90, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(2,-2,1,-2,0,0,0))]⟩,
  ⟨30, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨32, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/225),1,(0,0,0,0,0,0,0))]⟩,
  ⟨76, 27, [((-1),0,(0,2,0,2,0,0,0))]⟩,
  ⟨100, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨104, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨106, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨96, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨115, 4, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨49, 5, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨19, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-65),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨85, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((-39),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨24, 8, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨88, 9, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨90, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((26/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨58, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((26/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨62, 12, [(1,0,(0,0,0,0,0,0,0)),
  ((-13/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨94, 13, [(1,0,(0,0,0,0,0,0,0)),
  (390,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨33, 14, [(1,0,(0,0,0,0,0,0,0)),
  ((-20),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨104, 15, [(1,0,(0,0,0,0,0,0,0)),
  (30,1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨106, 16, [(1,0,(0,0,0,0,0,0,0)),
  (30,1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨65, 17, [(1,0,(0,0,0,0,0,0,0)),
  (76050,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨38, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨101, 19, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨44, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((-1800),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨104, 21, [(1,0,(0,0,0,0,0,0,0)),
  (1800,1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨106, 22, [(1,0,(0,0,0,0,0,0,0)),
  ((-338/25),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((338/9),1,(0,0,0,0,0,0,0))]⟩,
  ⟨75, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((169/50),1,(0,0,0,0,0,0,0))]⟩,
  ⟨110, 25, [(1,0,(0,0,0,0,0,0,0)),
  ((-76050),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨53, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-200),1,(0,0,1,-2,0,0,0))]⟩,
  ⟨118, 27, [(1,0,(0,0,0,0,0,0,0)),
  (450,1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨120, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-450),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨28, 57, [((-1),0,(1,-2,-1,2,0,0,0))]⟩,
  ⟨25, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨100, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨128, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,1,-2,0,0,0))]⟩,
  ⟨36, 3, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨104, 4, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨80, 5, [(1,0,(0,0,0,0,0,0,0)),
  (5,1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨107, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((52/5),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨54, 7, [(1,0,(0,0,0,0,0,0,0)),
  ((52/3),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨110, 8, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/8),1,(0,0,0,0,0,0,0))]⟩,
  ⟨85, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-25/2),1,(-1,2,1,-2,0,0,0))]⟩,
  ⟨113, 10, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/25),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨66, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/9),1,(-3,2,0,0,0,0,0))]⟩,
  ⟨148, 70, [(1,0,(-2,0,0,2,0,0,0))]⟩,
  ⟨57, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((65/2),1,(3,0,0,-2,0,0,0))]⟩,
  ⟨65, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/8),1,(3,0,0,-2,0,0,0))]⟩,
  ⟨150, 73, [((-1),0,(3,0,1,-2,0,0,0))]⟩,
  ⟨44, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨100, 1, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨66, 2, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨75, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1352/225),1,(-3,2,-1,2,0,0,0))]⟩,
  ⟨3, 78, [(1,0,(-1,2,-1,2,0,0,0))]⟩,
  ⟨149, 0, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨149, 1, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(0,0,0,0,0,0,0))]⟩,
  ⟨154, 2, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨156, 3, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨52, 4, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨52, 5, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,-2,0,0,0,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨26, 6, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(-1,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,0,0,0,0)),
  ((-1),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨52, 7, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(1,0,0,-2,0,0,0))]⟩,
  ⟨171, 8, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨159, 9, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,0,0,0,0,0)),
  ((-1),1,(0,-1,0,0,1,0,0)),
  ((-1),1,(0,0,0,0,0,0,0))]⟩,
  ⟨28, 10, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨116, 11, [(1,0,(0,0,0,0,0,0,0)),
  ((-1),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨149, 12, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-3,0,1,-2,0,0,0)),
  ((-1),1,(-3,0,1,-1,0,1,0)),
  (1,1,(-3,0,1,0,0,0,0))]⟩,
  ⟨30, 13, [(1,0,(0,0,0,0,0,0,0)),
  (1,1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨120, 14, [(1,0,(0,0,0,0,0,0,0)),
  (390,1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨122, 15, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(0,-2,0,0,0,0,0))]⟩,
  ⟨174, 16, [(1,0,(0,0,0,0,0,0,0)),
  ((130/3),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨61, 17, [(1,0,(0,0,0,0,0,0,0)),
  (65,1,(1,0,0,-2,0,0,0))]⟩,
  ⟨104, 18, [(1,0,(0,0,0,0,0,0,0)),
  ((195/2),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨62, 19, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(1,-2,0,0,0,0,0))]⟩,
  ⟨27, 20, [(1,0,(0,0,0,0,0,0,0)),
  ((65/2),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨185, 21, [(1,0,(0,0,0,0,0,0,0)),
  ((52/3),1,(-4,2,0,0,0,0,0))]⟩,
  ⟨104, 22, [(1,0,(0,0,0,0,0,0,0)),
  (13,1,(0,0,0,0,0,0,0))]⟩,
  ⟨131, 23, [(1,0,(0,0,0,0,0,0,0)),
  ((-4),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨111, 24, [(1,0,(0,0,0,0,0,0,0)),
  ((-13),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨134, 25, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨68, 26, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨137, 27, [(1,0,(0,0,0,0,0,0,0)),
  ((-65),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨69, 28, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-2,-2,1,-2,0,0,0))]⟩,
  ⟨117, 29, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨141, 30, [(1,0,(0,0,0,0,0,0,0)),
  ((-52/15),1,(-3,0,1,0,0,0,0))]⟩,
  ⟨71, 31, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨191, 32, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨72, 33, [(1,0,(0,0,0,0,0,0,0)),
  ((-26/3),1,(0,0,0,0,0,0,0))]⟩,
  ⟨72, 34, [(1,0,(0,0,0,0,0,0,0)),
  ((13/5),1,(0,0,0,0,0,0,0))]⟩,
  ⟨129, 35, [(1,0,(0,0,0,0,0,0,0)),
  ((13/15),1,(0,0,0,0,0,0,0))]⟩,
  ⟨73, 36, [(1,0,(0,0,0,0,0,0,0)),
  ((-390),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨149, 37, [(1,0,(0,0,0,0,0,0,0)),
  ((-390),1,(-1,0,0,-2,0,0,0))]⟩,
  ⟨131, 38, [(1,0,(0,0,0,0,0,0,0)),
  (78,1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨152, 39, [(1,0,(0,0,0,0,0,0,0)),
  ((-420),1,(-1,-2,1,-2,0,0,0))]⟩,
  ⟨132, 40, [(1,0,(0,0,0,0,0,0,0)),
  ((-624/5),1,(-1,-2,0,0,0,0,0))]⟩,
  ⟨104, 41, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨202, 42, [(1,0,(0,0,0,0,0,0,0)),
  ((-60),1,(-4,0,1,-2,0,0,0))]⟩,
  ⟨181, 43, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨183, 44, [(1,0,(0,0,0,0,0,0,0)),
  ((-39/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨134, 45, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨160, 46, [(1,0,(0,0,0,0,0,0,0)),
  (39,1,(-1,0,0,0,0,0,0))]⟩,
  ⟨82, 47, [(1,0,(0,0,0,0,0,0,0)),
  ((-30),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨82, 48, [(1,0,(0,0,0,0,0,0,0)),
  ((-30),1,(1,-2,1,-2,0,0,0))]⟩,
  ⟨164, 49, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨177, 50, [(1,0,(0,0,0,0,0,0,0)),
  (60,1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨167, 51, [(1,0,(0,0,0,0,0,0,0)),
  ((-76050),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨85, 52, [(1,0,(0,0,0,0,0,0,0)),
  ((-76050),1,(0,-2,0,-2,0,0,0))]⟩,
  ⟨170, 53, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(0,-2,0,0,0,0,0))]⟩,
  ⟨215, 54, [(1,0,(0,0,0,0,0,0,0)),
  ((-8450/9),1,(-2,2,0,-2,0,0,0))]⟩,
  ⟨87, 55, [(1,0,(0,0,0,0,0,0,0)),
  ((-4225/2),1,(1,0,0,-2,0,0,0))]⟩,
  ⟨146, 56, [(1,0,(0,0,0,0,0,0,0)),
  ((-38025/8),1,(0,-2,1,-2,0,0,0))]⟩,
  ⟨88, 57, [(1,0,(0,0,0,0,0,0,0)),
  ((1521/2),1,(1,-2,0,0,0,0,0))]⟩,
  ⟨64, 58, [(1,0,(0,0,0,0,0,0,0)),
  ((4225/8),1,(-1,2,0,-2,0,0,0))]⟩,
  ⟨121, 59, [(1,0,(0,0,0,0,0,0,0)),
  ((1352/9),1,(-4,2,0,0,0,0,0))]⟩,
  ⟨143, 60, [(1,0,(0,0,0,0,0,0,0)),
  ((169/2),1,(0,0,0,0,0,0,0))]⟩,
  ⟨179, 61, [(1,0,(0,0,0,0,0,0,0)),
  (8,1,(-3,0,1,0,0,0,0))]⟩,
  ⟨153, 62, [(1,0,(0,0,0,0,0,0,0)),
  ((169/2),1,(-1,0,0,0,0,0,0))]⟩,
  ⟨182, 63, [(1,0,(0,0,0,0,0,0,0)),
  ((-1521/2),1,(-1,-2,0,0,0,0,0))]⟩
]



























































































































































































def compactBlock009Indices : List ℕ := [125, 122, 121, 119, 117, 116, 100, 94, 93, 92, 91, 90, 89, 88, 87, 86, 83, 80, 79, 78, 77, 76, 75, 74, 73, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
def compactBlock009Results : List Poly :=
  program_results% (compactBlock009Inputs) (compactBlock009Program) (compactBlock009Indices)

def node3419 : Poly := rowAt compactBlock009Results 0
def node3431 : Poly := rowAt compactBlock009Results 1
def node3433 : Poly := rowAt compactBlock009Results 2
def node3436 : Poly := rowAt compactBlock009Results 3
def node3445 : Poly := rowAt compactBlock009Results 4
def node3447 : Poly := rowAt compactBlock009Results 5
def node3481 : Poly := rowAt compactBlock009Results 6
def node3490 : Poly := rowAt compactBlock009Results 7
def node3491 : Poly := rowAt compactBlock009Results 8
def node3492 : Poly := rowAt compactBlock009Results 9
def node3494 : Poly := rowAt compactBlock009Results 10
def node3495 : Poly := rowAt compactBlock009Results 11
def node3497 : Poly := rowAt compactBlock009Results 12
def node3498 : Poly := rowAt compactBlock009Results 13
def node3500 : Poly := rowAt compactBlock009Results 14
def node3501 : Poly := rowAt compactBlock009Results 15
def node3507 : Poly := rowAt compactBlock009Results 16
def node3526 : Poly := rowAt compactBlock009Results 17
def node3527 : Poly := rowAt compactBlock009Results 18
def node3528 : Poly := rowAt compactBlock009Results 19
def node3529 : Poly := rowAt compactBlock009Results 20
def node3532 : Poly := rowAt compactBlock009Results 21
def node3533 : Poly := rowAt compactBlock009Results 22
def node3534 : Poly := rowAt compactBlock009Results 23
def node3535 : Poly := rowAt compactBlock009Results 24
def node3564 : Poly := rowAt compactBlock009Results 25
def node3569 : Poly := rowAt compactBlock009Results 26
def node3570 : Poly := rowAt compactBlock009Results 27
def node3571 : Poly := rowAt compactBlock009Results 28
def node3572 : Poly := rowAt compactBlock009Results 29
def node3573 : Poly := rowAt compactBlock009Results 30
def node3574 : Poly := rowAt compactBlock009Results 31
def node3575 : Poly := rowAt compactBlock009Results 32
def node3576 : Poly := rowAt compactBlock009Results 33
def node3579 : Poly := rowAt compactBlock009Results 34
def node3580 : Poly := rowAt compactBlock009Results 35
def node3584 : Poly := rowAt compactBlock009Results 36
def node3595 : Poly := rowAt compactBlock009Results 37
def node3623 : Poly := rowAt compactBlock009Results 38
def node3626 : Poly := rowAt compactBlock009Results 39
def node3631 : Poly := rowAt compactBlock009Results 40
def node3632 : Poly := rowAt compactBlock009Results 41
def node3633 : Poly := rowAt compactBlock009Results 42
def node3634 : Poly := rowAt compactBlock009Results 43
def node3638 : Poly := rowAt compactBlock009Results 44
def node3639 : Poly := rowAt compactBlock009Results 45
def node3640 : Poly := rowAt compactBlock009Results 46
def node3642 : Poly := rowAt compactBlock009Results 47
def node3645 : Poly := rowAt compactBlock009Results 48
def node3646 : Poly := rowAt compactBlock009Results 49
def node3647 : Poly := rowAt compactBlock009Results 50
def node3648 : Poly := rowAt compactBlock009Results 51
def node3653 : Poly := rowAt compactBlock009Results 52
def node3654 : Poly := rowAt compactBlock009Results 53
def node3655 : Poly := rowAt compactBlock009Results 54
def node3656 : Poly := rowAt compactBlock009Results 55
def node3660 : Poly := rowAt compactBlock009Results 56
def node3661 : Poly := rowAt compactBlock009Results 57
def node3662 : Poly := rowAt compactBlock009Results 58
def node3664 : Poly := rowAt compactBlock009Results 59
def node3666 : Poly := rowAt compactBlock009Results 60
def node3671 : Poly := rowAt compactBlock009Results 61
def node3673 : Poly := rowAt compactBlock009Results 62
def node3674 : Poly := rowAt compactBlock009Results 63
def node3676 : Poly := rowAt compactBlock009Results 64
def node3681 : Poly := rowAt compactBlock009Results 65
def node3683 : Poly := rowAt compactBlock009Results 66
def node3684 : Poly := rowAt compactBlock009Results 67
def node3687 : Poly := rowAt compactBlock009Results 68
def node3688 : Poly := rowAt compactBlock009Results 69
def node3689 : Poly := rowAt compactBlock009Results 70
def node3690 : Poly := rowAt compactBlock009Results 71
def node3691 : Poly := rowAt compactBlock009Results 72
def node3692 : Poly := rowAt compactBlock009Results 73
def node3693 : Poly := rowAt compactBlock009Results 74
def node3694 : Poly := rowAt compactBlock009Results 75
def node3695 : Poly := rowAt compactBlock009Results 76
def node3696 : Poly := rowAt compactBlock009Results 77
def node3697 : Poly := rowAt compactBlock009Results 78
def node3698 : Poly := rowAt compactBlock009Results 79
def node3700 : Poly := rowAt compactBlock009Results 80
def node3702 : Poly := rowAt compactBlock009Results 81
def node3704 : Poly := rowAt compactBlock009Results 82
def node3705 : Poly := rowAt compactBlock009Results 83
def node3706 : Poly := rowAt compactBlock009Results 84
def node3708 : Poly := rowAt compactBlock009Results 85
def node3711 : Poly := rowAt compactBlock009Results 86
def node3712 : Poly := rowAt compactBlock009Results 87
def node3713 : Poly := rowAt compactBlock009Results 88
def node3714 : Poly := rowAt compactBlock009Results 89
def node3719 : Poly := rowAt compactBlock009Results 90
def node3720 : Poly := rowAt compactBlock009Results 91
def node3721 : Poly := rowAt compactBlock009Results 92

theorem compactBlock009_certificate : outputs compactBlock009Inputs compactBlock009Program compactBlock009Indices = compactBlock009Results := by
  decide +kernel

theorem compactBlock009_derived : ∀ p ∈ compactBlock009Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock009_inputs compactBlock009Program compactBlock009Indices compactBlock009_certificate

#print axioms compactBlock009_derived


}
end SmallLevelTwentySixGermDAG
end
