module
public meta import QuantitativeArithmeticLaurentProgramDataV4
public import QuantitativeArithmeticLaurentProgramTheoryV4
public import SmallLevelTwentySixGermDAGSourceRowsV1
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

theorem compactBlock027_certificate : outputs compactBlock027Inputs compactBlock027Program compactBlock027Indices = compactBlock027Results := by
  decide +kernel

theorem compactBlock027_derived : ∀ p ∈ compactBlock027Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock027_inputs compactBlock027Program compactBlock027Indices compactBlock027_certificate

#print axioms compactBlock027_derived


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

theorem compactBlock028_certificate : outputs compactBlock028Inputs compactBlock028Program compactBlock028Indices = compactBlock028Results := by
  decide +kernel

theorem compactBlock028_derived : ∀ p ∈ compactBlock028Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock028_inputs compactBlock028Program compactBlock028Indices compactBlock028_certificate

#print axioms compactBlock028_derived


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

theorem compactBlock029_certificate : outputs compactBlock029Inputs compactBlock029Program compactBlock029Indices = compactBlock029Results := by
  decide +kernel

theorem compactBlock029_derived : ∀ p ∈ compactBlock029Results, Derived sourceRows 1191 p :=
  checked_outputs compactBlock029_inputs compactBlock029Program compactBlock029Indices compactBlock029_certificate

#print axioms compactBlock029_derived
end SmallLevelTwentySixGermDAG
end
