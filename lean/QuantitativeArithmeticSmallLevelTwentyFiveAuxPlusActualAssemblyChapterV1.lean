module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusActualBindingsChapterV1

public import QuantitativeArithmeticFiniteRangeCertificatesV1
public import QuantitativeArithmeticListBoundsV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridDataTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModelTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSymbolicRowsV1
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import QuantitativeArithmeticCompactFactCommandsV1
public meta import QuantitativeArithmeticFiniteRangeCommandsV4

-- These editor-information linters are incompatible with compact_certificate.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusActualDispatchV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate def actual (j : ℕ) : SourceRow :=
  match j/32 with
  | 0 => actualBlock0 (j%32)
  | 1 => actualBlock1 (j%32)
  | 2 => actualBlock2 (j%32)
  | 3 => actualBlock3 (j%32)
  | 4 => actualBlock4 (j%32)
  | 5 => actualBlock5 (j%32)
  | 6 => actualBlock6 (j%32)
  | 7 => actualBlock7 (j%32)
  | 8 => actualBlock8 (j%32)
  | 9 => actualBlock9 (j%32)
  | 10 => actualBlock10 (j%32)
  | 11 => actualBlock11 (j%32)
  | 12 => actualBlock12 (j%32)
  | 13 => actualBlock13 (j%32)
  | 14 => actualBlock14 (j%32)
  | 15 => actualBlock15 (j%32)
  | 16 => actualBlock16 (j%32)
  | 17 => actualBlock17 (j%32)
  | 18 => actualBlock18 (j%32)
  | 19 => actualBlock19 (j%32)
  | 20 => actualBlock20 (j%32)
  | 21 => actualBlock21 (j%32)
  | 22 => actualBlock22 (j%32)
  | 23 => actualBlock23 (j%32)
  | 24 => actualBlock24 (j%32)
  | 25 => actualBlock25 (j%32)
  | 26 => actualBlock26 (j%32)
  | 27 => actualBlock27 (j%32)
  | 28 => actualBlock28 (j%32)
  | 29 => actualBlock29 (j%32)
  | 30 => actualBlock30 (j%32)
  | 31 => actualBlock31 (j%32)
  | 32 => actualBlock32 (j%32)
  | 33 => actualBlock33 (j%32)
  | 34 => actualBlock34 (j%32)
  | 35 => actualBlock35 (j%32)
  | 36 => actualBlock36 (j%32)
  | 37 => actualBlock37 (j%32)
  | 38 => actualBlock38 (j%32)
  | 39 => actualBlock39 (j%32)
  | 40 => actualBlock40 (j%32)
  | 41 => actualBlock41 (j%32)
  | 42 => actualBlock42 (j%32)
  | 43 => actualBlock43 (j%32)
  | 44 => actualBlock44 (j%32)
  | 45 => actualBlock45 (j%32)
  | 46 => actualBlock46 (j%32)
  | 47 => actualBlock47 (j%32)
  | 48 => actualBlock48 (j%32)
  | 49 => actualBlock49 (j%32)
  | 50 => actualBlock50 (j%32)
  | 51 => actualBlock51 (j%32)
  | 52 => actualBlock52 (j%32)
  | 53 => actualBlock53 (j%32)
  | 54 => actualBlock54 (j%32)
  | 55 => actualBlock55 (j%32)
  | 56 => actualBlock56 (j%32)
  | 57 => actualBlock57 (j%32)
  | 58 => actualBlock58 (j%32)
  | 59 => actualBlock59 (j%32)
  | 60 => actualBlock60 (j%32)
  | 61 => actualBlock61 (j%32)
  | 62 => actualBlock62 (j%32)
  | 63 => actualBlock63 (j%32)
  | 64 => actualBlock64 (j%32)
  | 65 => actualBlock65 (j%32)
  | 66 => actualBlock66 (j%32)
  | 67 => actualBlock67 (j%32)
  | 68 => actualBlock68 (j%32)
  | 69 => actualBlock69 (j%32)
  | 70 => actualBlock70 (j%32)
  | 71 => actualBlock71 (j%32)
  | 72 => actualBlock72 (j%32)
  | 73 => actualBlock73 (j%32)
  | 74 => actualBlock74 (j%32)
  | 75 => actualBlock75 (j%32)
  | 76 => actualBlock76 (j%32)
  | 77 => actualBlock77 (j%32)
  | 78 => actualBlock78 (j%32)
  | 79 => actualBlock79 (j%32)
  | 80 => actualBlock80 (j%32)
  | 81 => actualBlock81 (j%32)
  | 82 => actualBlock82 (j%32)
  | 83 => actualBlock83 (j%32)
  | 84 => actualBlock84 (j%32)
  | 85 => actualBlock85 (j%32)
  | 86 => actualBlock86 (j%32)
  | 87 => actualBlock87 (j%32)
  | 88 => actualBlock88 (j%32)
  | 89 => actualBlock89 (j%32)
  | 90 => actualBlock90 (j%32)
  | 91 => actualBlock91 (j%32)
  | 92 => actualBlock92 (j%32)
  | 93 => actualBlock93 (j%32)
  | 94 => actualBlock94 (j%32)
  | 95 => actualBlock95 (j%32)
  | 96 => actualBlock96 (j%32)
  | 97 => actualBlock97 (j%32)
  | 98 => actualBlock98 (j%32)
  | 99 => actualBlock99 (j%32)
  | 100 => actualBlock100 (j%32)
  | 101 => actualBlock101 (j%32)
  | 102 => actualBlock102 (j%32)
  | 103 => actualBlock103 (j%32)
  | 104 => actualBlock104 (j%32)
  | 105 => actualBlock105 (j%32)
  | 106 => actualBlock106 (j%32)
  | 107 => actualBlock107 (j%32)
  | 108 => actualBlock108 (j%32)
  | 109 => actualBlock109 (j%32)
  | 110 => actualBlock110 (j%32)
  | 111 => actualBlock111 (j%32)
  | 112 => actualBlock112 (j%32)
  | 113 => actualBlock113 (j%32)
  | 114 => actualBlock114 (j%32)
  | 115 => actualBlock115 (j%32)
  | 116 => actualBlock116 (j%32)
  | 117 => actualBlock117 (j%32)
  | 118 => actualBlock118 (j%32)
  | 119 => actualBlock119 (j%32)
  | 120 => actualBlock120 (j%32)
  | 121 => actualBlock121 (j%32)
  | 122 => actualBlock122 (j%32)
  | 123 => actualBlock123 (j%32)
  | 124 => actualBlock124 (j%32)
  | 125 => actualBlock125 (j%32)
  | 126 => actualBlock126 (j%32)
  | 127 => actualBlock127 (j%32)
  | 128 => actualBlock128 (j%32)
  | 129 => actualBlock129 (j%32)
  | 130 => actualBlock130 (j%32)
  | 131 => actualBlock131 (j%32)
  | 132 => actualBlock132 (j%32)
  | 133 => actualBlock133 (j%32)
  | 134 => actualBlock134 (j%32)
  | 135 => actualBlock135 (j%32)
  | 136 => actualBlock136 (j%32)
  | 137 => actualBlock137 (j%32)
  | 138 => actualBlock138 (j%32)
  | 139 => actualBlock139 (j%32)
  | 140 => actualBlock140 (j%32)
  | 141 => actualBlock141 (j%32)
  | 142 => actualBlock142 (j%32)
  | 143 => actualBlock143 (j%32)
  | _ => .old 0

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusActualAssemblyBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate theorem actual_source_chunk0 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+0)))=source (i+0) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h0 : ∀ i<32, P (i+0) := by
    intro i hi
    have hd : (i+0)/32=0 := by omega
    have hm : (i+0)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_0 ⟨i,hi⟩
  have h1 : ∀ i<32, P (i+32) := by
    intro i hi
    have hd : (i+32)/32=1 := by omega
    have hm : (i+32)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_1 ⟨i,hi⟩
  have h2 : ∀ i<32, P (i+64) := by
    intro i hi
    have hd : (i+64)/32=2 := by omega
    have hm : (i+64)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_2 ⟨i,hi⟩
  have h3 : ∀ i<32, P (i+96) := by
    intro i hi
    have hd : (i+96)/32=3 := by omega
    have hm : (i+96)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_3 ⟨i,hi⟩
  have h4 : ∀ i<32, P (i+128) := by
    intro i hi
    have hd : (i+128)/32=4 := by omega
    have hm : (i+128)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_4 ⟨i,hi⟩
  have h5 : ∀ i<32, P (i+160) := by
    intro i hi
    have hd : (i+160)/32=5 := by omega
    have hm : (i+160)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_5 ⟨i,hi⟩
  have h6 : ∀ i<32, P (i+192) := by
    intro i hi
    have hd : (i+192)/32=6 := by omega
    have hm : (i+192)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_6 ⟨i,hi⟩
  have h7 : ∀ i<32, P (i+224) := by
    intro i hi
    have hd : (i+224)/32=7 := by omega
    have hm : (i+224)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_7 ⟨i,hi⟩
  have h8 : ∀ i<32, P (i+256) := by
    intro i hi
    have hd : (i+256)/32=8 := by omega
    have hm : (i+256)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_8 ⟨i,hi⟩
  have h9 : ∀ i<32, P (i+288) := by
    intro i hi
    have hd : (i+288)/32=9 := by omega
    have hm : (i+288)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_9 ⟨i,hi⟩
  have h10 : ∀ i<32, P (i+320) := by
    intro i hi
    have hd : (i+320)/32=10 := by omega
    have hm : (i+320)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_10 ⟨i,hi⟩
  have h11 : ∀ i<32, P (i+352) := by
    intro i hi
    have hd : (i+352)/32=11 := by omega
    have hm : (i+352)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_11 ⟨i,hi⟩
  exact (finite_range% P 0 [
    32 => h0,
    32 => h1,
    32 => h2,
    32 => h3,
    32 => h4,
    32 => h5,
    32 => h6,
    32 => h7,
    32 => h8,
    32 => h9,
    32 => h10,
    32 => h11
  ])
#print axioms actual_source_chunk0
compact_certificate theorem actual_tail_chunk0 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+0)))=tail (i+0) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h0 : ∀ i<32, P (i+0) := by
    intro i hi
    have hd : (i+0)/32=0 := by omega
    have hm : (i+0)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_0 ⟨i,hi⟩
  have h1 : ∀ i<32, P (i+32) := by
    intro i hi
    have hd : (i+32)/32=1 := by omega
    have hm : (i+32)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_1 ⟨i,hi⟩
  have h2 : ∀ i<32, P (i+64) := by
    intro i hi
    have hd : (i+64)/32=2 := by omega
    have hm : (i+64)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_2 ⟨i,hi⟩
  have h3 : ∀ i<32, P (i+96) := by
    intro i hi
    have hd : (i+96)/32=3 := by omega
    have hm : (i+96)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_3 ⟨i,hi⟩
  have h4 : ∀ i<32, P (i+128) := by
    intro i hi
    have hd : (i+128)/32=4 := by omega
    have hm : (i+128)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_4 ⟨i,hi⟩
  have h5 : ∀ i<32, P (i+160) := by
    intro i hi
    have hd : (i+160)/32=5 := by omega
    have hm : (i+160)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_5 ⟨i,hi⟩
  have h6 : ∀ i<32, P (i+192) := by
    intro i hi
    have hd : (i+192)/32=6 := by omega
    have hm : (i+192)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_6 ⟨i,hi⟩
  have h7 : ∀ i<32, P (i+224) := by
    intro i hi
    have hd : (i+224)/32=7 := by omega
    have hm : (i+224)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_7 ⟨i,hi⟩
  have h8 : ∀ i<32, P (i+256) := by
    intro i hi
    have hd : (i+256)/32=8 := by omega
    have hm : (i+256)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_8 ⟨i,hi⟩
  have h9 : ∀ i<32, P (i+288) := by
    intro i hi
    have hd : (i+288)/32=9 := by omega
    have hm : (i+288)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_9 ⟨i,hi⟩
  have h10 : ∀ i<32, P (i+320) := by
    intro i hi
    have hd : (i+320)/32=10 := by omega
    have hm : (i+320)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_10 ⟨i,hi⟩
  have h11 : ∀ i<32, P (i+352) := by
    intro i hi
    have hd : (i+352)/32=11 := by omega
    have hm : (i+352)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_11 ⟨i,hi⟩
  exact (finite_range% P 0 [
    32 => h0,
    32 => h1,
    32 => h2,
    32 => h3,
    32 => h4,
    32 => h5,
    32 => h6,
    32 => h7,
    32 => h8,
    32 => h9,
    32 => h10,
    32 => h11
  ])
#print axioms actual_tail_chunk0

compact_certificate theorem actual_source_chunk1 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+384)))=source (i+384) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h12 : ∀ i<32, P (i+384) := by
    intro i hi
    have hd : (i+384)/32=12 := by omega
    have hm : (i+384)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_12 ⟨i,hi⟩
  have h13 : ∀ i<32, P (i+416) := by
    intro i hi
    have hd : (i+416)/32=13 := by omega
    have hm : (i+416)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_13 ⟨i,hi⟩
  have h14 : ∀ i<32, P (i+448) := by
    intro i hi
    have hd : (i+448)/32=14 := by omega
    have hm : (i+448)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_14 ⟨i,hi⟩
  have h15 : ∀ i<32, P (i+480) := by
    intro i hi
    have hd : (i+480)/32=15 := by omega
    have hm : (i+480)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_15 ⟨i,hi⟩
  have h16 : ∀ i<32, P (i+512) := by
    intro i hi
    have hd : (i+512)/32=16 := by omega
    have hm : (i+512)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_16 ⟨i,hi⟩
  have h17 : ∀ i<32, P (i+544) := by
    intro i hi
    have hd : (i+544)/32=17 := by omega
    have hm : (i+544)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_17 ⟨i,hi⟩
  have h18 : ∀ i<32, P (i+576) := by
    intro i hi
    have hd : (i+576)/32=18 := by omega
    have hm : (i+576)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_18 ⟨i,hi⟩
  have h19 : ∀ i<32, P (i+608) := by
    intro i hi
    have hd : (i+608)/32=19 := by omega
    have hm : (i+608)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_19 ⟨i,hi⟩
  have h20 : ∀ i<32, P (i+640) := by
    intro i hi
    have hd : (i+640)/32=20 := by omega
    have hm : (i+640)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_20 ⟨i,hi⟩
  have h21 : ∀ i<32, P (i+672) := by
    intro i hi
    have hd : (i+672)/32=21 := by omega
    have hm : (i+672)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_21 ⟨i,hi⟩
  have h22 : ∀ i<32, P (i+704) := by
    intro i hi
    have hd : (i+704)/32=22 := by omega
    have hm : (i+704)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_22 ⟨i,hi⟩
  have h23 : ∀ i<32, P (i+736) := by
    intro i hi
    have hd : (i+736)/32=23 := by omega
    have hm : (i+736)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_23 ⟨i,hi⟩
  exact (finite_range% P 384 [
    32 => h12,
    32 => h13,
    32 => h14,
    32 => h15,
    32 => h16,
    32 => h17,
    32 => h18,
    32 => h19,
    32 => h20,
    32 => h21,
    32 => h22,
    32 => h23
  ])
#print axioms actual_source_chunk1
compact_certificate theorem actual_tail_chunk1 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+384)))=tail (i+384) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h12 : ∀ i<32, P (i+384) := by
    intro i hi
    have hd : (i+384)/32=12 := by omega
    have hm : (i+384)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_12 ⟨i,hi⟩
  have h13 : ∀ i<32, P (i+416) := by
    intro i hi
    have hd : (i+416)/32=13 := by omega
    have hm : (i+416)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_13 ⟨i,hi⟩
  have h14 : ∀ i<32, P (i+448) := by
    intro i hi
    have hd : (i+448)/32=14 := by omega
    have hm : (i+448)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_14 ⟨i,hi⟩
  have h15 : ∀ i<32, P (i+480) := by
    intro i hi
    have hd : (i+480)/32=15 := by omega
    have hm : (i+480)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_15 ⟨i,hi⟩
  have h16 : ∀ i<32, P (i+512) := by
    intro i hi
    have hd : (i+512)/32=16 := by omega
    have hm : (i+512)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_16 ⟨i,hi⟩
  have h17 : ∀ i<32, P (i+544) := by
    intro i hi
    have hd : (i+544)/32=17 := by omega
    have hm : (i+544)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_17 ⟨i,hi⟩
  have h18 : ∀ i<32, P (i+576) := by
    intro i hi
    have hd : (i+576)/32=18 := by omega
    have hm : (i+576)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_18 ⟨i,hi⟩
  have h19 : ∀ i<32, P (i+608) := by
    intro i hi
    have hd : (i+608)/32=19 := by omega
    have hm : (i+608)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_19 ⟨i,hi⟩
  have h20 : ∀ i<32, P (i+640) := by
    intro i hi
    have hd : (i+640)/32=20 := by omega
    have hm : (i+640)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_20 ⟨i,hi⟩
  have h21 : ∀ i<32, P (i+672) := by
    intro i hi
    have hd : (i+672)/32=21 := by omega
    have hm : (i+672)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_21 ⟨i,hi⟩
  have h22 : ∀ i<32, P (i+704) := by
    intro i hi
    have hd : (i+704)/32=22 := by omega
    have hm : (i+704)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_22 ⟨i,hi⟩
  have h23 : ∀ i<32, P (i+736) := by
    intro i hi
    have hd : (i+736)/32=23 := by omega
    have hm : (i+736)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_23 ⟨i,hi⟩
  exact (finite_range% P 384 [
    32 => h12,
    32 => h13,
    32 => h14,
    32 => h15,
    32 => h16,
    32 => h17,
    32 => h18,
    32 => h19,
    32 => h20,
    32 => h21,
    32 => h22,
    32 => h23
  ])
#print axioms actual_tail_chunk1

compact_certificate theorem actual_source_chunk2 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+768)))=source (i+768) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h24 : ∀ i<32, P (i+768) := by
    intro i hi
    have hd : (i+768)/32=24 := by omega
    have hm : (i+768)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_24 ⟨i,hi⟩
  have h25 : ∀ i<32, P (i+800) := by
    intro i hi
    have hd : (i+800)/32=25 := by omega
    have hm : (i+800)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_25 ⟨i,hi⟩
  have h26 : ∀ i<32, P (i+832) := by
    intro i hi
    have hd : (i+832)/32=26 := by omega
    have hm : (i+832)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_26 ⟨i,hi⟩
  have h27 : ∀ i<32, P (i+864) := by
    intro i hi
    have hd : (i+864)/32=27 := by omega
    have hm : (i+864)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_27 ⟨i,hi⟩
  have h28 : ∀ i<32, P (i+896) := by
    intro i hi
    have hd : (i+896)/32=28 := by omega
    have hm : (i+896)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_28 ⟨i,hi⟩
  have h29 : ∀ i<32, P (i+928) := by
    intro i hi
    have hd : (i+928)/32=29 := by omega
    have hm : (i+928)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_29 ⟨i,hi⟩
  have h30 : ∀ i<32, P (i+960) := by
    intro i hi
    have hd : (i+960)/32=30 := by omega
    have hm : (i+960)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_30 ⟨i,hi⟩
  have h31 : ∀ i<32, P (i+992) := by
    intro i hi
    have hd : (i+992)/32=31 := by omega
    have hm : (i+992)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_31 ⟨i,hi⟩
  have h32 : ∀ i<32, P (i+1024) := by
    intro i hi
    have hd : (i+1024)/32=32 := by omega
    have hm : (i+1024)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_32 ⟨i,hi⟩
  have h33 : ∀ i<32, P (i+1056) := by
    intro i hi
    have hd : (i+1056)/32=33 := by omega
    have hm : (i+1056)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_33 ⟨i,hi⟩
  have h34 : ∀ i<32, P (i+1088) := by
    intro i hi
    have hd : (i+1088)/32=34 := by omega
    have hm : (i+1088)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_34 ⟨i,hi⟩
  have h35 : ∀ i<32, P (i+1120) := by
    intro i hi
    have hd : (i+1120)/32=35 := by omega
    have hm : (i+1120)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_35 ⟨i,hi⟩
  exact (finite_range% P 768 [
    32 => h24,
    32 => h25,
    32 => h26,
    32 => h27,
    32 => h28,
    32 => h29,
    32 => h30,
    32 => h31,
    32 => h32,
    32 => h33,
    32 => h34,
    32 => h35
  ])
#print axioms actual_source_chunk2
compact_certificate theorem actual_tail_chunk2 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+768)))=tail (i+768) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h24 : ∀ i<32, P (i+768) := by
    intro i hi
    have hd : (i+768)/32=24 := by omega
    have hm : (i+768)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_24 ⟨i,hi⟩
  have h25 : ∀ i<32, P (i+800) := by
    intro i hi
    have hd : (i+800)/32=25 := by omega
    have hm : (i+800)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_25 ⟨i,hi⟩
  have h26 : ∀ i<32, P (i+832) := by
    intro i hi
    have hd : (i+832)/32=26 := by omega
    have hm : (i+832)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_26 ⟨i,hi⟩
  have h27 : ∀ i<32, P (i+864) := by
    intro i hi
    have hd : (i+864)/32=27 := by omega
    have hm : (i+864)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_27 ⟨i,hi⟩
  have h28 : ∀ i<32, P (i+896) := by
    intro i hi
    have hd : (i+896)/32=28 := by omega
    have hm : (i+896)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_28 ⟨i,hi⟩
  have h29 : ∀ i<32, P (i+928) := by
    intro i hi
    have hd : (i+928)/32=29 := by omega
    have hm : (i+928)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_29 ⟨i,hi⟩
  have h30 : ∀ i<32, P (i+960) := by
    intro i hi
    have hd : (i+960)/32=30 := by omega
    have hm : (i+960)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_30 ⟨i,hi⟩
  have h31 : ∀ i<32, P (i+992) := by
    intro i hi
    have hd : (i+992)/32=31 := by omega
    have hm : (i+992)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_31 ⟨i,hi⟩
  have h32 : ∀ i<32, P (i+1024) := by
    intro i hi
    have hd : (i+1024)/32=32 := by omega
    have hm : (i+1024)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_32 ⟨i,hi⟩
  have h33 : ∀ i<32, P (i+1056) := by
    intro i hi
    have hd : (i+1056)/32=33 := by omega
    have hm : (i+1056)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_33 ⟨i,hi⟩
  have h34 : ∀ i<32, P (i+1088) := by
    intro i hi
    have hd : (i+1088)/32=34 := by omega
    have hm : (i+1088)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_34 ⟨i,hi⟩
  have h35 : ∀ i<32, P (i+1120) := by
    intro i hi
    have hd : (i+1120)/32=35 := by omega
    have hm : (i+1120)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_35 ⟨i,hi⟩
  exact (finite_range% P 768 [
    32 => h24,
    32 => h25,
    32 => h26,
    32 => h27,
    32 => h28,
    32 => h29,
    32 => h30,
    32 => h31,
    32 => h32,
    32 => h33,
    32 => h34,
    32 => h35
  ])
#print axioms actual_tail_chunk2

compact_certificate theorem actual_source_chunk3 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+1152)))=source (i+1152) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h36 : ∀ i<32, P (i+1152) := by
    intro i hi
    have hd : (i+1152)/32=36 := by omega
    have hm : (i+1152)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_36 ⟨i,hi⟩
  have h37 : ∀ i<32, P (i+1184) := by
    intro i hi
    have hd : (i+1184)/32=37 := by omega
    have hm : (i+1184)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_37 ⟨i,hi⟩
  have h38 : ∀ i<32, P (i+1216) := by
    intro i hi
    have hd : (i+1216)/32=38 := by omega
    have hm : (i+1216)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_38 ⟨i,hi⟩
  have h39 : ∀ i<32, P (i+1248) := by
    intro i hi
    have hd : (i+1248)/32=39 := by omega
    have hm : (i+1248)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_39 ⟨i,hi⟩
  have h40 : ∀ i<32, P (i+1280) := by
    intro i hi
    have hd : (i+1280)/32=40 := by omega
    have hm : (i+1280)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_40 ⟨i,hi⟩
  have h41 : ∀ i<32, P (i+1312) := by
    intro i hi
    have hd : (i+1312)/32=41 := by omega
    have hm : (i+1312)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_41 ⟨i,hi⟩
  have h42 : ∀ i<32, P (i+1344) := by
    intro i hi
    have hd : (i+1344)/32=42 := by omega
    have hm : (i+1344)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_42 ⟨i,hi⟩
  have h43 : ∀ i<32, P (i+1376) := by
    intro i hi
    have hd : (i+1376)/32=43 := by omega
    have hm : (i+1376)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_43 ⟨i,hi⟩
  have h44 : ∀ i<32, P (i+1408) := by
    intro i hi
    have hd : (i+1408)/32=44 := by omega
    have hm : (i+1408)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_44 ⟨i,hi⟩
  have h45 : ∀ i<32, P (i+1440) := by
    intro i hi
    have hd : (i+1440)/32=45 := by omega
    have hm : (i+1440)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_45 ⟨i,hi⟩
  have h46 : ∀ i<32, P (i+1472) := by
    intro i hi
    have hd : (i+1472)/32=46 := by omega
    have hm : (i+1472)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_46 ⟨i,hi⟩
  have h47 : ∀ i<32, P (i+1504) := by
    intro i hi
    have hd : (i+1504)/32=47 := by omega
    have hm : (i+1504)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_47 ⟨i,hi⟩
  exact (finite_range% P 1152 [
    32 => h36,
    32 => h37,
    32 => h38,
    32 => h39,
    32 => h40,
    32 => h41,
    32 => h42,
    32 => h43,
    32 => h44,
    32 => h45,
    32 => h46,
    32 => h47
  ])
#print axioms actual_source_chunk3
compact_certificate theorem actual_tail_chunk3 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+1152)))=tail (i+1152) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h36 : ∀ i<32, P (i+1152) := by
    intro i hi
    have hd : (i+1152)/32=36 := by omega
    have hm : (i+1152)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_36 ⟨i,hi⟩
  have h37 : ∀ i<32, P (i+1184) := by
    intro i hi
    have hd : (i+1184)/32=37 := by omega
    have hm : (i+1184)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_37 ⟨i,hi⟩
  have h38 : ∀ i<32, P (i+1216) := by
    intro i hi
    have hd : (i+1216)/32=38 := by omega
    have hm : (i+1216)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_38 ⟨i,hi⟩
  have h39 : ∀ i<32, P (i+1248) := by
    intro i hi
    have hd : (i+1248)/32=39 := by omega
    have hm : (i+1248)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_39 ⟨i,hi⟩
  have h40 : ∀ i<32, P (i+1280) := by
    intro i hi
    have hd : (i+1280)/32=40 := by omega
    have hm : (i+1280)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_40 ⟨i,hi⟩
  have h41 : ∀ i<32, P (i+1312) := by
    intro i hi
    have hd : (i+1312)/32=41 := by omega
    have hm : (i+1312)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_41 ⟨i,hi⟩
  have h42 : ∀ i<32, P (i+1344) := by
    intro i hi
    have hd : (i+1344)/32=42 := by omega
    have hm : (i+1344)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_42 ⟨i,hi⟩
  have h43 : ∀ i<32, P (i+1376) := by
    intro i hi
    have hd : (i+1376)/32=43 := by omega
    have hm : (i+1376)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_43 ⟨i,hi⟩
  have h44 : ∀ i<32, P (i+1408) := by
    intro i hi
    have hd : (i+1408)/32=44 := by omega
    have hm : (i+1408)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_44 ⟨i,hi⟩
  have h45 : ∀ i<32, P (i+1440) := by
    intro i hi
    have hd : (i+1440)/32=45 := by omega
    have hm : (i+1440)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_45 ⟨i,hi⟩
  have h46 : ∀ i<32, P (i+1472) := by
    intro i hi
    have hd : (i+1472)/32=46 := by omega
    have hm : (i+1472)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_46 ⟨i,hi⟩
  have h47 : ∀ i<32, P (i+1504) := by
    intro i hi
    have hd : (i+1504)/32=47 := by omega
    have hm : (i+1504)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_47 ⟨i,hi⟩
  exact (finite_range% P 1152 [
    32 => h36,
    32 => h37,
    32 => h38,
    32 => h39,
    32 => h40,
    32 => h41,
    32 => h42,
    32 => h43,
    32 => h44,
    32 => h45,
    32 => h46,
    32 => h47
  ])
#print axioms actual_tail_chunk3

compact_certificate theorem actual_source_chunk4 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+1536)))=source (i+1536) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h48 : ∀ i<32, P (i+1536) := by
    intro i hi
    have hd : (i+1536)/32=48 := by omega
    have hm : (i+1536)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_48 ⟨i,hi⟩
  have h49 : ∀ i<32, P (i+1568) := by
    intro i hi
    have hd : (i+1568)/32=49 := by omega
    have hm : (i+1568)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_49 ⟨i,hi⟩
  have h50 : ∀ i<32, P (i+1600) := by
    intro i hi
    have hd : (i+1600)/32=50 := by omega
    have hm : (i+1600)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_50 ⟨i,hi⟩
  have h51 : ∀ i<32, P (i+1632) := by
    intro i hi
    have hd : (i+1632)/32=51 := by omega
    have hm : (i+1632)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_51 ⟨i,hi⟩
  have h52 : ∀ i<32, P (i+1664) := by
    intro i hi
    have hd : (i+1664)/32=52 := by omega
    have hm : (i+1664)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_52 ⟨i,hi⟩
  have h53 : ∀ i<32, P (i+1696) := by
    intro i hi
    have hd : (i+1696)/32=53 := by omega
    have hm : (i+1696)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_53 ⟨i,hi⟩
  have h54 : ∀ i<32, P (i+1728) := by
    intro i hi
    have hd : (i+1728)/32=54 := by omega
    have hm : (i+1728)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_54 ⟨i,hi⟩
  have h55 : ∀ i<32, P (i+1760) := by
    intro i hi
    have hd : (i+1760)/32=55 := by omega
    have hm : (i+1760)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_55 ⟨i,hi⟩
  have h56 : ∀ i<32, P (i+1792) := by
    intro i hi
    have hd : (i+1792)/32=56 := by omega
    have hm : (i+1792)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_56 ⟨i,hi⟩
  have h57 : ∀ i<32, P (i+1824) := by
    intro i hi
    have hd : (i+1824)/32=57 := by omega
    have hm : (i+1824)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_57 ⟨i,hi⟩
  have h58 : ∀ i<32, P (i+1856) := by
    intro i hi
    have hd : (i+1856)/32=58 := by omega
    have hm : (i+1856)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_58 ⟨i,hi⟩
  have h59 : ∀ i<32, P (i+1888) := by
    intro i hi
    have hd : (i+1888)/32=59 := by omega
    have hm : (i+1888)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_59 ⟨i,hi⟩
  exact (finite_range% P 1536 [
    32 => h48,
    32 => h49,
    32 => h50,
    32 => h51,
    32 => h52,
    32 => h53,
    32 => h54,
    32 => h55,
    32 => h56,
    32 => h57,
    32 => h58,
    32 => h59
  ])
#print axioms actual_source_chunk4
compact_certificate theorem actual_tail_chunk4 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+1536)))=tail (i+1536) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h48 : ∀ i<32, P (i+1536) := by
    intro i hi
    have hd : (i+1536)/32=48 := by omega
    have hm : (i+1536)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_48 ⟨i,hi⟩
  have h49 : ∀ i<32, P (i+1568) := by
    intro i hi
    have hd : (i+1568)/32=49 := by omega
    have hm : (i+1568)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_49 ⟨i,hi⟩
  have h50 : ∀ i<32, P (i+1600) := by
    intro i hi
    have hd : (i+1600)/32=50 := by omega
    have hm : (i+1600)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_50 ⟨i,hi⟩
  have h51 : ∀ i<32, P (i+1632) := by
    intro i hi
    have hd : (i+1632)/32=51 := by omega
    have hm : (i+1632)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_51 ⟨i,hi⟩
  have h52 : ∀ i<32, P (i+1664) := by
    intro i hi
    have hd : (i+1664)/32=52 := by omega
    have hm : (i+1664)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_52 ⟨i,hi⟩
  have h53 : ∀ i<32, P (i+1696) := by
    intro i hi
    have hd : (i+1696)/32=53 := by omega
    have hm : (i+1696)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_53 ⟨i,hi⟩
  have h54 : ∀ i<32, P (i+1728) := by
    intro i hi
    have hd : (i+1728)/32=54 := by omega
    have hm : (i+1728)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_54 ⟨i,hi⟩
  have h55 : ∀ i<32, P (i+1760) := by
    intro i hi
    have hd : (i+1760)/32=55 := by omega
    have hm : (i+1760)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_55 ⟨i,hi⟩
  have h56 : ∀ i<32, P (i+1792) := by
    intro i hi
    have hd : (i+1792)/32=56 := by omega
    have hm : (i+1792)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_56 ⟨i,hi⟩
  have h57 : ∀ i<32, P (i+1824) := by
    intro i hi
    have hd : (i+1824)/32=57 := by omega
    have hm : (i+1824)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_57 ⟨i,hi⟩
  have h58 : ∀ i<32, P (i+1856) := by
    intro i hi
    have hd : (i+1856)/32=58 := by omega
    have hm : (i+1856)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_58 ⟨i,hi⟩
  have h59 : ∀ i<32, P (i+1888) := by
    intro i hi
    have hd : (i+1888)/32=59 := by omega
    have hm : (i+1888)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_59 ⟨i,hi⟩
  exact (finite_range% P 1536 [
    32 => h48,
    32 => h49,
    32 => h50,
    32 => h51,
    32 => h52,
    32 => h53,
    32 => h54,
    32 => h55,
    32 => h56,
    32 => h57,
    32 => h58,
    32 => h59
  ])
#print axioms actual_tail_chunk4

compact_certificate theorem actual_source_chunk5 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+1920)))=source (i+1920) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h60 : ∀ i<32, P (i+1920) := by
    intro i hi
    have hd : (i+1920)/32=60 := by omega
    have hm : (i+1920)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_60 ⟨i,hi⟩
  have h61 : ∀ i<32, P (i+1952) := by
    intro i hi
    have hd : (i+1952)/32=61 := by omega
    have hm : (i+1952)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_61 ⟨i,hi⟩
  have h62 : ∀ i<32, P (i+1984) := by
    intro i hi
    have hd : (i+1984)/32=62 := by omega
    have hm : (i+1984)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_62 ⟨i,hi⟩
  have h63 : ∀ i<32, P (i+2016) := by
    intro i hi
    have hd : (i+2016)/32=63 := by omega
    have hm : (i+2016)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_63 ⟨i,hi⟩
  have h64 : ∀ i<32, P (i+2048) := by
    intro i hi
    have hd : (i+2048)/32=64 := by omega
    have hm : (i+2048)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_64 ⟨i,hi⟩
  have h65 : ∀ i<32, P (i+2080) := by
    intro i hi
    have hd : (i+2080)/32=65 := by omega
    have hm : (i+2080)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_65 ⟨i,hi⟩
  have h66 : ∀ i<32, P (i+2112) := by
    intro i hi
    have hd : (i+2112)/32=66 := by omega
    have hm : (i+2112)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_66 ⟨i,hi⟩
  have h67 : ∀ i<32, P (i+2144) := by
    intro i hi
    have hd : (i+2144)/32=67 := by omega
    have hm : (i+2144)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_67 ⟨i,hi⟩
  have h68 : ∀ i<32, P (i+2176) := by
    intro i hi
    have hd : (i+2176)/32=68 := by omega
    have hm : (i+2176)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_68 ⟨i,hi⟩
  have h69 : ∀ i<32, P (i+2208) := by
    intro i hi
    have hd : (i+2208)/32=69 := by omega
    have hm : (i+2208)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_69 ⟨i,hi⟩
  have h70 : ∀ i<32, P (i+2240) := by
    intro i hi
    have hd : (i+2240)/32=70 := by omega
    have hm : (i+2240)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_70 ⟨i,hi⟩
  have h71 : ∀ i<32, P (i+2272) := by
    intro i hi
    have hd : (i+2272)/32=71 := by omega
    have hm : (i+2272)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_71 ⟨i,hi⟩
  exact (finite_range% P 1920 [
    32 => h60,
    32 => h61,
    32 => h62,
    32 => h63,
    32 => h64,
    32 => h65,
    32 => h66,
    32 => h67,
    32 => h68,
    32 => h69,
    32 => h70,
    32 => h71
  ])
#print axioms actual_source_chunk5
compact_certificate theorem actual_tail_chunk5 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+1920)))=tail (i+1920) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h60 : ∀ i<32, P (i+1920) := by
    intro i hi
    have hd : (i+1920)/32=60 := by omega
    have hm : (i+1920)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_60 ⟨i,hi⟩
  have h61 : ∀ i<32, P (i+1952) := by
    intro i hi
    have hd : (i+1952)/32=61 := by omega
    have hm : (i+1952)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_61 ⟨i,hi⟩
  have h62 : ∀ i<32, P (i+1984) := by
    intro i hi
    have hd : (i+1984)/32=62 := by omega
    have hm : (i+1984)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_62 ⟨i,hi⟩
  have h63 : ∀ i<32, P (i+2016) := by
    intro i hi
    have hd : (i+2016)/32=63 := by omega
    have hm : (i+2016)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_63 ⟨i,hi⟩
  have h64 : ∀ i<32, P (i+2048) := by
    intro i hi
    have hd : (i+2048)/32=64 := by omega
    have hm : (i+2048)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_64 ⟨i,hi⟩
  have h65 : ∀ i<32, P (i+2080) := by
    intro i hi
    have hd : (i+2080)/32=65 := by omega
    have hm : (i+2080)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_65 ⟨i,hi⟩
  have h66 : ∀ i<32, P (i+2112) := by
    intro i hi
    have hd : (i+2112)/32=66 := by omega
    have hm : (i+2112)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_66 ⟨i,hi⟩
  have h67 : ∀ i<32, P (i+2144) := by
    intro i hi
    have hd : (i+2144)/32=67 := by omega
    have hm : (i+2144)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_67 ⟨i,hi⟩
  have h68 : ∀ i<32, P (i+2176) := by
    intro i hi
    have hd : (i+2176)/32=68 := by omega
    have hm : (i+2176)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_68 ⟨i,hi⟩
  have h69 : ∀ i<32, P (i+2208) := by
    intro i hi
    have hd : (i+2208)/32=69 := by omega
    have hm : (i+2208)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_69 ⟨i,hi⟩
  have h70 : ∀ i<32, P (i+2240) := by
    intro i hi
    have hd : (i+2240)/32=70 := by omega
    have hm : (i+2240)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_70 ⟨i,hi⟩
  have h71 : ∀ i<32, P (i+2272) := by
    intro i hi
    have hd : (i+2272)/32=71 := by omega
    have hm : (i+2272)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_71 ⟨i,hi⟩
  exact (finite_range% P 1920 [
    32 => h60,
    32 => h61,
    32 => h62,
    32 => h63,
    32 => h64,
    32 => h65,
    32 => h66,
    32 => h67,
    32 => h68,
    32 => h69,
    32 => h70,
    32 => h71
  ])
#print axioms actual_tail_chunk5

compact_certificate theorem actual_source_chunk6 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+2304)))=source (i+2304) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h72 : ∀ i<32, P (i+2304) := by
    intro i hi
    have hd : (i+2304)/32=72 := by omega
    have hm : (i+2304)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_72 ⟨i,hi⟩
  have h73 : ∀ i<32, P (i+2336) := by
    intro i hi
    have hd : (i+2336)/32=73 := by omega
    have hm : (i+2336)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_73 ⟨i,hi⟩
  have h74 : ∀ i<32, P (i+2368) := by
    intro i hi
    have hd : (i+2368)/32=74 := by omega
    have hm : (i+2368)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_74 ⟨i,hi⟩
  have h75 : ∀ i<32, P (i+2400) := by
    intro i hi
    have hd : (i+2400)/32=75 := by omega
    have hm : (i+2400)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_75 ⟨i,hi⟩
  have h76 : ∀ i<32, P (i+2432) := by
    intro i hi
    have hd : (i+2432)/32=76 := by omega
    have hm : (i+2432)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_76 ⟨i,hi⟩
  have h77 : ∀ i<32, P (i+2464) := by
    intro i hi
    have hd : (i+2464)/32=77 := by omega
    have hm : (i+2464)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_77 ⟨i,hi⟩
  have h78 : ∀ i<32, P (i+2496) := by
    intro i hi
    have hd : (i+2496)/32=78 := by omega
    have hm : (i+2496)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_78 ⟨i,hi⟩
  have h79 : ∀ i<32, P (i+2528) := by
    intro i hi
    have hd : (i+2528)/32=79 := by omega
    have hm : (i+2528)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_79 ⟨i,hi⟩
  have h80 : ∀ i<32, P (i+2560) := by
    intro i hi
    have hd : (i+2560)/32=80 := by omega
    have hm : (i+2560)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_80 ⟨i,hi⟩
  have h81 : ∀ i<32, P (i+2592) := by
    intro i hi
    have hd : (i+2592)/32=81 := by omega
    have hm : (i+2592)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_81 ⟨i,hi⟩
  have h82 : ∀ i<32, P (i+2624) := by
    intro i hi
    have hd : (i+2624)/32=82 := by omega
    have hm : (i+2624)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_82 ⟨i,hi⟩
  have h83 : ∀ i<32, P (i+2656) := by
    intro i hi
    have hd : (i+2656)/32=83 := by omega
    have hm : (i+2656)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_83 ⟨i,hi⟩
  exact (finite_range% P 2304 [
    32 => h72,
    32 => h73,
    32 => h74,
    32 => h75,
    32 => h76,
    32 => h77,
    32 => h78,
    32 => h79,
    32 => h80,
    32 => h81,
    32 => h82,
    32 => h83
  ])
#print axioms actual_source_chunk6
compact_certificate theorem actual_tail_chunk6 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+2304)))=tail (i+2304) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h72 : ∀ i<32, P (i+2304) := by
    intro i hi
    have hd : (i+2304)/32=72 := by omega
    have hm : (i+2304)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_72 ⟨i,hi⟩
  have h73 : ∀ i<32, P (i+2336) := by
    intro i hi
    have hd : (i+2336)/32=73 := by omega
    have hm : (i+2336)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_73 ⟨i,hi⟩
  have h74 : ∀ i<32, P (i+2368) := by
    intro i hi
    have hd : (i+2368)/32=74 := by omega
    have hm : (i+2368)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_74 ⟨i,hi⟩
  have h75 : ∀ i<32, P (i+2400) := by
    intro i hi
    have hd : (i+2400)/32=75 := by omega
    have hm : (i+2400)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_75 ⟨i,hi⟩
  have h76 : ∀ i<32, P (i+2432) := by
    intro i hi
    have hd : (i+2432)/32=76 := by omega
    have hm : (i+2432)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_76 ⟨i,hi⟩
  have h77 : ∀ i<32, P (i+2464) := by
    intro i hi
    have hd : (i+2464)/32=77 := by omega
    have hm : (i+2464)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_77 ⟨i,hi⟩
  have h78 : ∀ i<32, P (i+2496) := by
    intro i hi
    have hd : (i+2496)/32=78 := by omega
    have hm : (i+2496)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_78 ⟨i,hi⟩
  have h79 : ∀ i<32, P (i+2528) := by
    intro i hi
    have hd : (i+2528)/32=79 := by omega
    have hm : (i+2528)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_79 ⟨i,hi⟩
  have h80 : ∀ i<32, P (i+2560) := by
    intro i hi
    have hd : (i+2560)/32=80 := by omega
    have hm : (i+2560)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_80 ⟨i,hi⟩
  have h81 : ∀ i<32, P (i+2592) := by
    intro i hi
    have hd : (i+2592)/32=81 := by omega
    have hm : (i+2592)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_81 ⟨i,hi⟩
  have h82 : ∀ i<32, P (i+2624) := by
    intro i hi
    have hd : (i+2624)/32=82 := by omega
    have hm : (i+2624)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_82 ⟨i,hi⟩
  have h83 : ∀ i<32, P (i+2656) := by
    intro i hi
    have hd : (i+2656)/32=83 := by omega
    have hm : (i+2656)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_83 ⟨i,hi⟩
  exact (finite_range% P 2304 [
    32 => h72,
    32 => h73,
    32 => h74,
    32 => h75,
    32 => h76,
    32 => h77,
    32 => h78,
    32 => h79,
    32 => h80,
    32 => h81,
    32 => h82,
    32 => h83
  ])
#print axioms actual_tail_chunk6

compact_certificate theorem actual_source_chunk7 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+2688)))=source (i+2688) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h84 : ∀ i<32, P (i+2688) := by
    intro i hi
    have hd : (i+2688)/32=84 := by omega
    have hm : (i+2688)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_84 ⟨i,hi⟩
  have h85 : ∀ i<32, P (i+2720) := by
    intro i hi
    have hd : (i+2720)/32=85 := by omega
    have hm : (i+2720)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_85 ⟨i,hi⟩
  have h86 : ∀ i<32, P (i+2752) := by
    intro i hi
    have hd : (i+2752)/32=86 := by omega
    have hm : (i+2752)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_86 ⟨i,hi⟩
  have h87 : ∀ i<32, P (i+2784) := by
    intro i hi
    have hd : (i+2784)/32=87 := by omega
    have hm : (i+2784)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_87 ⟨i,hi⟩
  have h88 : ∀ i<32, P (i+2816) := by
    intro i hi
    have hd : (i+2816)/32=88 := by omega
    have hm : (i+2816)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_88 ⟨i,hi⟩
  have h89 : ∀ i<32, P (i+2848) := by
    intro i hi
    have hd : (i+2848)/32=89 := by omega
    have hm : (i+2848)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_89 ⟨i,hi⟩
  have h90 : ∀ i<32, P (i+2880) := by
    intro i hi
    have hd : (i+2880)/32=90 := by omega
    have hm : (i+2880)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_90 ⟨i,hi⟩
  have h91 : ∀ i<32, P (i+2912) := by
    intro i hi
    have hd : (i+2912)/32=91 := by omega
    have hm : (i+2912)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_91 ⟨i,hi⟩
  have h92 : ∀ i<32, P (i+2944) := by
    intro i hi
    have hd : (i+2944)/32=92 := by omega
    have hm : (i+2944)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_92 ⟨i,hi⟩
  have h93 : ∀ i<32, P (i+2976) := by
    intro i hi
    have hd : (i+2976)/32=93 := by omega
    have hm : (i+2976)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_93 ⟨i,hi⟩
  have h94 : ∀ i<32, P (i+3008) := by
    intro i hi
    have hd : (i+3008)/32=94 := by omega
    have hm : (i+3008)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_94 ⟨i,hi⟩
  have h95 : ∀ i<32, P (i+3040) := by
    intro i hi
    have hd : (i+3040)/32=95 := by omega
    have hm : (i+3040)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_95 ⟨i,hi⟩
  exact (finite_range% P 2688 [
    32 => h84,
    32 => h85,
    32 => h86,
    32 => h87,
    32 => h88,
    32 => h89,
    32 => h90,
    32 => h91,
    32 => h92,
    32 => h93,
    32 => h94,
    32 => h95
  ])
#print axioms actual_source_chunk7
compact_certificate theorem actual_tail_chunk7 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+2688)))=tail (i+2688) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h84 : ∀ i<32, P (i+2688) := by
    intro i hi
    have hd : (i+2688)/32=84 := by omega
    have hm : (i+2688)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_84 ⟨i,hi⟩
  have h85 : ∀ i<32, P (i+2720) := by
    intro i hi
    have hd : (i+2720)/32=85 := by omega
    have hm : (i+2720)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_85 ⟨i,hi⟩
  have h86 : ∀ i<32, P (i+2752) := by
    intro i hi
    have hd : (i+2752)/32=86 := by omega
    have hm : (i+2752)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_86 ⟨i,hi⟩
  have h87 : ∀ i<32, P (i+2784) := by
    intro i hi
    have hd : (i+2784)/32=87 := by omega
    have hm : (i+2784)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_87 ⟨i,hi⟩
  have h88 : ∀ i<32, P (i+2816) := by
    intro i hi
    have hd : (i+2816)/32=88 := by omega
    have hm : (i+2816)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_88 ⟨i,hi⟩
  have h89 : ∀ i<32, P (i+2848) := by
    intro i hi
    have hd : (i+2848)/32=89 := by omega
    have hm : (i+2848)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_89 ⟨i,hi⟩
  have h90 : ∀ i<32, P (i+2880) := by
    intro i hi
    have hd : (i+2880)/32=90 := by omega
    have hm : (i+2880)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_90 ⟨i,hi⟩
  have h91 : ∀ i<32, P (i+2912) := by
    intro i hi
    have hd : (i+2912)/32=91 := by omega
    have hm : (i+2912)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_91 ⟨i,hi⟩
  have h92 : ∀ i<32, P (i+2944) := by
    intro i hi
    have hd : (i+2944)/32=92 := by omega
    have hm : (i+2944)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_92 ⟨i,hi⟩
  have h93 : ∀ i<32, P (i+2976) := by
    intro i hi
    have hd : (i+2976)/32=93 := by omega
    have hm : (i+2976)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_93 ⟨i,hi⟩
  have h94 : ∀ i<32, P (i+3008) := by
    intro i hi
    have hd : (i+3008)/32=94 := by omega
    have hm : (i+3008)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_94 ⟨i,hi⟩
  have h95 : ∀ i<32, P (i+3040) := by
    intro i hi
    have hd : (i+3040)/32=95 := by omega
    have hm : (i+3040)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_95 ⟨i,hi⟩
  exact (finite_range% P 2688 [
    32 => h84,
    32 => h85,
    32 => h86,
    32 => h87,
    32 => h88,
    32 => h89,
    32 => h90,
    32 => h91,
    32 => h92,
    32 => h93,
    32 => h94,
    32 => h95
  ])
#print axioms actual_tail_chunk7

compact_certificate theorem actual_source_chunk8 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+3072)))=source (i+3072) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h96 : ∀ i<32, P (i+3072) := by
    intro i hi
    have hd : (i+3072)/32=96 := by omega
    have hm : (i+3072)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_96 ⟨i,hi⟩
  have h97 : ∀ i<32, P (i+3104) := by
    intro i hi
    have hd : (i+3104)/32=97 := by omega
    have hm : (i+3104)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_97 ⟨i,hi⟩
  have h98 : ∀ i<32, P (i+3136) := by
    intro i hi
    have hd : (i+3136)/32=98 := by omega
    have hm : (i+3136)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_98 ⟨i,hi⟩
  have h99 : ∀ i<32, P (i+3168) := by
    intro i hi
    have hd : (i+3168)/32=99 := by omega
    have hm : (i+3168)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_99 ⟨i,hi⟩
  have h100 : ∀ i<32, P (i+3200) := by
    intro i hi
    have hd : (i+3200)/32=100 := by omega
    have hm : (i+3200)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_100 ⟨i,hi⟩
  have h101 : ∀ i<32, P (i+3232) := by
    intro i hi
    have hd : (i+3232)/32=101 := by omega
    have hm : (i+3232)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_101 ⟨i,hi⟩
  have h102 : ∀ i<32, P (i+3264) := by
    intro i hi
    have hd : (i+3264)/32=102 := by omega
    have hm : (i+3264)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_102 ⟨i,hi⟩
  have h103 : ∀ i<32, P (i+3296) := by
    intro i hi
    have hd : (i+3296)/32=103 := by omega
    have hm : (i+3296)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_103 ⟨i,hi⟩
  have h104 : ∀ i<32, P (i+3328) := by
    intro i hi
    have hd : (i+3328)/32=104 := by omega
    have hm : (i+3328)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_104 ⟨i,hi⟩
  have h105 : ∀ i<32, P (i+3360) := by
    intro i hi
    have hd : (i+3360)/32=105 := by omega
    have hm : (i+3360)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_105 ⟨i,hi⟩
  have h106 : ∀ i<32, P (i+3392) := by
    intro i hi
    have hd : (i+3392)/32=106 := by omega
    have hm : (i+3392)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_106 ⟨i,hi⟩
  have h107 : ∀ i<32, P (i+3424) := by
    intro i hi
    have hd : (i+3424)/32=107 := by omega
    have hm : (i+3424)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_107 ⟨i,hi⟩
  exact (finite_range% P 3072 [
    32 => h96,
    32 => h97,
    32 => h98,
    32 => h99,
    32 => h100,
    32 => h101,
    32 => h102,
    32 => h103,
    32 => h104,
    32 => h105,
    32 => h106,
    32 => h107
  ])
#print axioms actual_source_chunk8
compact_certificate theorem actual_tail_chunk8 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+3072)))=tail (i+3072) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h96 : ∀ i<32, P (i+3072) := by
    intro i hi
    have hd : (i+3072)/32=96 := by omega
    have hm : (i+3072)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_96 ⟨i,hi⟩
  have h97 : ∀ i<32, P (i+3104) := by
    intro i hi
    have hd : (i+3104)/32=97 := by omega
    have hm : (i+3104)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_97 ⟨i,hi⟩
  have h98 : ∀ i<32, P (i+3136) := by
    intro i hi
    have hd : (i+3136)/32=98 := by omega
    have hm : (i+3136)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_98 ⟨i,hi⟩
  have h99 : ∀ i<32, P (i+3168) := by
    intro i hi
    have hd : (i+3168)/32=99 := by omega
    have hm : (i+3168)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_99 ⟨i,hi⟩
  have h100 : ∀ i<32, P (i+3200) := by
    intro i hi
    have hd : (i+3200)/32=100 := by omega
    have hm : (i+3200)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_100 ⟨i,hi⟩
  have h101 : ∀ i<32, P (i+3232) := by
    intro i hi
    have hd : (i+3232)/32=101 := by omega
    have hm : (i+3232)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_101 ⟨i,hi⟩
  have h102 : ∀ i<32, P (i+3264) := by
    intro i hi
    have hd : (i+3264)/32=102 := by omega
    have hm : (i+3264)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_102 ⟨i,hi⟩
  have h103 : ∀ i<32, P (i+3296) := by
    intro i hi
    have hd : (i+3296)/32=103 := by omega
    have hm : (i+3296)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_103 ⟨i,hi⟩
  have h104 : ∀ i<32, P (i+3328) := by
    intro i hi
    have hd : (i+3328)/32=104 := by omega
    have hm : (i+3328)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_104 ⟨i,hi⟩
  have h105 : ∀ i<32, P (i+3360) := by
    intro i hi
    have hd : (i+3360)/32=105 := by omega
    have hm : (i+3360)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_105 ⟨i,hi⟩
  have h106 : ∀ i<32, P (i+3392) := by
    intro i hi
    have hd : (i+3392)/32=106 := by omega
    have hm : (i+3392)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_106 ⟨i,hi⟩
  have h107 : ∀ i<32, P (i+3424) := by
    intro i hi
    have hd : (i+3424)/32=107 := by omega
    have hm : (i+3424)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_107 ⟨i,hi⟩
  exact (finite_range% P 3072 [
    32 => h96,
    32 => h97,
    32 => h98,
    32 => h99,
    32 => h100,
    32 => h101,
    32 => h102,
    32 => h103,
    32 => h104,
    32 => h105,
    32 => h106,
    32 => h107
  ])
#print axioms actual_tail_chunk8

compact_certificate theorem actual_source_chunk9 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+3456)))=source (i+3456) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h108 : ∀ i<32, P (i+3456) := by
    intro i hi
    have hd : (i+3456)/32=108 := by omega
    have hm : (i+3456)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_108 ⟨i,hi⟩
  have h109 : ∀ i<32, P (i+3488) := by
    intro i hi
    have hd : (i+3488)/32=109 := by omega
    have hm : (i+3488)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_109 ⟨i,hi⟩
  have h110 : ∀ i<32, P (i+3520) := by
    intro i hi
    have hd : (i+3520)/32=110 := by omega
    have hm : (i+3520)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_110 ⟨i,hi⟩
  have h111 : ∀ i<32, P (i+3552) := by
    intro i hi
    have hd : (i+3552)/32=111 := by omega
    have hm : (i+3552)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_111 ⟨i,hi⟩
  have h112 : ∀ i<32, P (i+3584) := by
    intro i hi
    have hd : (i+3584)/32=112 := by omega
    have hm : (i+3584)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_112 ⟨i,hi⟩
  have h113 : ∀ i<32, P (i+3616) := by
    intro i hi
    have hd : (i+3616)/32=113 := by omega
    have hm : (i+3616)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_113 ⟨i,hi⟩
  have h114 : ∀ i<32, P (i+3648) := by
    intro i hi
    have hd : (i+3648)/32=114 := by omega
    have hm : (i+3648)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_114 ⟨i,hi⟩
  have h115 : ∀ i<32, P (i+3680) := by
    intro i hi
    have hd : (i+3680)/32=115 := by omega
    have hm : (i+3680)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_115 ⟨i,hi⟩
  have h116 : ∀ i<32, P (i+3712) := by
    intro i hi
    have hd : (i+3712)/32=116 := by omega
    have hm : (i+3712)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_116 ⟨i,hi⟩
  have h117 : ∀ i<32, P (i+3744) := by
    intro i hi
    have hd : (i+3744)/32=117 := by omega
    have hm : (i+3744)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_117 ⟨i,hi⟩
  have h118 : ∀ i<32, P (i+3776) := by
    intro i hi
    have hd : (i+3776)/32=118 := by omega
    have hm : (i+3776)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_118 ⟨i,hi⟩
  have h119 : ∀ i<32, P (i+3808) := by
    intro i hi
    have hd : (i+3808)/32=119 := by omega
    have hm : (i+3808)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_119 ⟨i,hi⟩
  exact (finite_range% P 3456 [
    32 => h108,
    32 => h109,
    32 => h110,
    32 => h111,
    32 => h112,
    32 => h113,
    32 => h114,
    32 => h115,
    32 => h116,
    32 => h117,
    32 => h118,
    32 => h119
  ])
#print axioms actual_source_chunk9
compact_certificate theorem actual_tail_chunk9 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+3456)))=tail (i+3456) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h108 : ∀ i<32, P (i+3456) := by
    intro i hi
    have hd : (i+3456)/32=108 := by omega
    have hm : (i+3456)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_108 ⟨i,hi⟩
  have h109 : ∀ i<32, P (i+3488) := by
    intro i hi
    have hd : (i+3488)/32=109 := by omega
    have hm : (i+3488)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_109 ⟨i,hi⟩
  have h110 : ∀ i<32, P (i+3520) := by
    intro i hi
    have hd : (i+3520)/32=110 := by omega
    have hm : (i+3520)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_110 ⟨i,hi⟩
  have h111 : ∀ i<32, P (i+3552) := by
    intro i hi
    have hd : (i+3552)/32=111 := by omega
    have hm : (i+3552)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_111 ⟨i,hi⟩
  have h112 : ∀ i<32, P (i+3584) := by
    intro i hi
    have hd : (i+3584)/32=112 := by omega
    have hm : (i+3584)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_112 ⟨i,hi⟩
  have h113 : ∀ i<32, P (i+3616) := by
    intro i hi
    have hd : (i+3616)/32=113 := by omega
    have hm : (i+3616)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_113 ⟨i,hi⟩
  have h114 : ∀ i<32, P (i+3648) := by
    intro i hi
    have hd : (i+3648)/32=114 := by omega
    have hm : (i+3648)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_114 ⟨i,hi⟩
  have h115 : ∀ i<32, P (i+3680) := by
    intro i hi
    have hd : (i+3680)/32=115 := by omega
    have hm : (i+3680)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_115 ⟨i,hi⟩
  have h116 : ∀ i<32, P (i+3712) := by
    intro i hi
    have hd : (i+3712)/32=116 := by omega
    have hm : (i+3712)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_116 ⟨i,hi⟩
  have h117 : ∀ i<32, P (i+3744) := by
    intro i hi
    have hd : (i+3744)/32=117 := by omega
    have hm : (i+3744)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_117 ⟨i,hi⟩
  have h118 : ∀ i<32, P (i+3776) := by
    intro i hi
    have hd : (i+3776)/32=118 := by omega
    have hm : (i+3776)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_118 ⟨i,hi⟩
  have h119 : ∀ i<32, P (i+3808) := by
    intro i hi
    have hd : (i+3808)/32=119 := by omega
    have hm : (i+3808)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_119 ⟨i,hi⟩
  exact (finite_range% P 3456 [
    32 => h108,
    32 => h109,
    32 => h110,
    32 => h111,
    32 => h112,
    32 => h113,
    32 => h114,
    32 => h115,
    32 => h116,
    32 => h117,
    32 => h118,
    32 => h119
  ])
#print axioms actual_tail_chunk9

compact_certificate theorem actual_source_chunk10 : ∀ i<384, normalizedPoly (rawSourcePoly 1 (actual (i+3840)))=source (i+3840) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h120 : ∀ i<32, P (i+3840) := by
    intro i hi
    have hd : (i+3840)/32=120 := by omega
    have hm : (i+3840)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_120 ⟨i,hi⟩
  have h121 : ∀ i<32, P (i+3872) := by
    intro i hi
    have hd : (i+3872)/32=121 := by omega
    have hm : (i+3872)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_121 ⟨i,hi⟩
  have h122 : ∀ i<32, P (i+3904) := by
    intro i hi
    have hd : (i+3904)/32=122 := by omega
    have hm : (i+3904)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_122 ⟨i,hi⟩
  have h123 : ∀ i<32, P (i+3936) := by
    intro i hi
    have hd : (i+3936)/32=123 := by omega
    have hm : (i+3936)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_123 ⟨i,hi⟩
  have h124 : ∀ i<32, P (i+3968) := by
    intro i hi
    have hd : (i+3968)/32=124 := by omega
    have hm : (i+3968)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_124 ⟨i,hi⟩
  have h125 : ∀ i<32, P (i+4000) := by
    intro i hi
    have hd : (i+4000)/32=125 := by omega
    have hm : (i+4000)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_125 ⟨i,hi⟩
  have h126 : ∀ i<32, P (i+4032) := by
    intro i hi
    have hd : (i+4032)/32=126 := by omega
    have hm : (i+4032)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_126 ⟨i,hi⟩
  have h127 : ∀ i<32, P (i+4064) := by
    intro i hi
    have hd : (i+4064)/32=127 := by omega
    have hm : (i+4064)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_127 ⟨i,hi⟩
  have h128 : ∀ i<32, P (i+4096) := by
    intro i hi
    have hd : (i+4096)/32=128 := by omega
    have hm : (i+4096)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_128 ⟨i,hi⟩
  have h129 : ∀ i<32, P (i+4128) := by
    intro i hi
    have hd : (i+4128)/32=129 := by omega
    have hm : (i+4128)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_129 ⟨i,hi⟩
  have h130 : ∀ i<32, P (i+4160) := by
    intro i hi
    have hd : (i+4160)/32=130 := by omega
    have hm : (i+4160)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_130 ⟨i,hi⟩
  have h131 : ∀ i<32, P (i+4192) := by
    intro i hi
    have hd : (i+4192)/32=131 := by omega
    have hm : (i+4192)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_131 ⟨i,hi⟩
  exact (finite_range% P 3840 [
    32 => h120,
    32 => h121,
    32 => h122,
    32 => h123,
    32 => h124,
    32 => h125,
    32 => h126,
    32 => h127,
    32 => h128,
    32 => h129,
    32 => h130,
    32 => h131
  ])
#print axioms actual_source_chunk10
compact_certificate theorem actual_tail_chunk10 : ∀ i<384, normalizedPoly (rawTailPoly (actual (i+3840)))=tail (i+3840) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h120 : ∀ i<32, P (i+3840) := by
    intro i hi
    have hd : (i+3840)/32=120 := by omega
    have hm : (i+3840)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_120 ⟨i,hi⟩
  have h121 : ∀ i<32, P (i+3872) := by
    intro i hi
    have hd : (i+3872)/32=121 := by omega
    have hm : (i+3872)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_121 ⟨i,hi⟩
  have h122 : ∀ i<32, P (i+3904) := by
    intro i hi
    have hd : (i+3904)/32=122 := by omega
    have hm : (i+3904)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_122 ⟨i,hi⟩
  have h123 : ∀ i<32, P (i+3936) := by
    intro i hi
    have hd : (i+3936)/32=123 := by omega
    have hm : (i+3936)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_123 ⟨i,hi⟩
  have h124 : ∀ i<32, P (i+3968) := by
    intro i hi
    have hd : (i+3968)/32=124 := by omega
    have hm : (i+3968)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_124 ⟨i,hi⟩
  have h125 : ∀ i<32, P (i+4000) := by
    intro i hi
    have hd : (i+4000)/32=125 := by omega
    have hm : (i+4000)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_125 ⟨i,hi⟩
  have h126 : ∀ i<32, P (i+4032) := by
    intro i hi
    have hd : (i+4032)/32=126 := by omega
    have hm : (i+4032)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_126 ⟨i,hi⟩
  have h127 : ∀ i<32, P (i+4064) := by
    intro i hi
    have hd : (i+4064)/32=127 := by omega
    have hm : (i+4064)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_127 ⟨i,hi⟩
  have h128 : ∀ i<32, P (i+4096) := by
    intro i hi
    have hd : (i+4096)/32=128 := by omega
    have hm : (i+4096)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_128 ⟨i,hi⟩
  have h129 : ∀ i<32, P (i+4128) := by
    intro i hi
    have hd : (i+4128)/32=129 := by omega
    have hm : (i+4128)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_129 ⟨i,hi⟩
  have h130 : ∀ i<32, P (i+4160) := by
    intro i hi
    have hd : (i+4160)/32=130 := by omega
    have hm : (i+4160)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_130 ⟨i,hi⟩
  have h131 : ∀ i<32, P (i+4192) := by
    intro i hi
    have hd : (i+4192)/32=131 := by omega
    have hm : (i+4192)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_131 ⟨i,hi⟩
  exact (finite_range% P 3840 [
    32 => h120,
    32 => h121,
    32 => h122,
    32 => h123,
    32 => h124,
    32 => h125,
    32 => h126,
    32 => h127,
    32 => h128,
    32 => h129,
    32 => h130,
    32 => h131
  ])
#print axioms actual_tail_chunk10

compact_certificate theorem actual_source_chunk11 : ∀ i<376, normalizedPoly (rawSourcePoly 1 (actual (i+4224)))=source (i+4224) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h132 : ∀ i<32, P (i+4224) := by
    intro i hi
    have hd : (i+4224)/32=132 := by omega
    have hm : (i+4224)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_132 ⟨i,hi⟩
  have h133 : ∀ i<32, P (i+4256) := by
    intro i hi
    have hd : (i+4256)/32=133 := by omega
    have hm : (i+4256)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_133 ⟨i,hi⟩
  have h134 : ∀ i<32, P (i+4288) := by
    intro i hi
    have hd : (i+4288)/32=134 := by omega
    have hm : (i+4288)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_134 ⟨i,hi⟩
  have h135 : ∀ i<32, P (i+4320) := by
    intro i hi
    have hd : (i+4320)/32=135 := by omega
    have hm : (i+4320)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_135 ⟨i,hi⟩
  have h136 : ∀ i<32, P (i+4352) := by
    intro i hi
    have hd : (i+4352)/32=136 := by omega
    have hm : (i+4352)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_136 ⟨i,hi⟩
  have h137 : ∀ i<32, P (i+4384) := by
    intro i hi
    have hd : (i+4384)/32=137 := by omega
    have hm : (i+4384)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_137 ⟨i,hi⟩
  have h138 : ∀ i<32, P (i+4416) := by
    intro i hi
    have hd : (i+4416)/32=138 := by omega
    have hm : (i+4416)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_138 ⟨i,hi⟩
  have h139 : ∀ i<32, P (i+4448) := by
    intro i hi
    have hd : (i+4448)/32=139 := by omega
    have hm : (i+4448)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_139 ⟨i,hi⟩
  have h140 : ∀ i<32, P (i+4480) := by
    intro i hi
    have hd : (i+4480)/32=140 := by omega
    have hm : (i+4480)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_140 ⟨i,hi⟩
  have h141 : ∀ i<32, P (i+4512) := by
    intro i hi
    have hd : (i+4512)/32=141 := by omega
    have hm : (i+4512)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_141 ⟨i,hi⟩
  have h142 : ∀ i<32, P (i+4544) := by
    intro i hi
    have hd : (i+4544)/32=142 := by omega
    have hm : (i+4544)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_142 ⟨i,hi⟩
  have h143 : ∀ i<24, P (i+4576) := by
    intro i hi
    have hd : (i+4576)/32=143 := by omega
    have hm : (i+4576)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_source_143 ⟨i,hi⟩
  exact (finite_range% P 4224 [
    32 => h132,
    32 => h133,
    32 => h134,
    32 => h135,
    32 => h136,
    32 => h137,
    32 => h138,
    32 => h139,
    32 => h140,
    32 => h141,
    32 => h142,
    24 => h143
  ])
#print axioms actual_source_chunk11
compact_certificate theorem actual_tail_chunk11 : ∀ i<376, normalizedPoly (rawTailPoly (actual (i+4224)))=tail (i+4224) := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h132 : ∀ i<32, P (i+4224) := by
    intro i hi
    have hd : (i+4224)/32=132 := by omega
    have hm : (i+4224)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_132 ⟨i,hi⟩
  have h133 : ∀ i<32, P (i+4256) := by
    intro i hi
    have hd : (i+4256)/32=133 := by omega
    have hm : (i+4256)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_133 ⟨i,hi⟩
  have h134 : ∀ i<32, P (i+4288) := by
    intro i hi
    have hd : (i+4288)/32=134 := by omega
    have hm : (i+4288)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_134 ⟨i,hi⟩
  have h135 : ∀ i<32, P (i+4320) := by
    intro i hi
    have hd : (i+4320)/32=135 := by omega
    have hm : (i+4320)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_135 ⟨i,hi⟩
  have h136 : ∀ i<32, P (i+4352) := by
    intro i hi
    have hd : (i+4352)/32=136 := by omega
    have hm : (i+4352)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_136 ⟨i,hi⟩
  have h137 : ∀ i<32, P (i+4384) := by
    intro i hi
    have hd : (i+4384)/32=137 := by omega
    have hm : (i+4384)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_137 ⟨i,hi⟩
  have h138 : ∀ i<32, P (i+4416) := by
    intro i hi
    have hd : (i+4416)/32=138 := by omega
    have hm : (i+4416)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_138 ⟨i,hi⟩
  have h139 : ∀ i<32, P (i+4448) := by
    intro i hi
    have hd : (i+4448)/32=139 := by omega
    have hm : (i+4448)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_139 ⟨i,hi⟩
  have h140 : ∀ i<32, P (i+4480) := by
    intro i hi
    have hd : (i+4480)/32=140 := by omega
    have hm : (i+4480)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_140 ⟨i,hi⟩
  have h141 : ∀ i<32, P (i+4512) := by
    intro i hi
    have hd : (i+4512)/32=141 := by omega
    have hm : (i+4512)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_141 ⟨i,hi⟩
  have h142 : ∀ i<32, P (i+4544) := by
    intro i hi
    have hd : (i+4544)/32=142 := by omega
    have hm : (i+4544)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_142 ⟨i,hi⟩
  have h143 : ∀ i<24, P (i+4576) := by
    intro i hi
    have hd : (i+4576)/32=143 := by omega
    have hm : (i+4576)%32=i := by omega
    simpa only [P,actual,hd,hm] using actual_tail_143 ⟨i,hi⟩
  exact (finite_range% P 4224 [
    32 => h132,
    32 => h133,
    32 => h134,
    32 => h135,
    32 => h136,
    32 => h137,
    32 => h138,
    32 => h139,
    32 => h140,
    32 => h141,
    32 => h142,
    24 => h143
  ])
#print axioms actual_tail_chunk11

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

