module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusTailStagesChapterV1

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

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusActualCheckIndexDataSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate def actualBlock98 : ℕ → SourceRow
  | 0 => auxSource829
  | 1 => auxSource820
  | 2 => auxSource830
  | 3 => auxSource819
  | 4 => auxSource831
  | 5 => auxSource818
  | 6 => auxSource832
  | 7 => auxSource817
  | 8 => auxSource833
  | 9 => auxSource816
  | 10 => auxSource2148
  | 11 => auxSource843
  | 12 => auxSource842
  | 13 => auxSource844
  | 14 => auxSource841
  | 15 => auxSource845
  | 16 => auxSource840
  | 17 => auxSource846
  | 18 => auxSource839
  | 19 => auxSource847
  | 20 => auxSource838
  | 21 => auxSource848
  | 22 => auxSource837
  | 23 => auxSource849
  | 24 => auxSource836
  | 25 => auxSource850
  | 26 => auxSource835
  | 27 => auxSource851
  | 28 => auxSource834
  | 29 => auxSource2149
  | 30 => auxSource855
  | 31 => auxSource854
  | _ => .old 0



compact_certificate def actualBlock99 : ℕ → SourceRow
  | 0 => auxSource856
  | 1 => auxSource853
  | 2 => auxSource857
  | 3 => auxSource852
  | 4 => auxSource2150
  | 5 => auxSource867
  | 6 => auxSource866
  | 7 => auxSource868
  | 8 => auxSource865
  | 9 => auxSource869
  | 10 => auxSource864
  | 11 => auxSource870
  | 12 => auxSource863
  | 13 => auxSource871
  | 14 => auxSource862
  | 15 => auxSource872
  | 16 => auxSource861
  | 17 => auxSource873
  | 18 => auxSource860
  | 19 => auxSource874
  | 20 => auxSource859
  | 21 => auxSource875
  | 22 => auxSource858
  | 23 => auxSource2151
  | 24 => auxSource879
  | 25 => auxSource878
  | 26 => auxSource880
  | 27 => auxSource877
  | 28 => auxSource881
  | 29 => auxSource876
  | 30 => auxSource2152
  | 31 => auxSource885
  | _ => .old 0



compact_certificate def actualBlock100 : ℕ → SourceRow
  | 0 => auxSource884
  | 1 => auxSource886
  | 2 => auxSource883
  | 3 => auxSource887
  | 4 => auxSource882
  | 5 => auxSource2153
  | 6 => auxSource891
  | 7 => auxSource890
  | 8 => auxSource892
  | 9 => auxSource889
  | 10 => auxSource893
  | 11 => auxSource888
  | 12 => auxSource2154
  | 13 => auxSource895
  | 14 => auxSource894
  | 15 => auxSource896
  | 16 => auxSource897
  | 17 => auxSource898
  | 18 => auxSource899
  | 19 => auxSource900
  | 20 => auxSource901
  | 21 => auxSource902
  | 22 => auxSource903
  | 23 => auxSource904
  | 24 => auxSource905
  | 25 => auxSource906
  | 26 => auxSource907
  | 27 => auxSource908
  | 28 => auxSource909
  | 29 => auxSource910
  | 30 => auxSource911
  | 31 => auxSource912
  | _ => .old 0

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusActualCheckIndexBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate theorem actual_source_98_part0 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock98 (i.val+0)))=source ((i.val+0)+3136) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_98_part0
compact_certificate theorem actual_tail_98_part0 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock98 (i.val+0)))=tail ((i.val+0)+3136) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_98_part0

compact_certificate theorem actual_source_98_part1 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock98 (i.val+8)))=source ((i.val+8)+3136) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_98_part1
compact_certificate theorem actual_tail_98_part1 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock98 (i.val+8)))=tail ((i.val+8)+3136) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_98_part1

compact_certificate theorem actual_source_98_part2 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock98 (i.val+16)))=source ((i.val+16)+3136) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_98_part2
compact_certificate theorem actual_tail_98_part2 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock98 (i.val+16)))=tail ((i.val+16)+3136) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_98_part2

compact_certificate theorem actual_source_98_part3 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock98 (i.val+24)))=source ((i.val+24)+3136) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_98_part3
compact_certificate theorem actual_tail_98_part3 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock98 (i.val+24)))=tail ((i.val+24)+3136) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_98_part3

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end

section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate theorem actual_source_99_part0 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock99 (i.val+0)))=source ((i.val+0)+3168) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part0
compact_certificate theorem actual_tail_99_part0 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock99 (i.val+0)))=tail ((i.val+0)+3168) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part0

compact_certificate theorem actual_source_99_part1_single0 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 8))=source 3176 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part1_single0
compact_certificate theorem actual_tail_99_part1_single0 :
    normalizedPoly (rawTailPoly (actualBlock99 8))=tail 3176 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part1_single0

compact_certificate theorem actual_source_99_part1_single1 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 9))=source 3177 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part1_single1
compact_certificate theorem actual_tail_99_part1_single1 :
    normalizedPoly (rawTailPoly (actualBlock99 9))=tail 3177 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part1_single1

compact_certificate theorem actual_source_99_part1_single2 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 10))=source 3178 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part1_single2
compact_certificate theorem actual_tail_99_part1_single2 :
    normalizedPoly (rawTailPoly (actualBlock99 10))=tail 3178 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part1_single2

compact_certificate theorem actual_source_99_part1_single3 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 11))=source 3179 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part1_single3
compact_certificate theorem actual_tail_99_part1_single3 :
    normalizedPoly (rawTailPoly (actualBlock99 11))=tail 3179 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part1_single3

compact_certificate theorem actual_source_99_part1_single4 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 12))=source 3180 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part1_single4
compact_certificate theorem actual_tail_99_part1_single4 :
    normalizedPoly (rawTailPoly (actualBlock99 12))=tail 3180 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part1_single4

compact_certificate theorem actual_source_99_part1_single5 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 13))=source 3181 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part1_single5
compact_certificate theorem actual_tail_99_part1_single5 :
    normalizedPoly (rawTailPoly (actualBlock99 13))=tail 3181 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part1_single5

compact_certificate theorem actual_source_99_part1_single6 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 14))=source 3182 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part1_single6
compact_certificate theorem actual_tail_99_part1_single6 :
    normalizedPoly (rawTailPoly (actualBlock99 14))=tail 3182 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part1_single6

compact_certificate theorem actual_source_99_part1_single7 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 15))=source 3183 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part1_single7
compact_certificate theorem actual_tail_99_part1_single7 :
    normalizedPoly (rawTailPoly (actualBlock99 15))=tail 3183 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part1_single7

compact_certificate theorem actual_source_99_part1 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock99 (i.val+8)))=source ((i.val+8)+3168) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock99 j))=source (j+3168)
  have h : ∀ i<8, P (i+8) := (finite_range% P 8 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part1_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part1_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part1_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part1_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part1_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part1_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part1_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part1_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_99_part1
compact_certificate theorem actual_tail_99_part1 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock99 (i.val+8)))=tail ((i.val+8)+3168) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock99 j))=tail (j+3168)
  have h : ∀ i<8, P (i+8) := (finite_range% P 8 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part1_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part1_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part1_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part1_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part1_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part1_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part1_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part1_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_99_part1

compact_certificate theorem actual_source_99_part2_single0 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 16))=source 3184 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part2_single0
compact_certificate theorem actual_tail_99_part2_single0 :
    normalizedPoly (rawTailPoly (actualBlock99 16))=tail 3184 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part2_single0

compact_certificate theorem actual_source_99_part2_single1 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 17))=source 3185 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part2_single1
compact_certificate theorem actual_tail_99_part2_single1 :
    normalizedPoly (rawTailPoly (actualBlock99 17))=tail 3185 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part2_single1

compact_certificate theorem actual_source_99_part2_single2 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 18))=source 3186 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part2_single2
compact_certificate theorem actual_tail_99_part2_single2 :
    normalizedPoly (rawTailPoly (actualBlock99 18))=tail 3186 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part2_single2

compact_certificate theorem actual_source_99_part2_single3 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 19))=source 3187 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part2_single3
compact_certificate theorem actual_tail_99_part2_single3 :
    normalizedPoly (rawTailPoly (actualBlock99 19))=tail 3187 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part2_single3

compact_certificate theorem actual_source_99_part2_single4 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 20))=source 3188 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part2_single4
compact_certificate theorem actual_tail_99_part2_single4 :
    normalizedPoly (rawTailPoly (actualBlock99 20))=tail 3188 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part2_single4

compact_certificate theorem actual_source_99_part2_single5 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 21))=source 3189 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part2_single5
compact_certificate theorem actual_tail_99_part2_single5 :
    normalizedPoly (rawTailPoly (actualBlock99 21))=tail 3189 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part2_single5

compact_certificate theorem actual_source_99_part2_single6 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 22))=source 3190 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part2_single6
compact_certificate theorem actual_tail_99_part2_single6 :
    normalizedPoly (rawTailPoly (actualBlock99 22))=tail 3190 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part2_single6

compact_certificate theorem actual_source_99_part2_single7 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 23))=source 3191 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part2_single7
compact_certificate theorem actual_tail_99_part2_single7 :
    normalizedPoly (rawTailPoly (actualBlock99 23))=tail 3191 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part2_single7

compact_certificate theorem actual_source_99_part2 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock99 (i.val+16)))=source ((i.val+16)+3168) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock99 j))=source (j+3168)
  have h : ∀ i<8, P (i+16) := (finite_range% P 16 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part2_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part2_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part2_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part2_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part2_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part2_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part2_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part2_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_99_part2
compact_certificate theorem actual_tail_99_part2 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock99 (i.val+16)))=tail ((i.val+16)+3168) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock99 j))=tail (j+3168)
  have h : ∀ i<8, P (i+16) := (finite_range% P 16 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part2_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part2_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part2_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part2_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part2_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part2_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part2_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part2_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_99_part2

compact_certificate theorem actual_source_99_part3_single0 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 24))=source 3192 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part3_single0
compact_certificate theorem actual_tail_99_part3_single0 :
    normalizedPoly (rawTailPoly (actualBlock99 24))=tail 3192 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part3_single0

compact_certificate theorem actual_source_99_part3_single1 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 25))=source 3193 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part3_single1
compact_certificate theorem actual_tail_99_part3_single1 :
    normalizedPoly (rawTailPoly (actualBlock99 25))=tail 3193 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part3_single1

compact_certificate theorem actual_source_99_part3_single2 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 26))=source 3194 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part3_single2
compact_certificate theorem actual_tail_99_part3_single2 :
    normalizedPoly (rawTailPoly (actualBlock99 26))=tail 3194 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part3_single2

compact_certificate theorem actual_source_99_part3_single3 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 27))=source 3195 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part3_single3
compact_certificate theorem actual_tail_99_part3_single3 :
    normalizedPoly (rawTailPoly (actualBlock99 27))=tail 3195 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part3_single3

compact_certificate theorem actual_source_99_part3_single4 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 28))=source 3196 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part3_single4
compact_certificate theorem actual_tail_99_part3_single4 :
    normalizedPoly (rawTailPoly (actualBlock99 28))=tail 3196 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part3_single4

compact_certificate theorem actual_source_99_part3_single5 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 29))=source 3197 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part3_single5
compact_certificate theorem actual_tail_99_part3_single5 :
    normalizedPoly (rawTailPoly (actualBlock99 29))=tail 3197 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part3_single5

compact_certificate theorem actual_source_99_part3_single6 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 30))=source 3198 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part3_single6
compact_certificate theorem actual_tail_99_part3_single6 :
    normalizedPoly (rawTailPoly (actualBlock99 30))=tail 3198 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part3_single6

compact_certificate theorem actual_source_99_part3_single7 :
    normalizedPoly (rawSourcePoly 1 (actualBlock99 31))=source 3199 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_99_part3_single7
compact_certificate theorem actual_tail_99_part3_single7 :
    normalizedPoly (rawTailPoly (actualBlock99 31))=tail 3199 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_99_part3_single7

compact_certificate theorem actual_source_99_part3 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock99 (i.val+24)))=source ((i.val+24)+3168) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock99 j))=source (j+3168)
  have h : ∀ i<8, P (i+24) := (finite_range% P 24 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part3_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part3_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part3_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part3_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part3_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part3_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part3_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_99_part3_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_99_part3
compact_certificate theorem actual_tail_99_part3 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock99 (i.val+24)))=tail ((i.val+24)+3168) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock99 j))=tail (j+3168)
  have h : ∀ i<8, P (i+24) := (finite_range% P 24 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part3_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part3_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part3_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part3_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part3_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part3_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part3_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_99_part3_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_99_part3

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end

section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate theorem actual_source_100_part0_single0 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 0))=source 3200 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part0_single0
compact_certificate theorem actual_tail_100_part0_single0 :
    normalizedPoly (rawTailPoly (actualBlock100 0))=tail 3200 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part0_single0

compact_certificate theorem actual_source_100_part0_single1 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 1))=source 3201 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part0_single1
compact_certificate theorem actual_tail_100_part0_single1 :
    normalizedPoly (rawTailPoly (actualBlock100 1))=tail 3201 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part0_single1

compact_certificate theorem actual_source_100_part0_single2 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 2))=source 3202 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part0_single2
compact_certificate theorem actual_tail_100_part0_single2 :
    normalizedPoly (rawTailPoly (actualBlock100 2))=tail 3202 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part0_single2

compact_certificate theorem actual_source_100_part0_single3 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 3))=source 3203 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part0_single3
compact_certificate theorem actual_tail_100_part0_single3 :
    normalizedPoly (rawTailPoly (actualBlock100 3))=tail 3203 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part0_single3

compact_certificate theorem actual_source_100_part0_single4 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 4))=source 3204 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part0_single4
compact_certificate theorem actual_tail_100_part0_single4 :
    normalizedPoly (rawTailPoly (actualBlock100 4))=tail 3204 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part0_single4

compact_certificate theorem actual_source_100_part0_single5 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 5))=source 3205 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part0_single5
compact_certificate theorem actual_tail_100_part0_single5 :
    normalizedPoly (rawTailPoly (actualBlock100 5))=tail 3205 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part0_single5

compact_certificate theorem actual_source_100_part0_single6 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 6))=source 3206 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part0_single6
compact_certificate theorem actual_tail_100_part0_single6 :
    normalizedPoly (rawTailPoly (actualBlock100 6))=tail 3206 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part0_single6

compact_certificate theorem actual_source_100_part0_single7 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 7))=source 3207 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part0_single7
compact_certificate theorem actual_tail_100_part0_single7 :
    normalizedPoly (rawTailPoly (actualBlock100 7))=tail 3207 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part0_single7

compact_certificate theorem actual_source_100_part0 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock100 (i.val+0)))=source ((i.val+0)+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock100 j))=source (j+3200)
  have h : ∀ i<8, P (i+0) := (finite_range% P 0 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part0_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part0_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part0_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part0_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part0_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part0_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part0_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part0_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_100_part0
compact_certificate theorem actual_tail_100_part0 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock100 (i.val+0)))=tail ((i.val+0)+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock100 j))=tail (j+3200)
  have h : ∀ i<8, P (i+0) := (finite_range% P 0 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part0_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part0_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part0_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part0_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part0_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part0_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part0_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part0_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_100_part0

compact_certificate theorem actual_source_100_part1_single0 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 8))=source 3208 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part1_single0
compact_certificate theorem actual_tail_100_part1_single0 :
    normalizedPoly (rawTailPoly (actualBlock100 8))=tail 3208 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part1_single0

compact_certificate theorem actual_source_100_part1_single1 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 9))=source 3209 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part1_single1
compact_certificate theorem actual_tail_100_part1_single1 :
    normalizedPoly (rawTailPoly (actualBlock100 9))=tail 3209 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part1_single1

compact_certificate theorem actual_source_100_part1_single2 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 10))=source 3210 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part1_single2
compact_certificate theorem actual_tail_100_part1_single2 :
    normalizedPoly (rawTailPoly (actualBlock100 10))=tail 3210 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part1_single2

compact_certificate theorem actual_source_100_part1_single3 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 11))=source 3211 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part1_single3
compact_certificate theorem actual_tail_100_part1_single3 :
    normalizedPoly (rawTailPoly (actualBlock100 11))=tail 3211 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part1_single3

compact_certificate theorem actual_source_100_part1_single4 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 12))=source 3212 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part1_single4
compact_certificate theorem actual_tail_100_part1_single4 :
    normalizedPoly (rawTailPoly (actualBlock100 12))=tail 3212 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part1_single4

compact_certificate theorem actual_source_100_part1_single5 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 13))=source 3213 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part1_single5
compact_certificate theorem actual_tail_100_part1_single5 :
    normalizedPoly (rawTailPoly (actualBlock100 13))=tail 3213 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part1_single5

compact_certificate theorem actual_source_100_part1_single6 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 14))=source 3214 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part1_single6
compact_certificate theorem actual_tail_100_part1_single6 :
    normalizedPoly (rawTailPoly (actualBlock100 14))=tail 3214 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part1_single6

compact_certificate theorem actual_source_100_part1_single7 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 15))=source 3215 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part1_single7
compact_certificate theorem actual_tail_100_part1_single7 :
    normalizedPoly (rawTailPoly (actualBlock100 15))=tail 3215 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part1_single7

compact_certificate theorem actual_source_100_part1 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock100 (i.val+8)))=source ((i.val+8)+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock100 j))=source (j+3200)
  have h : ∀ i<8, P (i+8) := (finite_range% P 8 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part1_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part1_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part1_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part1_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part1_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part1_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part1_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part1_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_100_part1
compact_certificate theorem actual_tail_100_part1 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock100 (i.val+8)))=tail ((i.val+8)+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock100 j))=tail (j+3200)
  have h : ∀ i<8, P (i+8) := (finite_range% P 8 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part1_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part1_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part1_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part1_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part1_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part1_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part1_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part1_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_100_part1

compact_certificate theorem actual_source_100_part2_single0 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 16))=source 3216 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part2_single0
compact_certificate theorem actual_tail_100_part2_single0 :
    normalizedPoly (rawTailPoly (actualBlock100 16))=tail 3216 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part2_single0

compact_certificate theorem actual_source_100_part2_single1 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 17))=source 3217 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part2_single1
compact_certificate theorem actual_tail_100_part2_single1 :
    normalizedPoly (rawTailPoly (actualBlock100 17))=tail 3217 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part2_single1

compact_certificate theorem actual_source_100_part2_single2 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 18))=source 3218 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part2_single2
compact_certificate theorem actual_tail_100_part2_single2 :
    normalizedPoly (rawTailPoly (actualBlock100 18))=tail 3218 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part2_single2

compact_certificate theorem actual_source_100_part2_single3 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 19))=source 3219 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part2_single3
compact_certificate theorem actual_tail_100_part2_single3 :
    normalizedPoly (rawTailPoly (actualBlock100 19))=tail 3219 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part2_single3

compact_certificate theorem actual_source_100_part2_single4 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 20))=source 3220 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part2_single4
compact_certificate theorem actual_tail_100_part2_single4 :
    normalizedPoly (rawTailPoly (actualBlock100 20))=tail 3220 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part2_single4

compact_certificate theorem actual_source_100_part2_single5 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 21))=source 3221 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part2_single5
compact_certificate theorem actual_tail_100_part2_single5 :
    normalizedPoly (rawTailPoly (actualBlock100 21))=tail 3221 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part2_single5

compact_certificate theorem actual_source_100_part2_single6 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 22))=source 3222 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part2_single6
compact_certificate theorem actual_tail_100_part2_single6 :
    normalizedPoly (rawTailPoly (actualBlock100 22))=tail 3222 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part2_single6

compact_certificate theorem actual_source_100_part2_single7 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 23))=source 3223 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part2_single7
compact_certificate theorem actual_tail_100_part2_single7 :
    normalizedPoly (rawTailPoly (actualBlock100 23))=tail 3223 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part2_single7

compact_certificate theorem actual_source_100_part2 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock100 (i.val+16)))=source ((i.val+16)+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock100 j))=source (j+3200)
  have h : ∀ i<8, P (i+16) := (finite_range% P 16 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part2_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part2_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part2_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part2_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part2_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part2_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part2_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part2_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_100_part2
compact_certificate theorem actual_tail_100_part2 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock100 (i.val+16)))=tail ((i.val+16)+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock100 j))=tail (j+3200)
  have h : ∀ i<8, P (i+16) := (finite_range% P 16 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part2_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part2_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part2_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part2_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part2_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part2_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part2_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part2_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_100_part2

compact_certificate theorem actual_source_100_part3_single0 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 24))=source 3224 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part3_single0
compact_certificate theorem actual_tail_100_part3_single0 :
    normalizedPoly (rawTailPoly (actualBlock100 24))=tail 3224 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part3_single0

compact_certificate theorem actual_source_100_part3_single1 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 25))=source 3225 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part3_single1
compact_certificate theorem actual_tail_100_part3_single1 :
    normalizedPoly (rawTailPoly (actualBlock100 25))=tail 3225 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part3_single1

compact_certificate theorem actual_source_100_part3_single2 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 26))=source 3226 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part3_single2
compact_certificate theorem actual_tail_100_part3_single2 :
    normalizedPoly (rawTailPoly (actualBlock100 26))=tail 3226 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part3_single2

compact_certificate theorem actual_source_100_part3_single3 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 27))=source 3227 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part3_single3
compact_certificate theorem actual_tail_100_part3_single3 :
    normalizedPoly (rawTailPoly (actualBlock100 27))=tail 3227 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part3_single3

compact_certificate theorem actual_source_100_part3_single4 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 28))=source 3228 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part3_single4
compact_certificate theorem actual_tail_100_part3_single4 :
    normalizedPoly (rawTailPoly (actualBlock100 28))=tail 3228 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part3_single4

compact_certificate theorem actual_source_100_part3_single5 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 29))=source 3229 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part3_single5
compact_certificate theorem actual_tail_100_part3_single5 :
    normalizedPoly (rawTailPoly (actualBlock100 29))=tail 3229 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part3_single5

compact_certificate theorem actual_source_100_part3_single6 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 30))=source 3230 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part3_single6
compact_certificate theorem actual_tail_100_part3_single6 :
    normalizedPoly (rawTailPoly (actualBlock100 30))=tail 3230 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part3_single6

compact_certificate theorem actual_source_100_part3_single7 :
    normalizedPoly (rawSourcePoly 1 (actualBlock100 31))=source 3231 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_100_part3_single7
compact_certificate theorem actual_tail_100_part3_single7 :
    normalizedPoly (rawTailPoly (actualBlock100 31))=tail 3231 := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_tail_100_part3_single7

compact_certificate theorem actual_source_100_part3 : ∀ i : Fin 8,
    normalizedPoly (rawSourcePoly 1 (actualBlock100 (i.val+24)))=source ((i.val+24)+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock100 j))=source (j+3200)
  have h : ∀ i<8, P (i+24) := (finite_range% P 24 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part3_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part3_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part3_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part3_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part3_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part3_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part3_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_source_100_part3_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_100_part3
compact_certificate theorem actual_tail_100_part3 : ∀ i : Fin 8,
    normalizedPoly (rawTailPoly (actualBlock100 (i.val+24)))=tail ((i.val+24)+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock100 j))=tail (j+3200)
  have h : ∀ i<8, P (i+24) := (finite_range% P 24 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part3_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part3_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part3_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part3_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part3_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part3_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part3_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton actual_tail_100_part3_single7)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_100_part3

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusActualCheckBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate def actualBlock0 : ℕ → SourceRow
  | 0 => auxSource2486
  | 1 => auxSource2487
  | 2 => auxSource2488
  | 3 => auxSource2489
  | 4 => auxSource2490
  | 5 => auxSource2491
  | 6 => auxSource2492
  | 7 => auxSource2493
  | 8 => auxSource2494
  | 9 => auxSource2495
  | 10 => auxSource2496
  | 11 => auxSource2497
  | 12 => auxSource2498
  | 13 => auxSource2499
  | 14 => auxSource2500
  | 15 => auxSource2501
  | 16 => auxSource2502
  | 17 => auxSource2503
  | 18 => auxSource2504
  | 19 => auxSource2505
  | 20 => auxSource2506
  | 21 => auxSource2507
  | 22 => auxSource2508
  | 23 => auxSource2509
  | 24 => auxSource4410
  | 25 => auxSource2510
  | 26 => auxSource2511
  | 27 => auxSource2512
  | 28 => auxSource2513
  | 29 => auxSource2514
  | 30 => auxSource2515
  | 31 => auxSource2516
  | _ => .old 0

compact_certificate theorem actual_source_0 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock0 i.val))=source (i.val+0) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_0 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock0 i.val))=tail (i.val+0) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_0
#print axioms actual_tail_0

compact_certificate def actualBlock1 : ℕ → SourceRow
  | 0 => auxSource2517
  | 1 => auxSource2518
  | 2 => auxSource2519
  | 3 => auxSource2520
  | 4 => auxSource2521
  | 5 => auxSource2522
  | 6 => auxSource2523
  | 7 => auxSource2524
  | 8 => auxSource2525
  | 9 => auxSource2526
  | 10 => auxSource2527
  | 11 => auxSource2528
  | 12 => auxSource2529
  | 13 => auxSource2530
  | 14 => auxSource2531
  | 15 => auxSource2532
  | 16 => auxSource2533
  | 17 => auxSource4401
  | 18 => auxSource4180
  | 19 => auxSource4181
  | 20 => auxSource4182
  | 21 => auxSource4183
  | 22 => auxSource4184
  | 23 => auxSource4185
  | 24 => auxSource4186
  | 25 => auxSource4187
  | 26 => auxSource4188
  | 27 => auxSource4189
  | 28 => auxSource4190
  | 29 => auxSource4191
  | 30 => auxSource2454
  | 31 => auxSource2455
  | _ => .old 0

compact_certificate theorem actual_source_1 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock1 i.val))=source (i.val+32) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_1 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock1 i.val))=tail (i.val+32) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_1
#print axioms actual_tail_1

compact_certificate def actualBlock2 : ℕ → SourceRow
  | 0 => auxSource2456
  | 1 => auxSource2457
  | 2 => auxSource2458
  | 3 => auxSource2459
  | 4 => auxSource2460
  | 5 => auxSource2461
  | 6 => auxSource2462
  | 7 => auxSource2463
  | 8 => auxSource2464
  | 9 => auxSource2465
  | 10 => auxSource2466
  | 11 => auxSource2467
  | 12 => auxSource4440
  | 13 => auxSource4047
  | 14 => auxSource4048
  | 15 => auxSource4049
  | 16 => auxSource4050
  | 17 => auxSource4051
  | 18 => auxSource4052
  | 19 => auxSource4053
  | 20 => auxSource4054
  | 21 => auxSource4055
  | 22 => auxSource4056
  | 23 => auxSource4057
  | 24 => auxSource4058
  | 25 => auxSource4059
  | 26 => auxSource4060
  | 27 => auxSource4061
  | 28 => auxSource4062
  | 29 => auxSource4063
  | 30 => auxSource4064
  | 31 => auxSource4065
  | _ => .old 0

compact_certificate theorem actual_source_2 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock2 i.val))=source (i.val+64) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_2 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock2 i.val))=tail (i.val+64) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_2
#print axioms actual_tail_2

compact_certificate def actualBlock3 : ℕ → SourceRow
  | 0 => auxSource4066
  | 1 => auxSource4067
  | 2 => auxSource4068
  | 3 => auxSource4069
  | 4 => auxSource4070
  | 5 => auxSource4071
  | 6 => auxSource4072
  | 7 => auxSource4073
  | 8 => auxSource4074
  | 9 => auxSource4075
  | 10 => auxSource4076
  | 11 => auxSource4077
  | 12 => auxSource4078
  | 13 => auxSource4079
  | 14 => auxSource4080
  | 15 => auxSource4081
  | 16 => auxSource4082
  | 17 => auxSource4083
  | 18 => auxSource4084
  | 19 => auxSource4085
  | 20 => auxSource4086
  | 21 => auxSource4087
  | 22 => auxSource4088
  | 23 => auxSource4089
  | 24 => auxSource4090
  | 25 => auxSource4091
  | 26 => auxSource4092
  | 27 => auxSource4093
  | 28 => auxSource4094
  | 29 => auxSource4095
  | 30 => auxSource4096
  | 31 => auxSource4097
  | _ => .old 0

compact_certificate theorem actual_source_3 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock3 i.val))=source (i.val+96) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_3 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock3 i.val))=tail (i.val+96) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_3
#print axioms actual_tail_3

compact_certificate def actualBlock4 : ℕ → SourceRow
  | 0 => auxSource4098
  | 1 => auxSource4099
  | 2 => auxSource4100
  | 3 => auxSource4101
  | 4 => auxSource4102
  | 5 => auxSource4103
  | 6 => auxSource4104
  | 7 => auxSource4105
  | 8 => auxSource4106
  | 9 => auxSource3578
  | 10 => auxSource3579
  | 11 => auxSource4240
  | 12 => auxSource4241
  | 13 => auxSource4242
  | 14 => auxSource2614
  | 15 => auxSource2615
  | 16 => auxSource2616
  | 17 => auxSource2617
  | 18 => auxSource2618
  | 19 => auxSource2619
  | 20 => auxSource2620
  | 21 => auxSource2621
  | 22 => auxSource2622
  | 23 => auxSource2623
  | 24 => auxSource2624
  | 25 => auxSource2625
  | 26 => auxSource2626
  | 27 => auxSource2627
  | 28 => auxSource2628
  | 29 => auxSource2629
  | 30 => auxSource2630
  | 31 => auxSource2631
  | _ => .old 0

compact_certificate theorem actual_source_4 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock4 i.val))=source (i.val+128) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_4 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock4 i.val))=tail (i.val+128) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_4
#print axioms actual_tail_4

compact_certificate def actualBlock5 : ℕ → SourceRow
  | 0 => auxSource2632
  | 1 => auxSource2633
  | 2 => auxSource2634
  | 3 => auxSource2635
  | 4 => auxSource2636
  | 5 => auxSource2637
  | 6 => auxSource2638
  | 7 => auxSource2639
  | 8 => auxSource4413
  | 9 => auxSource2640
  | 10 => auxSource2641
  | 11 => auxSource2642
  | 12 => auxSource2643
  | 13 => auxSource2644
  | 14 => auxSource2645
  | 15 => auxSource2646
  | 16 => auxSource2647
  | 17 => auxSource2648
  | 18 => auxSource2649
  | 19 => auxSource2650
  | 20 => auxSource2651
  | 21 => auxSource2652
  | 22 => auxSource2653
  | 23 => auxSource2654
  | 24 => auxSource2655
  | 25 => auxSource3564
  | 26 => auxSource3565
  | 27 => auxSource3566
  | 28 => auxSource3567
  | 29 => auxSource3568
  | 30 => auxSource3569
  | 31 => auxSource3570
  | _ => .old 0

compact_certificate theorem actual_source_5 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock5 i.val))=source (i.val+160) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_5 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock5 i.val))=tail (i.val+160) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_5
#print axioms actual_tail_5

compact_certificate def actualBlock6 : ℕ → SourceRow
  | 0 => auxSource3571
  | 1 => auxSource3572
  | 2 => auxSource3573
  | 3 => auxSource3574
  | 4 => auxSource3575
  | 5 => auxSource2709
  | 6 => auxSource2710
  | 7 => auxSource2711
  | 8 => auxSource2712
  | 9 => auxSource2713
  | 10 => auxSource2714
  | 11 => auxSource2715
  | 12 => auxSource2716
  | 13 => auxSource2717
  | 14 => auxSource2718
  | 15 => auxSource2225
  | 16 => auxSource2226
  | 17 => auxSource2227
  | 18 => auxSource2228
  | 19 => auxSource2229
  | 20 => auxSource2230
  | 21 => auxSource2231
  | 22 => auxSource2232
  | 23 => auxSource2233
  | 24 => auxSource2234
  | 25 => auxSource2235
  | 26 => auxSource2236
  | 27 => auxSource2237
  | 28 => auxSource2238
  | 29 => auxSource2239
  | 30 => auxSource2240
  | 31 => auxSource2241
  | _ => .old 0

compact_certificate theorem actual_source_6 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock6 i.val))=source (i.val+192) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_6 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock6 i.val))=tail (i.val+192) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_6
#print axioms actual_tail_6

compact_certificate def actualBlock7 : ℕ → SourceRow
  | 0 => auxSource2242
  | 1 => auxSource2243
  | 2 => auxSource2244
  | 3 => auxSource2245
  | 4 => auxSource2246
  | 5 => auxSource2247
  | 6 => auxSource2248
  | 7 => auxSource2249
  | 8 => auxSource2250
  | 9 => auxSource2251
  | 10 => auxSource2252
  | 11 => auxSource2253
  | 12 => auxSource2254
  | 13 => auxSource2255
  | 14 => auxSource2256
  | 15 => auxSource2257
  | 16 => auxSource2258
  | 17 => auxSource2259
  | 18 => auxSource2260
  | 19 => auxSource2261
  | 20 => auxSource2262
  | 21 => auxSource2263
  | 22 => auxSource2264
  | 23 => auxSource2265
  | 24 => auxSource2266
  | 25 => auxSource2267
  | 26 => auxSource2268
  | 27 => auxSource2269
  | 28 => auxSource2270
  | 29 => auxSource2271
  | 30 => auxSource2272
  | 31 => auxSource2273
  | _ => .old 0

compact_certificate theorem actual_source_7 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock7 i.val))=source (i.val+224) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_7 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock7 i.val))=tail (i.val+224) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_7
#print axioms actual_tail_7

compact_certificate def actualBlock8 : ℕ → SourceRow
  | 0 => auxSource2274
  | 1 => auxSource2275
  | 2 => auxSource2276
  | 3 => auxSource2277
  | 4 => auxSource2278
  | 5 => auxSource2279
  | 6 => auxSource2280
  | 7 => auxSource2281
  | 8 => auxSource2282
  | 9 => auxSource2283
  | 10 => auxSource2284
  | 11 => auxSource2285
  | 12 => auxSource4403
  | 13 => auxSource2165
  | 14 => auxSource2166
  | 15 => auxSource2167
  | 16 => auxSource2168
  | 17 => auxSource2169
  | 18 => auxSource2170
  | 19 => auxSource2171
  | 20 => auxSource2172
  | 21 => auxSource2173
  | 22 => auxSource2174
  | 23 => auxSource2175
  | 24 => auxSource2176
  | 25 => auxSource2177
  | 26 => auxSource2178
  | 27 => auxSource2179
  | 28 => auxSource2180
  | 29 => auxSource2181
  | 30 => auxSource2182
  | 31 => auxSource2183
  | _ => .old 0

compact_certificate theorem actual_source_8 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock8 i.val))=source (i.val+256) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_8 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock8 i.val))=tail (i.val+256) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_8
#print axioms actual_tail_8

compact_certificate def actualBlock9 : ℕ → SourceRow
  | 0 => auxSource2184
  | 1 => auxSource2185
  | 2 => auxSource2186
  | 3 => auxSource2187
  | 4 => auxSource2188
  | 5 => auxSource2189
  | 6 => auxSource2190
  | 7 => auxSource2191
  | 8 => auxSource2192
  | 9 => auxSource2193
  | 10 => auxSource2194
  | 11 => auxSource2195
  | 12 => auxSource2196
  | 13 => auxSource2197
  | 14 => auxSource2198
  | 15 => auxSource2199
  | 16 => auxSource2200
  | 17 => auxSource2201
  | 18 => auxSource2202
  | 19 => auxSource2203
  | 20 => auxSource2204
  | 21 => auxSource2205
  | 22 => auxSource2206
  | 23 => auxSource2207
  | 24 => auxSource2208
  | 25 => auxSource2209
  | 26 => auxSource2210
  | 27 => auxSource2211
  | 28 => auxSource2212
  | 29 => auxSource2213
  | 30 => auxSource2214
  | 31 => auxSource2215
  | _ => .old 0

compact_certificate theorem actual_source_9 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock9 i.val))=source (i.val+288) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_9 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock9 i.val))=tail (i.val+288) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_9
#print axioms actual_tail_9

compact_certificate def actualBlock10 : ℕ → SourceRow
  | 0 => auxSource2216
  | 1 => auxSource2217
  | 2 => auxSource2218
  | 3 => auxSource2219
  | 4 => auxSource2220
  | 5 => auxSource2221
  | 6 => auxSource2222
  | 7 => auxSource2223
  | 8 => auxSource2224
  | 9 => auxSource3258
  | 10 => auxSource3259
  | 11 => auxSource3260
  | 12 => auxSource3261
  | 13 => auxSource3262
  | 14 => auxSource3263
  | 15 => auxSource3264
  | 16 => auxSource3265
  | 17 => auxSource3266
  | 18 => auxSource3267
  | 19 => auxSource3268
  | 20 => auxSource3269
  | 21 => auxSource3270
  | 22 => auxSource3271
  | 23 => auxSource3272
  | 24 => auxSource3273
  | 25 => auxSource3274
  | 26 => auxSource3275
  | 27 => auxSource3276
  | 28 => auxSource3277
  | 29 => auxSource3278
  | 30 => auxSource4423
  | 31 => auxSource3279
  | _ => .old 0

compact_certificate theorem actual_source_10 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock10 i.val))=source (i.val+320) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_10 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock10 i.val))=tail (i.val+320) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_10
#print axioms actual_tail_10

compact_certificate def actualBlock11 : ℕ → SourceRow
  | 0 => auxSource3280
  | 1 => auxSource3281
  | 2 => auxSource3282
  | 3 => auxSource3283
  | 4 => auxSource3284
  | 5 => auxSource3285
  | 6 => auxSource3286
  | 7 => auxSource3287
  | 8 => auxSource3288
  | 9 => auxSource3289
  | 10 => auxSource3290
  | 11 => auxSource3291
  | 12 => auxSource3292
  | 13 => auxSource3293
  | 14 => auxSource3294
  | 15 => auxSource3295
  | 16 => auxSource3296
  | 17 => auxSource3297
  | 18 => auxSource3298
  | 19 => auxSource3064
  | 20 => auxSource3065
  | 21 => auxSource3066
  | 22 => auxSource3773
  | 23 => auxSource3774
  | 24 => auxSource3775
  | 25 => auxSource3776
  | 26 => auxSource3777
  | 27 => auxSource3778
  | 28 => auxSource3779
  | 29 => auxSource3780
  | 30 => auxSource3781
  | 31 => auxSource3782
  | _ => .old 0

compact_certificate theorem actual_source_11 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock11 i.val))=source (i.val+352) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_11 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock11 i.val))=tail (i.val+352) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_11
#print axioms actual_tail_11

compact_certificate def actualBlock12 : ℕ → SourceRow
  | 0 => auxSource2294
  | 1 => auxSource2295
  | 2 => auxSource2296
  | 3 => auxSource2297
  | 4 => auxSource2582
  | 5 => auxSource2583
  | 6 => auxSource2584
  | 7 => auxSource2585
  | 8 => auxSource2586
  | 9 => auxSource2587
  | 10 => auxSource2588
  | 11 => auxSource2589
  | 12 => auxSource2590
  | 13 => auxSource4412
  | 14 => auxSource2591
  | 15 => auxSource2592
  | 16 => auxSource2593
  | 17 => auxSource2594
  | 18 => auxSource2595
  | 19 => auxSource2596
  | 20 => auxSource2597
  | 21 => auxSource2598
  | 22 => auxSource2599
  | 23 => auxSource2602
  | 24 => auxSource2603
  | 25 => auxSource3580
  | 26 => auxSource3581
  | 27 => auxSource3582
  | 28 => auxSource3583
  | 29 => auxSource3584
  | 30 => auxSource3585
  | 31 => auxSource3315
  | _ => .old 0

compact_certificate theorem actual_source_12 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock12 i.val))=source (i.val+384) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_12 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock12 i.val))=tail (i.val+384) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_12
#print axioms actual_tail_12

compact_certificate def actualBlock13 : ℕ → SourceRow
  | 0 => auxSource3316
  | 1 => auxSource3317
  | 2 => auxSource3318
  | 3 => auxSource3319
  | 4 => auxSource3320
  | 5 => auxSource3321
  | 6 => auxSource3322
  | 7 => auxSource3323
  | 8 => auxSource3063
  | 9 => auxSource2776
  | 10 => auxSource2777
  | 11 => auxSource2778
  | 12 => auxSource2779
  | 13 => auxSource2780
  | 14 => auxSource2781
  | 15 => auxSource2782
  | 16 => auxSource2783
  | 17 => auxSource2784
  | 18 => auxSource2785
  | 19 => auxSource2786
  | 20 => auxSource2787
  | 21 => auxSource2788
  | 22 => auxSource2789
  | 23 => auxSource2790
  | 24 => auxSource2791
  | 25 => auxSource2792
  | 26 => auxSource4417
  | 27 => auxSource2793
  | 28 => auxSource2794
  | 29 => auxSource2795
  | 30 => auxSource2796
  | 31 => auxSource2797
  | _ => .old 0

compact_certificate theorem actual_source_13 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock13 i.val))=source (i.val+416) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_13 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock13 i.val))=tail (i.val+416) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_13
#print axioms actual_tail_13

compact_certificate def actualBlock14 : ℕ → SourceRow
  | 0 => auxSource2798
  | 1 => auxSource2799
  | 2 => auxSource2800
  | 3 => auxSource2801
  | 4 => auxSource2802
  | 5 => auxSource2803
  | 6 => auxSource2804
  | 7 => auxSource2805
  | 8 => auxSource2806
  | 9 => auxSource2807
  | 10 => auxSource2808
  | 11 => auxSource2809
  | 12 => auxSource2810
  | 13 => auxSource2811
  | 14 => auxSource2812
  | 15 => auxSource2813
  | 16 => auxSource2814
  | 17 => auxSource2815
  | 18 => auxSource2816
  | 19 => auxSource2817
  | 20 => auxSource2818
  | 21 => auxSource2950
  | 22 => auxSource2951
  | 23 => auxSource2952
  | 24 => auxSource2953
  | 25 => auxSource2954
  | 26 => auxSource3635
  | 27 => auxSource3636
  | 28 => auxSource3637
  | 29 => auxSource3638
  | 30 => auxSource3639
  | 31 => auxSource3640
  | _ => .old 0

compact_certificate theorem actual_source_14 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock14 i.val))=source (i.val+448) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_14 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock14 i.val))=tail (i.val+448) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_14
#print axioms actual_tail_14

compact_certificate def actualBlock15 : ℕ → SourceRow
  | 0 => auxSource3641
  | 1 => auxSource3642
  | 2 => auxSource3643
  | 3 => auxSource3644
  | 4 => auxSource3645
  | 5 => auxSource3646
  | 6 => auxSource3647
  | 7 => auxSource3648
  | 8 => auxSource3649
  | 9 => auxSource3650
  | 10 => auxSource3651
  | 11 => auxSource3652
  | 12 => auxSource3653
  | 13 => auxSource3654
  | 14 => auxSource3655
  | 15 => auxSource3656
  | 16 => auxSource3657
  | 17 => auxSource3658
  | 18 => auxSource4429
  | 19 => auxSource3659
  | 20 => auxSource3660
  | 21 => auxSource3661
  | 22 => auxSource3662
  | 23 => auxSource3663
  | 24 => auxSource3664
  | 25 => auxSource3665
  | 26 => auxSource3666
  | 27 => auxSource3667
  | 28 => auxSource3668
  | 29 => auxSource3669
  | 30 => auxSource3670
  | 31 => auxSource3671
  | _ => .old 0

compact_certificate theorem actual_source_15 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock15 i.val))=source (i.val+480) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_15 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock15 i.val))=tail (i.val+480) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_15
#print axioms actual_tail_15

compact_certificate def actualBlock16 : ℕ → SourceRow
  | 0 => auxSource3672
  | 1 => auxSource3673
  | 2 => auxSource3674
  | 3 => auxSource3675
  | 4 => auxSource3676
  | 5 => auxSource3677
  | 6 => auxSource3678
  | 7 => auxSource3679
  | 8 => auxSource3680
  | 9 => auxSource3681
  | 10 => auxSource3682
  | 11 => auxSource4163
  | 12 => auxSource4164
  | 13 => auxSource4165
  | 14 => auxSource4166
  | 15 => auxSource4442
  | 16 => auxSource4167
  | 17 => auxSource4168
  | 18 => auxSource4169
  | 19 => auxSource4170
  | 20 => auxSource4171
  | 21 => auxSource4172
  | 22 => auxSource4173
  | 23 => auxSource4174
  | 24 => auxSource4175
  | 25 => auxSource3011
  | 26 => auxSource3012
  | 27 => auxSource3013
  | 28 => auxSource3014
  | 29 => auxSource3015
  | 30 => auxSource3016
  | 31 => auxSource3017
  | _ => .old 0

compact_certificate theorem actual_source_16 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock16 i.val))=source (i.val+512) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_16 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock16 i.val))=tail (i.val+512) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_16
#print axioms actual_tail_16

compact_certificate def actualBlock17 : ℕ → SourceRow
  | 0 => auxSource3018
  | 1 => auxSource3019
  | 2 => auxSource3020
  | 3 => auxSource3021
  | 4 => auxSource3022
  | 5 => auxSource3023
  | 6 => auxSource4421
  | 7 => auxSource3024
  | 8 => auxSource3025
  | 9 => auxSource3026
  | 10 => auxSource3027
  | 11 => auxSource3028
  | 12 => auxSource3029
  | 13 => auxSource3030
  | 14 => auxSource3031
  | 15 => auxSource3032
  | 16 => auxSource3033
  | 17 => auxSource3034
  | 18 => auxSource3035
  | 19 => auxSource3036
  | 20 => auxSource3037
  | 21 => auxSource3038
  | 22 => auxSource3039
  | 23 => auxSource3040
  | 24 => auxSource3041
  | 25 => auxSource3042
  | 26 => auxSource3043
  | 27 => auxSource3044
  | 28 => auxSource3045
  | 29 => auxSource3046
  | 30 => auxSource3047
  | 31 => auxSource3048
  | _ => .old 0

compact_certificate theorem actual_source_17 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock17 i.val))=source (i.val+544) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_17 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock17 i.val))=tail (i.val+544) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_17
#print axioms actual_tail_17

compact_certificate def actualBlock18 : ℕ → SourceRow
  | 0 => auxSource3049
  | 1 => auxSource3525
  | 2 => auxSource3526
  | 3 => auxSource3527
  | 4 => auxSource3528
  | 5 => auxSource3529
  | 6 => auxSource3530
  | 7 => auxSource3531
  | 8 => auxSource3532
  | 9 => auxSource3533
  | 10 => auxSource3534
  | 11 => auxSource3535
  | 12 => auxSource3536
  | 13 => auxSource3537
  | 14 => auxSource4427
  | 15 => auxSource3538
  | 16 => auxSource3539
  | 17 => auxSource3540
  | 18 => auxSource3541
  | 19 => auxSource3542
  | 20 => auxSource3543
  | 21 => auxSource3544
  | 22 => auxSource3545
  | 23 => auxSource3546
  | 24 => auxSource3547
  | 25 => auxSource3548
  | 26 => auxSource3549
  | 27 => auxSource3550
  | 28 => auxSource3551
  | 29 => auxSource3552
  | 30 => auxSource3553
  | 31 => auxSource3554
  | _ => .old 0

compact_certificate theorem actual_source_18 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock18 i.val))=source (i.val+576) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_18 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock18 i.val))=tail (i.val+576) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_18
#print axioms actual_tail_18

compact_certificate def actualBlock19 : ℕ → SourceRow
  | 0 => auxSource3555
  | 1 => auxSource3556
  | 2 => auxSource3557
  | 3 => auxSource3558
  | 4 => auxSource3559
  | 5 => auxSource3560
  | 6 => auxSource3561
  | 7 => auxSource3562
  | 8 => auxSource3563
  | 9 => auxSource3705
  | 10 => auxSource3706
  | 11 => auxSource3707
  | 12 => auxSource4431
  | 13 => auxSource3708
  | 14 => auxSource3709
  | 15 => auxSource3710
  | 16 => auxSource4334
  | 17 => auxSource4335
  | 18 => auxSource4336
  | 19 => auxSource2534
  | 20 => auxSource2535
  | 21 => auxSource2536
  | 22 => auxSource2537
  | 23 => auxSource2538
  | 24 => auxSource2539
  | 25 => auxSource2540
  | 26 => auxSource2541
  | 27 => auxSource2542
  | 28 => auxSource2543
  | 29 => auxSource2544
  | 30 => auxSource2545
  | 31 => auxSource2546
  | _ => .old 0

compact_certificate theorem actual_source_19 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock19 i.val))=source (i.val+608) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_19 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock19 i.val))=tail (i.val+608) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_19
#print axioms actual_tail_19

compact_certificate def actualBlock20 : ℕ → SourceRow
  | 0 => auxSource2547
  | 1 => auxSource2548
  | 2 => auxSource2549
  | 3 => auxSource2550
  | 4 => auxSource2551
  | 5 => auxSource2552
  | 6 => auxSource2553
  | 7 => auxSource2554
  | 8 => auxSource2555
  | 9 => auxSource2556
  | 10 => auxSource2557
  | 11 => auxSource4411
  | 12 => auxSource2558
  | 13 => auxSource2559
  | 14 => auxSource2560
  | 15 => auxSource2561
  | 16 => auxSource2562
  | 17 => auxSource2563
  | 18 => auxSource2564
  | 19 => auxSource2565
  | 20 => auxSource2566
  | 21 => auxSource2567
  | 22 => auxSource2568
  | 23 => auxSource2569
  | 24 => auxSource2570
  | 25 => auxSource2571
  | 26 => auxSource2572
  | 27 => auxSource2573
  | 28 => auxSource2574
  | 29 => auxSource2575
  | 30 => auxSource2576
  | 31 => auxSource2577
  | _ => .old 0

compact_certificate theorem actual_source_20 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock20 i.val))=source (i.val+640) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_20 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock20 i.val))=tail (i.val+640) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_20
#print axioms actual_tail_20

compact_certificate def actualBlock21 : ℕ → SourceRow
  | 0 => auxSource2578
  | 1 => auxSource2579
  | 2 => auxSource2580
  | 3 => auxSource2581
  | 4 => auxSource3839
  | 5 => auxSource3840
  | 6 => auxSource3841
  | 7 => auxSource3842
  | 8 => auxSource4360
  | 9 => auxSource2728
  | 10 => auxSource2729
  | 11 => auxSource2730
  | 12 => auxSource2731
  | 13 => auxSource2732
  | 14 => auxSource2733
  | 15 => auxSource2734
  | 16 => auxSource2735
  | 17 => auxSource2736
  | 18 => auxSource2737
  | 19 => auxSource2738
  | 20 => auxSource2739
  | 21 => auxSource2740
  | 22 => auxSource2741
  | 23 => auxSource2742
  | 24 => auxSource2743
  | 25 => auxSource2744
  | 26 => auxSource2745
  | 27 => auxSource2746
  | 28 => auxSource2747
  | 29 => auxSource2748
  | 30 => auxSource2749
  | 31 => auxSource2750
  | _ => .old 0

compact_certificate theorem actual_source_21 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock21 i.val))=source (i.val+672) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_21 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock21 i.val))=tail (i.val+672) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_21
#print axioms actual_tail_21

compact_certificate def actualBlock22 : ℕ → SourceRow
  | 0 => auxSource2751
  | 1 => auxSource2752
  | 2 => auxSource2753
  | 3 => auxSource4415
  | 4 => auxSource2754
  | 5 => auxSource2755
  | 6 => auxSource2756
  | 7 => auxSource2757
  | 8 => auxSource2758
  | 9 => auxSource2759
  | 10 => auxSource2760
  | 11 => auxSource2761
  | 12 => auxSource2762
  | 13 => auxSource2763
  | 14 => auxSource2764
  | 15 => auxSource2765
  | 16 => auxSource2766
  | 17 => auxSource2767
  | 18 => auxSource2768
  | 19 => auxSource2769
  | 20 => auxSource3698
  | 21 => auxSource3699
  | 22 => auxSource3854
  | 23 => auxSource3855
  | 24 => auxSource3856
  | 25 => auxSource3857
  | 26 => auxSource3858
  | 27 => auxSource3859
  | 28 => auxSource3860
  | 29 => auxSource3861
  | 30 => auxSource3862
  | 31 => auxSource3863
  | _ => .old 0

compact_certificate theorem actual_source_22 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock22 i.val))=source (i.val+704) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_22 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock22 i.val))=tail (i.val+704) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_22
#print axioms actual_tail_22

compact_certificate def actualBlock23 : ℕ → SourceRow
  | 0 => auxSource3864
  | 1 => auxSource3865
  | 2 => auxSource3866
  | 3 => auxSource3867
  | 4 => auxSource3868
  | 5 => auxSource3869
  | 6 => auxSource3870
  | 7 => auxSource3871
  | 8 => auxSource3872
  | 9 => auxSource3873
  | 10 => auxSource3874
  | 11 => auxSource3875
  | 12 => auxSource3876
  | 13 => auxSource3877
  | 14 => auxSource4436
  | 15 => auxSource3878
  | 16 => auxSource3879
  | 17 => auxSource3880
  | 18 => auxSource3881
  | 19 => auxSource3882
  | 20 => auxSource3883
  | 21 => auxSource3884
  | 22 => auxSource3885
  | 23 => auxSource3886
  | 24 => auxSource3887
  | 25 => auxSource3888
  | 26 => auxSource3889
  | 27 => auxSource3890
  | 28 => auxSource3891
  | 29 => auxSource3892
  | 30 => auxSource3893
  | 31 => auxSource3894
  | _ => .old 0

compact_certificate theorem actual_source_23 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock23 i.val))=source (i.val+736) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_23 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock23 i.val))=tail (i.val+736) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_23
#print axioms actual_tail_23

compact_certificate def actualBlock24 : ℕ → SourceRow
  | 0 => auxSource3895
  | 1 => auxSource3896
  | 2 => auxSource3897
  | 3 => auxSource3898
  | 4 => auxSource3899
  | 5 => auxSource3900
  | 6 => auxSource3901
  | 7 => auxSource4385
  | 8 => auxSource4386
  | 9 => auxSource4387
  | 10 => auxSource4388
  | 11 => auxSource4389
  | 12 => auxSource3483
  | 13 => auxSource3484
  | 14 => auxSource3485
  | 15 => auxSource3486
  | 16 => auxSource3487
  | 17 => auxSource3488
  | 18 => auxSource3489
  | 19 => auxSource3490
  | 20 => auxSource3491
  | 21 => auxSource3492
  | 22 => auxSource3493
  | 23 => auxSource3494
  | 24 => auxSource3495
  | 25 => auxSource3496
  | 26 => auxSource3497
  | 27 => auxSource3498
  | 28 => auxSource3499
  | 29 => auxSource3500
  | 30 => auxSource3501
  | 31 => auxSource3502
  | _ => .old 0

compact_certificate theorem actual_source_24 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock24 i.val))=source (i.val+768) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_24 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock24 i.val))=tail (i.val+768) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_24
#print axioms actual_tail_24

compact_certificate def actualBlock25 : ℕ → SourceRow
  | 0 => auxSource3503
  | 1 => auxSource3504
  | 2 => auxSource3505
  | 3 => auxSource3506
  | 4 => auxSource3507
  | 5 => auxSource3508
  | 6 => auxSource4426
  | 7 => auxSource3509
  | 8 => auxSource3510
  | 9 => auxSource3511
  | 10 => auxSource3512
  | 11 => auxSource3513
  | 12 => auxSource3514
  | 13 => auxSource3515
  | 14 => auxSource3516
  | 15 => auxSource3517
  | 16 => auxSource3518
  | 17 => auxSource3519
  | 18 => auxSource3520
  | 19 => auxSource3521
  | 20 => auxSource2298
  | 21 => auxSource2299
  | 22 => auxSource2300
  | 23 => auxSource2301
  | 24 => auxSource2302
  | 25 => auxSource2303
  | 26 => auxSource2304
  | 27 => auxSource2305
  | 28 => auxSource2306
  | 29 => auxSource2307
  | 30 => auxSource2308
  | 31 => auxSource2309
  | _ => .old 0

compact_certificate theorem actual_source_25 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock25 i.val))=source (i.val+800) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_25 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock25 i.val))=tail (i.val+800) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_25
#print axioms actual_tail_25

compact_certificate def actualBlock26 : ℕ → SourceRow
  | 0 => auxSource3576
  | 1 => auxSource2719
  | 2 => auxSource3464
  | 3 => auxSource3465
  | 4 => auxSource3466
  | 5 => auxSource3467
  | 6 => auxSource3468
  | 7 => auxSource3469
  | 8 => auxSource3062
  | 9 => auxSource4316
  | 10 => auxSource4317
  | 11 => auxSource4318
  | 12 => auxSource4319
  | 13 => auxSource4320
  | 14 => auxSource4321
  | 15 => auxSource4322
  | 16 => auxSource4323
  | 17 => auxSource4324
  | 18 => auxSource4446
  | 19 => auxSource4325
  | 20 => auxSource4326
  | 21 => auxSource4327
  | 22 => auxSource4328
  | 23 => auxSource4329
  | 24 => auxSource4330
  | 25 => auxSource4331
  | 26 => auxSource4332
  | 27 => auxSource4333
  | 28 => auxSource4364
  | 29 => auxSource4365
  | 30 => auxSource4366
  | 31 => auxSource4448
  | _ => .old 0

compact_certificate theorem actual_source_26 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock26 i.val))=source (i.val+832) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_26 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock26 i.val))=tail (i.val+832) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_26
#print axioms actual_tail_26

compact_certificate def actualBlock27 : ℕ → SourceRow
  | 0 => auxSource4367
  | 1 => auxSource4368
  | 2 => auxSource4369
  | 3 => auxSource2604
  | 4 => auxSource2293
  | 5 => auxSource2449
  | 6 => auxSource4439
  | 7 => auxSource3987
  | 8 => auxSource3988
  | 9 => auxSource3989
  | 10 => auxSource3990
  | 11 => auxSource3991
  | 12 => auxSource3992
  | 13 => auxSource3993
  | 14 => auxSource3994
  | 15 => auxSource3995
  | 16 => auxSource3996
  | 17 => auxSource3997
  | 18 => auxSource3998
  | 19 => auxSource3999
  | 20 => auxSource4000
  | 21 => auxSource4001
  | 22 => auxSource4002
  | 23 => auxSource4003
  | 24 => auxSource4004
  | 25 => auxSource4005
  | 26 => auxSource4006
  | 27 => auxSource4007
  | 28 => auxSource4008
  | 29 => auxSource4009
  | 30 => auxSource4010
  | 31 => auxSource4011
  | _ => .old 0

compact_certificate theorem actual_source_27 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock27 i.val))=source (i.val+864) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_27 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock27 i.val))=tail (i.val+864) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_27
#print axioms actual_tail_27

compact_certificate def actualBlock28 : ℕ → SourceRow
  | 0 => auxSource4012
  | 1 => auxSource4013
  | 2 => auxSource4014
  | 3 => auxSource4015
  | 4 => auxSource4016
  | 5 => auxSource4017
  | 6 => auxSource4018
  | 7 => auxSource4019
  | 8 => auxSource4020
  | 9 => auxSource4021
  | 10 => auxSource4022
  | 11 => auxSource4023
  | 12 => auxSource4024
  | 13 => auxSource4025
  | 14 => auxSource4026
  | 15 => auxSource4027
  | 16 => auxSource4028
  | 17 => auxSource4029
  | 18 => auxSource4030
  | 19 => auxSource4031
  | 20 => auxSource4032
  | 21 => auxSource4033
  | 22 => auxSource4034
  | 23 => auxSource4035
  | 24 => auxSource4036
  | 25 => auxSource4037
  | 26 => auxSource4038
  | 27 => auxSource4039
  | 28 => auxSource4040
  | 29 => auxSource4041
  | 30 => auxSource4042
  | 31 => auxSource4043
  | _ => .old 0

compact_certificate theorem actual_source_28 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock28 i.val))=source (i.val+896) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_28 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock28 i.val))=tail (i.val+896) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_28
#print axioms actual_tail_28

compact_certificate def actualBlock29 : ℕ → SourceRow
  | 0 => auxSource4044
  | 1 => auxSource4045
  | 2 => auxSource4046
  | 3 => auxSource3797
  | 4 => auxSource3798
  | 5 => auxSource3799
  | 6 => auxSource3800
  | 7 => auxSource3801
  | 8 => auxSource3802
  | 9 => auxSource3803
  | 10 => auxSource3804
  | 11 => auxSource3805
  | 12 => auxSource3806
  | 13 => auxSource3807
  | 14 => auxSource3808
  | 15 => auxSource3809
  | 16 => auxSource3810
  | 17 => auxSource3811
  | 18 => auxSource3812
  | 19 => auxSource3813
  | 20 => auxSource3814
  | 21 => auxSource3815
  | 22 => auxSource3816
  | 23 => auxSource3817
  | 24 => auxSource3818
  | 25 => auxSource3819
  | 26 => auxSource3820
  | 27 => auxSource3821
  | 28 => auxSource3822
  | 29 => auxSource4435
  | 30 => auxSource3823
  | 31 => auxSource3824
  | _ => .old 0

compact_certificate theorem actual_source_29 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock29 i.val))=source (i.val+928) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_29 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock29 i.val))=tail (i.val+928) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_29
#print axioms actual_tail_29

compact_certificate def actualBlock30 : ℕ → SourceRow
  | 0 => auxSource3825
  | 1 => auxSource3826
  | 2 => auxSource3827
  | 3 => auxSource3828
  | 4 => auxSource3829
  | 5 => auxSource3830
  | 6 => auxSource3831
  | 7 => auxSource3832
  | 8 => auxSource3833
  | 9 => auxSource3834
  | 10 => auxSource3835
  | 11 => auxSource3836
  | 12 => auxSource3837
  | 13 => auxSource3838
  | 14 => auxSource2829
  | 15 => auxSource2155
  | 16 => auxSource2156
  | 17 => auxSource2157
  | 18 => auxSource2158
  | 19 => auxSource2605
  | 20 => auxSource2606
  | 21 => auxSource2607
  | 22 => auxSource2608
  | 23 => auxSource2609
  | 24 => auxSource2610
  | 25 => auxSource2611
  | 26 => auxSource2612
  | 27 => auxSource2613
  | 28 => auxSource3700
  | 29 => auxSource3701
  | 30 => auxSource3702
  | 31 => auxSource3703
  | _ => .old 0

compact_certificate theorem actual_source_30 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock30 i.val))=source (i.val+960) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_30 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock30 i.val))=tail (i.val+960) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_30
#print axioms actual_tail_30

compact_certificate def actualBlock31 : ℕ → SourceRow
  | 0 => auxSource3704
  | 1 => auxSource3754
  | 2 => auxSource3755
  | 3 => auxSource3756
  | 4 => auxSource3757
  | 5 => auxSource3758
  | 6 => auxSource3759
  | 7 => auxSource4433
  | 8 => auxSource3760
  | 9 => auxSource3761
  | 10 => auxSource3762
  | 11 => auxSource3763
  | 12 => auxSource3764
  | 13 => auxSource3765
  | 14 => auxSource3766
  | 15 => auxSource3767
  | 16 => auxSource3768
  | 17 => auxSource3384
  | 18 => auxSource3385
  | 19 => auxSource3386
  | 20 => auxSource3387
  | 21 => auxSource4402
  | 22 => auxSource4274
  | 23 => auxSource4275
  | 24 => auxSource4276
  | 25 => auxSource4277
  | 26 => auxSource4278
  | 27 => auxSource4279
  | 28 => auxSource4280
  | 29 => auxSource4281
  | 30 => auxSource4282
  | 31 => auxSource4283
  | _ => .old 0

compact_certificate theorem actual_source_31 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock31 i.val))=source (i.val+992) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_31 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock31 i.val))=tail (i.val+992) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_31
#print axioms actual_tail_31

compact_certificate def actualBlock32 : ℕ → SourceRow
  | 0 => auxSource4284
  | 1 => auxSource4285
  | 2 => auxSource4286
  | 3 => auxSource4287
  | 4 => auxSource4288
  | 5 => auxSource4289
  | 6 => auxSource4290
  | 7 => auxSource4291
  | 8 => auxSource4292
  | 9 => auxSource4293
  | 10 => auxSource4294
  | 11 => auxSource4445
  | 12 => auxSource4295
  | 13 => auxSource4296
  | 14 => auxSource4297
  | 15 => auxSource4298
  | 16 => auxSource4299
  | 17 => auxSource4300
  | 18 => auxSource4301
  | 19 => auxSource4302
  | 20 => auxSource4303
  | 21 => auxSource4304
  | 22 => auxSource4305
  | 23 => auxSource4306
  | 24 => auxSource4307
  | 25 => auxSource4308
  | 26 => auxSource4309
  | 27 => auxSource4310
  | 28 => auxSource4311
  | 29 => auxSource4312
  | 30 => auxSource4313
  | 31 => auxSource4314
  | _ => .old 0

compact_certificate theorem actual_source_32 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock32 i.val))=source (i.val+1024) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_32 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock32 i.val))=tail (i.val+1024) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_32
#print axioms actual_tail_32

compact_certificate def actualBlock33 : ℕ → SourceRow
  | 0 => auxSource2448
  | 1 => auxSource2720
  | 2 => auxSource4396
  | 3 => auxSource4397
  | 4 => auxSource4398
  | 5 => auxSource4399
  | 6 => auxSource4400
  | 7 => auxSource3249
  | 8 => auxSource3250
  | 9 => auxSource3251
  | 10 => auxSource3252
  | 11 => auxSource3253
  | 12 => auxSource3254
  | 13 => auxSource3255
  | 14 => auxSource3256
  | 15 => auxSource3257
  | 16 => auxSource2840
  | 17 => auxSource2841
  | 18 => auxSource3008
  | 19 => auxSource3009
  | 20 => auxSource3010
  | 21 => auxSource3450
  | 22 => auxSource3919
  | 23 => auxSource3920
  | 24 => auxSource3921
  | 25 => auxSource3922
  | 26 => auxSource3923
  | 27 => auxSource3924
  | 28 => auxSource3925
  | 29 => auxSource3926
  | 30 => auxSource3927
  | 31 => auxSource3928
  | _ => .old 0

compact_certificate theorem actual_source_33 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock33 i.val))=source (i.val+1056) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_33 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock33 i.val))=tail (i.val+1056) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_33
#print axioms actual_tail_33

compact_certificate def actualBlock34 : ℕ → SourceRow
  | 0 => auxSource3929
  | 1 => auxSource3930
  | 2 => auxSource3931
  | 3 => auxSource4437
  | 4 => auxSource3932
  | 5 => auxSource3933
  | 6 => auxSource3934
  | 7 => auxSource3935
  | 8 => auxSource3936
  | 9 => auxSource3937
  | 10 => auxSource3938
  | 11 => auxSource3939
  | 12 => auxSource3940
  | 13 => auxSource3941
  | 14 => auxSource3942
  | 15 => auxSource3943
  | 16 => auxSource3944
  | 17 => auxSource3945
  | 18 => auxSource3946
  | 19 => auxSource3947
  | 20 => auxSource3948
  | 21 => auxSource3949
  | 22 => auxSource3950
  | 23 => auxSource3951
  | 24 => auxSource3952
  | 25 => auxSource3953
  | 26 => auxSource3954
  | 27 => auxSource3955
  | 28 => auxSource3956
  | 29 => auxSource3957
  | 30 => auxSource2468
  | 31 => auxSource2469
  | _ => .old 0

compact_certificate theorem actual_source_34 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock34 i.val))=source (i.val+1088) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_34 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock34 i.val))=tail (i.val+1088) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_34
#print axioms actual_tail_34

compact_certificate def actualBlock35 : ℕ → SourceRow
  | 0 => auxSource2470
  | 1 => auxSource2471
  | 2 => auxSource2472
  | 3 => auxSource2473
  | 4 => auxSource2474
  | 5 => auxSource2475
  | 6 => auxSource2476
  | 7 => auxSource4409
  | 8 => auxSource2477
  | 9 => auxSource2478
  | 10 => auxSource2479
  | 11 => auxSource2480
  | 12 => auxSource2481
  | 13 => auxSource2482
  | 14 => auxSource2483
  | 15 => auxSource2484
  | 16 => auxSource2485
  | 17 => auxSource2375
  | 18 => auxSource2376
  | 19 => auxSource2377
  | 20 => auxSource2378
  | 21 => auxSource4407
  | 22 => auxSource2379
  | 23 => auxSource2380
  | 24 => auxSource2381
  | 25 => auxSource2382
  | 26 => auxSource2383
  | 27 => auxSource2384
  | 28 => auxSource2385
  | 29 => auxSource2386
  | 30 => auxSource2387
  | 31 => auxSource2770
  | _ => .old 0

compact_certificate theorem actual_source_35 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock35 i.val))=source (i.val+1120) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_35 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock35 i.val))=tail (i.val+1120) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_35
#print axioms actual_tail_35

compact_certificate def actualBlock36 : ℕ → SourceRow
  | 0 => auxSource2771
  | 1 => auxSource2772
  | 2 => auxSource4416
  | 3 => auxSource2773
  | 4 => auxSource2774
  | 5 => auxSource2775
  | 6 => auxSource2349
  | 7 => auxSource2350
  | 8 => auxSource2351
  | 9 => auxSource2352
  | 10 => auxSource2353
  | 11 => auxSource2354
  | 12 => auxSource2355
  | 13 => auxSource2356
  | 14 => auxSource2357
  | 15 => auxSource4405
  | 16 => auxSource2358
  | 17 => auxSource2359
  | 18 => auxSource2360
  | 19 => auxSource2361
  | 20 => auxSource3470
  | 21 => auxSource4243
  | 22 => auxSource4244
  | 23 => auxSource4245
  | 24 => auxSource3685
  | 25 => auxSource3686
  | 26 => auxSource3687
  | 27 => auxSource4430
  | 28 => auxSource3688
  | 29 => auxSource3689
  | 30 => auxSource3690
  | 31 => auxSource3971
  | _ => .old 0

compact_certificate theorem actual_source_36 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock36 i.val))=source (i.val+1152) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_36 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock36 i.val))=tail (i.val+1152) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_36
#print axioms actual_tail_36

compact_certificate def actualBlock37 : ℕ → SourceRow
  | 0 => auxSource3972
  | 1 => auxSource3973
  | 2 => auxSource3974
  | 3 => auxSource3683
  | 4 => auxSource3684
  | 5 => auxSource3691
  | 6 => auxSource3692
  | 7 => auxSource3693
  | 8 => auxSource3694
  | 9 => auxSource3695
  | 10 => auxSource2656
  | 11 => auxSource2657
  | 12 => auxSource2658
  | 13 => auxSource2659
  | 14 => auxSource2660
  | 15 => auxSource4425
  | 16 => auxSource3389
  | 17 => auxSource3390
  | 18 => auxSource3391
  | 19 => auxSource3392
  | 20 => auxSource3393
  | 21 => auxSource3394
  | 22 => auxSource3395
  | 23 => auxSource3396
  | 24 => auxSource3397
  | 25 => auxSource3398
  | 26 => auxSource3399
  | 27 => auxSource3400
  | 28 => auxSource3401
  | 29 => auxSource3402
  | 30 => auxSource3403
  | 31 => auxSource3404
  | _ => .old 0

compact_certificate theorem actual_source_37 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock37 i.val))=source (i.val+1184) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_37 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock37 i.val))=tail (i.val+1184) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_37
#print axioms actual_tail_37

compact_certificate def actualBlock38 : ℕ → SourceRow
  | 0 => auxSource3405
  | 1 => auxSource3406
  | 2 => auxSource3407
  | 3 => auxSource3408
  | 4 => auxSource3409
  | 5 => auxSource3410
  | 6 => auxSource3411
  | 7 => auxSource3412
  | 8 => auxSource3413
  | 9 => auxSource3414
  | 10 => auxSource3415
  | 11 => auxSource3416
  | 12 => auxSource3417
  | 13 => auxSource3418
  | 14 => auxSource3419
  | 15 => auxSource3420
  | 16 => auxSource3421
  | 17 => auxSource3422
  | 18 => auxSource3423
  | 19 => auxSource3424
  | 20 => auxSource3425
  | 21 => auxSource3426
  | 22 => auxSource3427
  | 23 => auxSource3428
  | 24 => auxSource3429
  | 25 => auxSource3430
  | 26 => auxSource3431
  | 27 => auxSource3432
  | 28 => auxSource3433
  | 29 => auxSource3434
  | 30 => auxSource3435
  | 31 => auxSource3436
  | _ => .old 0

compact_certificate theorem actual_source_38 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock38 i.val))=source (i.val+1216) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_38 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock38 i.val))=tail (i.val+1216) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_38
#print axioms actual_tail_38

compact_certificate def actualBlock39 : ℕ → SourceRow
  | 0 => auxSource3437
  | 1 => auxSource3438
  | 2 => auxSource3439
  | 3 => auxSource3440
  | 4 => auxSource3441
  | 5 => auxSource3442
  | 6 => auxSource3443
  | 7 => auxSource3444
  | 8 => auxSource3445
  | 9 => auxSource3446
  | 10 => auxSource3447
  | 11 => auxSource3448
  | 12 => auxSource3299
  | 13 => auxSource3300
  | 14 => auxSource3301
  | 15 => auxSource3302
  | 16 => auxSource3303
  | 17 => auxSource3304
  | 18 => auxSource3305
  | 19 => auxSource3306
  | 20 => auxSource3307
  | 21 => auxSource3308
  | 22 => auxSource3309
  | 23 => auxSource3310
  | 24 => auxSource3311
  | 25 => auxSource3312
  | 26 => auxSource3313
  | 27 => auxSource3314
  | 28 => auxSource2427
  | 29 => auxSource2428
  | 30 => auxSource2429
  | 31 => auxSource2430
  | _ => .old 0

compact_certificate theorem actual_source_39 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock39 i.val))=source (i.val+1248) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_39 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock39 i.val))=tail (i.val+1248) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_39
#print axioms actual_tail_39

compact_certificate def actualBlock40 : ℕ → SourceRow
  | 0 => auxSource2431
  | 1 => auxSource2432
  | 2 => auxSource2433
  | 3 => auxSource2434
  | 4 => auxSource2435
  | 5 => auxSource2436
  | 6 => auxSource2437
  | 7 => auxSource2438
  | 8 => auxSource3050
  | 9 => auxSource3051
  | 10 => auxSource3052
  | 11 => auxSource3053
  | 12 => auxSource3054
  | 13 => auxSource3055
  | 14 => auxSource3056
  | 15 => auxSource3057
  | 16 => auxSource3058
  | 17 => auxSource3059
  | 18 => auxSource3060
  | 19 => auxSource3061
  | 20 => auxSource2600
  | 21 => auxSource2601
  | 22 => auxSource4246
  | 23 => auxSource4247
  | 24 => auxSource4248
  | 25 => auxSource4249
  | 26 => auxSource4250
  | 27 => auxSource4251
  | 28 => auxSource4252
  | 29 => auxSource4253
  | 30 => auxSource4254
  | 31 => auxSource4255
  | _ => .old 0

compact_certificate theorem actual_source_40 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock40 i.val))=source (i.val+1280) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_40 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock40 i.val))=tail (i.val+1280) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_40
#print axioms actual_tail_40

compact_certificate def actualBlock41 : ℕ → SourceRow
  | 0 => auxSource2388
  | 1 => auxSource2389
  | 2 => auxSource2390
  | 3 => auxSource2391
  | 4 => auxSource2392
  | 5 => auxSource2393
  | 6 => auxSource2394
  | 7 => auxSource2395
  | 8 => auxSource2396
  | 9 => auxSource2397
  | 10 => auxSource2398
  | 11 => auxSource2399
  | 12 => auxSource2400
  | 13 => auxSource4408
  | 14 => auxSource2401
  | 15 => auxSource2402
  | 16 => auxSource2403
  | 17 => auxSource2404
  | 18 => auxSource2405
  | 19 => auxSource2406
  | 20 => auxSource2407
  | 21 => auxSource2408
  | 22 => auxSource2409
  | 23 => auxSource2410
  | 24 => auxSource2411
  | 25 => auxSource2412
  | 26 => auxSource2413
  | 27 => auxSource2414
  | 28 => auxSource2415
  | 29 => auxSource2416
  | 30 => auxSource2417
  | 31 => auxSource2418
  | _ => .old 0

compact_certificate theorem actual_source_41 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock41 i.val))=source (i.val+1312) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_41 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock41 i.val))=tail (i.val+1312) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_41
#print axioms actual_tail_41

compact_certificate def actualBlock42 : ℕ → SourceRow
  | 0 => auxSource2419
  | 1 => auxSource2420
  | 2 => auxSource2421
  | 3 => auxSource2422
  | 4 => auxSource2423
  | 5 => auxSource2424
  | 6 => auxSource2425
  | 7 => auxSource2426
  | 8 => auxSource3769
  | 9 => auxSource3770
  | 10 => auxSource3771
  | 11 => auxSource3772
  | 12 => auxSource2955
  | 13 => auxSource2956
  | 14 => auxSource2310
  | 15 => auxSource2311
  | 16 => auxSource2312
  | 17 => auxSource2313
  | 18 => auxSource2314
  | 19 => auxSource2315
  | 20 => auxSource2316
  | 21 => auxSource2317
  | 22 => auxSource2318
  | 23 => auxSource2319
  | 24 => auxSource2320
  | 25 => auxSource2321
  | 26 => auxSource2322
  | 27 => auxSource2323
  | 28 => auxSource2324
  | 29 => auxSource2325
  | 30 => auxSource2326
  | 31 => auxSource2327
  | _ => .old 0

compact_certificate theorem actual_source_42 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock42 i.val))=source (i.val+1344) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_42 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock42 i.val))=tail (i.val+1344) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_42
#print axioms actual_tail_42

compact_certificate def actualBlock43 : ℕ → SourceRow
  | 0 => auxSource2328
  | 1 => auxSource2329
  | 2 => auxSource2330
  | 3 => auxSource2331
  | 4 => auxSource2332
  | 5 => auxSource2333
  | 6 => auxSource2334
  | 7 => auxSource2335
  | 8 => auxSource4404
  | 9 => auxSource2336
  | 10 => auxSource2337
  | 11 => auxSource2338
  | 12 => auxSource2339
  | 13 => auxSource2340
  | 14 => auxSource2341
  | 15 => auxSource2342
  | 16 => auxSource2343
  | 17 => auxSource2344
  | 18 => auxSource2345
  | 19 => auxSource2346
  | 20 => auxSource2347
  | 21 => auxSource2348
  | 22 => auxSource4342
  | 23 => auxSource4343
  | 24 => auxSource4344
  | 25 => auxSource4345
  | 26 => auxSource3451
  | 27 => auxSource3458
  | 28 => auxSource3459
  | 29 => auxSource3460
  | 30 => auxSource3461
  | 31 => auxSource3462
  | _ => .old 0

compact_certificate theorem actual_source_43 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock43 i.val))=source (i.val+1376) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_43 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock43 i.val))=tail (i.val+1376) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_43
#print axioms actual_tail_43

compact_certificate def actualBlock44 : ℕ → SourceRow
  | 0 => auxSource3463
  | 1 => auxSource3455
  | 2 => auxSource3456
  | 3 => auxSource3457
  | 4 => auxSource4348
  | 5 => auxSource4349
  | 6 => auxSource4350
  | 7 => auxSource4447
  | 8 => auxSource4351
  | 9 => auxSource4352
  | 10 => auxSource4353
  | 11 => auxSource4354
  | 12 => auxSource4355
  | 13 => auxSource4356
  | 14 => auxSource4357
  | 15 => auxSource4358
  | 16 => auxSource4359
  | 17 => auxSource4384
  | 18 => auxSource2902
  | 19 => auxSource2903
  | 20 => auxSource2904
  | 21 => auxSource2905
  | 22 => auxSource2906
  | 23 => auxSource2907
  | 24 => auxSource2908
  | 25 => auxSource2909
  | 26 => auxSource2910
  | 27 => auxSource2911
  | 28 => auxSource2912
  | 29 => auxSource2913
  | 30 => auxSource2914
  | 31 => auxSource2915
  | _ => .old 0

compact_certificate theorem actual_source_44 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock44 i.val))=source (i.val+1408) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_44 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock44 i.val))=tail (i.val+1408) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_44
#print axioms actual_tail_44

compact_certificate def actualBlock45 : ℕ → SourceRow
  | 0 => auxSource2916
  | 1 => auxSource2917
  | 2 => auxSource2918
  | 3 => auxSource2919
  | 4 => auxSource2920
  | 5 => auxSource2921
  | 6 => auxSource2922
  | 7 => auxSource2923
  | 8 => auxSource2924
  | 9 => auxSource2925
  | 10 => auxSource4419
  | 11 => auxSource2926
  | 12 => auxSource2927
  | 13 => auxSource2928
  | 14 => auxSource2929
  | 15 => auxSource2930
  | 16 => auxSource2931
  | 17 => auxSource2932
  | 18 => auxSource2933
  | 19 => auxSource2934
  | 20 => auxSource2935
  | 21 => auxSource2936
  | 22 => auxSource2937
  | 23 => auxSource2938
  | 24 => auxSource2939
  | 25 => auxSource2940
  | 26 => auxSource2941
  | 27 => auxSource2942
  | 28 => auxSource2943
  | 29 => auxSource2944
  | 30 => auxSource2945
  | 31 => auxSource2946
  | _ => .old 0

compact_certificate theorem actual_source_45 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock45 i.val))=source (i.val+1440) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_45 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock45 i.val))=tail (i.val+1440) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_45
#print axioms actual_tail_45

compact_certificate def actualBlock46 : ℕ → SourceRow
  | 0 => auxSource2947
  | 1 => auxSource2948
  | 2 => auxSource2949
  | 3 => auxSource4176
  | 4 => auxSource4177
  | 5 => auxSource4178
  | 6 => auxSource4179
  | 7 => auxSource3711
  | 8 => auxSource3712
  | 9 => auxSource3713
  | 10 => auxSource3714
  | 11 => auxSource3715
  | 12 => auxSource3716
  | 13 => auxSource3717
  | 14 => auxSource3718
  | 15 => auxSource3719
  | 16 => auxSource3720
  | 17 => auxSource3721
  | 18 => auxSource3722
  | 19 => auxSource3723
  | 20 => auxSource3724
  | 21 => auxSource3725
  | 22 => auxSource3726
  | 23 => auxSource3727
  | 24 => auxSource4432
  | 25 => auxSource3728
  | 26 => auxSource3729
  | 27 => auxSource3730
  | 28 => auxSource3731
  | 29 => auxSource3732
  | 30 => auxSource3733
  | 31 => auxSource3734
  | _ => .old 0

compact_certificate theorem actual_source_46 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock46 i.val))=source (i.val+1472) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_46 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock46 i.val))=tail (i.val+1472) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_46
#print axioms actual_tail_46

compact_certificate def actualBlock47 : ℕ → SourceRow
  | 0 => auxSource3735
  | 1 => auxSource3736
  | 2 => auxSource3737
  | 3 => auxSource3738
  | 4 => auxSource3739
  | 5 => auxSource3740
  | 6 => auxSource3741
  | 7 => auxSource3742
  | 8 => auxSource3743
  | 9 => auxSource3744
  | 10 => auxSource3745
  | 11 => auxSource3746
  | 12 => auxSource3747
  | 13 => auxSource3748
  | 14 => auxSource3749
  | 15 => auxSource3750
  | 16 => auxSource3751
  | 17 => auxSource3752
  | 18 => auxSource3753
  | 19 => auxSource3471
  | 20 => auxSource3472
  | 21 => auxSource3473
  | 22 => auxSource3474
  | 23 => auxSource3475
  | 24 => auxSource3476
  | 25 => auxSource3477
  | 26 => auxSource3478
  | 27 => auxSource3479
  | 28 => auxSource3480
  | 29 => auxSource3481
  | 30 => auxSource3482
  | 31 => auxSource4424
  | _ => .old 0

compact_certificate theorem actual_source_47 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock47 i.val))=source (i.val+1504) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_47 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock47 i.val))=tail (i.val+1504) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_47
#print axioms actual_tail_47

compact_certificate def actualBlock48 : ℕ → SourceRow
  | 0 => auxSource3324
  | 1 => auxSource3325
  | 2 => auxSource3326
  | 3 => auxSource3327
  | 4 => auxSource3328
  | 5 => auxSource3329
  | 6 => auxSource3330
  | 7 => auxSource3331
  | 8 => auxSource3332
  | 9 => auxSource3333
  | 10 => auxSource3334
  | 11 => auxSource3335
  | 12 => auxSource3336
  | 13 => auxSource3337
  | 14 => auxSource3338
  | 15 => auxSource3339
  | 16 => auxSource3340
  | 17 => auxSource3341
  | 18 => auxSource3342
  | 19 => auxSource3343
  | 20 => auxSource3344
  | 21 => auxSource3345
  | 22 => auxSource3346
  | 23 => auxSource3347
  | 24 => auxSource3348
  | 25 => auxSource3349
  | 26 => auxSource3350
  | 27 => auxSource3351
  | 28 => auxSource3352
  | 29 => auxSource3353
  | 30 => auxSource3354
  | 31 => auxSource3355
  | _ => .old 0

compact_certificate theorem actual_source_48 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock48 i.val))=source (i.val+1536) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_48 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock48 i.val))=tail (i.val+1536) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_48
#print axioms actual_tail_48

compact_certificate def actualBlock49 : ℕ → SourceRow
  | 0 => auxSource3356
  | 1 => auxSource3357
  | 2 => auxSource3358
  | 3 => auxSource3359
  | 4 => auxSource3360
  | 5 => auxSource3361
  | 6 => auxSource3362
  | 7 => auxSource3363
  | 8 => auxSource3364
  | 9 => auxSource3365
  | 10 => auxSource3366
  | 11 => auxSource3367
  | 12 => auxSource3368
  | 13 => auxSource3369
  | 14 => auxSource3370
  | 15 => auxSource3371
  | 16 => auxSource3372
  | 17 => auxSource3373
  | 18 => auxSource3374
  | 19 => auxSource3375
  | 20 => auxSource3376
  | 21 => auxSource3377
  | 22 => auxSource3378
  | 23 => auxSource3379
  | 24 => auxSource3380
  | 25 => auxSource3381
  | 26 => auxSource3382
  | 27 => auxSource3383
  | 28 => auxSource2842
  | 29 => auxSource2843
  | 30 => auxSource2844
  | 31 => auxSource2845
  | _ => .old 0

compact_certificate theorem actual_source_49 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock49 i.val))=source (i.val+1568) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_49 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock49 i.val))=tail (i.val+1568) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_49
#print axioms actual_tail_49

compact_certificate def actualBlock50 : ℕ → SourceRow
  | 0 => auxSource2846
  | 1 => auxSource2847
  | 2 => auxSource3783
  | 3 => auxSource3784
  | 4 => auxSource3785
  | 5 => auxSource3786
  | 6 => auxSource3787
  | 7 => auxSource3788
  | 8 => auxSource3789
  | 9 => auxSource3790
  | 10 => auxSource3791
  | 11 => auxSource4434
  | 12 => auxSource3792
  | 13 => auxSource3793
  | 14 => auxSource3794
  | 15 => auxSource3795
  | 16 => auxSource3796
  | 17 => auxSource2721
  | 18 => auxSource2899
  | 19 => auxSource2900
  | 20 => auxSource2901
  | 21 => auxSource2286
  | 22 => auxSource2287
  | 23 => auxSource2288
  | 24 => auxSource2289
  | 25 => auxSource2290
  | 26 => auxSource2291
  | 27 => auxSource4340
  | 28 => auxSource4341
  | 29 => auxSource3975
  | 30 => auxSource3976
  | 31 => auxSource3977
  | _ => .old 0

compact_certificate theorem actual_source_50 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock50 i.val))=source (i.val+1600) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_50 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock50 i.val))=tail (i.val+1600) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_50
#print axioms actual_tail_50

compact_certificate def actualBlock51 : ℕ → SourceRow
  | 0 => auxSource3978
  | 1 => auxSource3979
  | 2 => auxSource3980
  | 3 => auxSource3981
  | 4 => auxSource3982
  | 5 => auxSource3983
  | 6 => auxSource3984
  | 7 => auxSource3985
  | 8 => auxSource3986
  | 9 => auxSource2661
  | 10 => auxSource2662
  | 11 => auxSource2663
  | 12 => auxSource2664
  | 13 => auxSource2665
  | 14 => auxSource2666
  | 15 => auxSource2667
  | 16 => auxSource2668
  | 17 => auxSource2669
  | 18 => auxSource2670
  | 19 => auxSource2671
  | 20 => auxSource2672
  | 21 => auxSource2673
  | 22 => auxSource2674
  | 23 => auxSource2675
  | 24 => auxSource2676
  | 25 => auxSource2677
  | 26 => auxSource4414
  | 27 => auxSource2678
  | 28 => auxSource2679
  | 29 => auxSource2680
  | 30 => auxSource2681
  | 31 => auxSource2682
  | _ => .old 0

compact_certificate theorem actual_source_51 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock51 i.val))=source (i.val+1632) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_51 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock51 i.val))=tail (i.val+1632) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_51
#print axioms actual_tail_51

compact_certificate def actualBlock52 : ℕ → SourceRow
  | 0 => auxSource2683
  | 1 => auxSource2684
  | 2 => auxSource2685
  | 3 => auxSource2686
  | 4 => auxSource2687
  | 5 => auxSource2688
  | 6 => auxSource2689
  | 7 => auxSource2690
  | 8 => auxSource2691
  | 9 => auxSource2692
  | 10 => auxSource2693
  | 11 => auxSource2694
  | 12 => auxSource2695
  | 13 => auxSource2696
  | 14 => auxSource2697
  | 15 => auxSource2698
  | 16 => auxSource2699
  | 17 => auxSource2700
  | 18 => auxSource2701
  | 19 => auxSource2702
  | 20 => auxSource2703
  | 21 => auxSource2159
  | 22 => auxSource2160
  | 23 => auxSource2161
  | 24 => auxSource2162
  | 25 => auxSource2163
  | 26 => auxSource2164
  | 27 => auxSource3577
  | 28 => auxSource4376
  | 29 => auxSource4377
  | 30 => auxSource4378
  | 31 => auxSource4379
  | _ => .old 0

compact_certificate theorem actual_source_52 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock52 i.val))=source (i.val+1664) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_52 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock52 i.val))=tail (i.val+1664) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_52
#print axioms actual_tail_52

compact_certificate def actualBlock53 : ℕ → SourceRow
  | 0 => auxSource4380
  | 1 => auxSource4381
  | 2 => auxSource4382
  | 3 => auxSource4383
  | 4 => auxSource3452
  | 5 => auxSource3453
  | 6 => auxSource3454
  | 7 => auxSource4192
  | 8 => auxSource4193
  | 9 => auxSource4194
  | 10 => auxSource4195
  | 11 => auxSource4196
  | 12 => auxSource4197
  | 13 => auxSource4198
  | 14 => auxSource4199
  | 15 => auxSource4200
  | 16 => auxSource4201
  | 17 => auxSource4202
  | 18 => auxSource4203
  | 19 => auxSource4204
  | 20 => auxSource4205
  | 21 => auxSource4206
  | 22 => auxSource4207
  | 23 => auxSource4208
  | 24 => auxSource4209
  | 25 => auxSource4210
  | 26 => auxSource4211
  | 27 => auxSource4212
  | 28 => auxSource4213
  | 29 => auxSource4214
  | 30 => auxSource4215
  | 31 => auxSource4443
  | _ => .old 0

compact_certificate theorem actual_source_53 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock53 i.val))=source (i.val+1696) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_53 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock53 i.val))=tail (i.val+1696) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_53
#print axioms actual_tail_53

compact_certificate def actualBlock54 : ℕ → SourceRow
  | 0 => auxSource4216
  | 1 => auxSource4217
  | 2 => auxSource4218
  | 3 => auxSource4219
  | 4 => auxSource4220
  | 5 => auxSource4221
  | 6 => auxSource4222
  | 7 => auxSource4223
  | 8 => auxSource4224
  | 9 => auxSource4225
  | 10 => auxSource4226
  | 11 => auxSource4227
  | 12 => auxSource4228
  | 13 => auxSource4229
  | 14 => auxSource4230
  | 15 => auxSource4231
  | 16 => auxSource4232
  | 17 => auxSource4233
  | 18 => auxSource4234
  | 19 => auxSource4235
  | 20 => auxSource4236
  | 21 => auxSource4237
  | 22 => auxSource4238
  | 23 => auxSource4239
  | 24 => auxSource2443
  | 25 => auxSource2444
  | 26 => auxSource2445
  | 27 => auxSource2446
  | 28 => auxSource4337
  | 29 => auxSource4338
  | 30 => auxSource4339
  | 31 => auxSource2704
  | _ => .old 0

compact_certificate theorem actual_source_54 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock54 i.val))=source (i.val+1728) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_54 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock54 i.val))=tail (i.val+1728) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_54
#print axioms actual_tail_54

compact_certificate def actualBlock55 : ℕ → SourceRow
  | 0 => auxSource2705
  | 1 => auxSource2706
  | 2 => auxSource2707
  | 3 => auxSource2708
  | 4 => auxSource2830
  | 5 => auxSource2831
  | 6 => auxSource2832
  | 7 => auxSource2833
  | 8 => auxSource2834
  | 9 => auxSource4347
  | 10 => auxSource4371
  | 11 => auxSource4372
  | 12 => auxSource4373
  | 13 => auxSource4374
  | 14 => auxSource4375
  | 15 => auxSource2722
  | 16 => auxSource2723
  | 17 => auxSource2724
  | 18 => auxSource2725
  | 19 => auxSource2726
  | 20 => auxSource2727
  | 21 => auxSource3449
  | 22 => auxSource3696
  | 23 => auxSource3697
  | 24 => auxSource3902
  | 25 => auxSource3903
  | 26 => auxSource3904
  | 27 => auxSource3905
  | 28 => auxSource3906
  | 29 => auxSource3907
  | 30 => auxSource3908
  | 31 => auxSource3909
  | _ => .old 0

compact_certificate theorem actual_source_55 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock55 i.val))=source (i.val+1760) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_55 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock55 i.val))=tail (i.val+1760) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_55
#print axioms actual_tail_55

compact_certificate def actualBlock56 : ℕ → SourceRow
  | 0 => auxSource3910
  | 1 => auxSource3911
  | 2 => auxSource3912
  | 3 => auxSource3913
  | 4 => auxSource3914
  | 5 => auxSource3915
  | 6 => auxSource3916
  | 7 => auxSource3917
  | 8 => auxSource3918
  | 9 => auxSource3128
  | 10 => auxSource3129
  | 11 => auxSource3130
  | 12 => auxSource3131
  | 13 => auxSource3132
  | 14 => auxSource3133
  | 15 => auxSource3134
  | 16 => auxSource3135
  | 17 => auxSource3136
  | 18 => auxSource3137
  | 19 => auxSource3138
  | 20 => auxSource3139
  | 21 => auxSource3140
  | 22 => auxSource3141
  | 23 => auxSource3142
  | 24 => auxSource3143
  | 25 => auxSource3144
  | 26 => auxSource3145
  | 27 => auxSource3146
  | 28 => auxSource3147
  | 29 => auxSource3148
  | 30 => auxSource3149
  | 31 => auxSource3150
  | _ => .old 0

compact_certificate theorem actual_source_56 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock56 i.val))=source (i.val+1792) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_56 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock56 i.val))=tail (i.val+1792) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_56
#print axioms actual_tail_56

compact_certificate def actualBlock57 : ℕ → SourceRow
  | 0 => auxSource3151
  | 1 => auxSource3152
  | 2 => auxSource3153
  | 3 => auxSource3154
  | 4 => auxSource3155
  | 5 => auxSource3156
  | 6 => auxSource3157
  | 7 => auxSource3158
  | 8 => auxSource3159
  | 9 => auxSource3160
  | 10 => auxSource3161
  | 11 => auxSource3162
  | 12 => auxSource3163
  | 13 => auxSource3164
  | 14 => auxSource3165
  | 15 => auxSource3166
  | 16 => auxSource3167
  | 17 => auxSource3168
  | 18 => auxSource3169
  | 19 => auxSource3170
  | 20 => auxSource3171
  | 21 => auxSource3172
  | 22 => auxSource3173
  | 23 => auxSource3174
  | 24 => auxSource3175
  | 25 => auxSource3176
  | 26 => auxSource3177
  | 27 => auxSource3178
  | 28 => auxSource3179
  | 29 => auxSource3180
  | 30 => auxSource3181
  | 31 => auxSource3182
  | _ => .old 0

compact_certificate theorem actual_source_57 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock57 i.val))=source (i.val+1824) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_57 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock57 i.val))=tail (i.val+1824) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_57
#print axioms actual_tail_57

compact_certificate def actualBlock58 : ℕ → SourceRow
  | 0 => auxSource3183
  | 1 => auxSource3184
  | 2 => auxSource3185
  | 3 => auxSource3186
  | 4 => auxSource3187
  | 5 => auxSource3188
  | 6 => auxSource3201
  | 7 => auxSource3202
  | 8 => auxSource3203
  | 9 => auxSource3204
  | 10 => auxSource3205
  | 11 => auxSource3206
  | 12 => auxSource3207
  | 13 => auxSource2969
  | 14 => auxSource2970
  | 15 => auxSource2971
  | 16 => auxSource2972
  | 17 => auxSource2973
  | 18 => auxSource2974
  | 19 => auxSource2975
  | 20 => auxSource2976
  | 21 => auxSource2977
  | 22 => auxSource2978
  | 23 => auxSource2979
  | 24 => auxSource2980
  | 25 => auxSource2981
  | 26 => auxSource2982
  | 27 => auxSource2983
  | 28 => auxSource2984
  | 29 => auxSource2985
  | 30 => auxSource2986
  | 31 => auxSource2987
  | _ => .old 0

compact_certificate theorem actual_source_58 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock58 i.val))=source (i.val+1856) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_58 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock58 i.val))=tail (i.val+1856) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_58
#print axioms actual_tail_58

compact_certificate def actualBlock59 : ℕ → SourceRow
  | 0 => auxSource2988
  | 1 => auxSource2989
  | 2 => auxSource2990
  | 3 => auxSource2991
  | 4 => auxSource2992
  | 5 => auxSource2993
  | 6 => auxSource2994
  | 7 => auxSource4420
  | 8 => auxSource2995
  | 9 => auxSource2996
  | 10 => auxSource2997
  | 11 => auxSource2998
  | 12 => auxSource2999
  | 13 => auxSource3000
  | 14 => auxSource3001
  | 15 => auxSource3002
  | 16 => auxSource3003
  | 17 => auxSource3004
  | 18 => auxSource3005
  | 19 => auxSource3006
  | 20 => auxSource3007
  | 21 => auxSource4361
  | 22 => auxSource4362
  | 23 => auxSource4363
  | 24 => auxSource3843
  | 25 => auxSource3844
  | 26 => auxSource3845
  | 27 => auxSource3846
  | 28 => auxSource3847
  | 29 => auxSource3848
  | 30 => auxSource3849
  | 31 => auxSource3850
  | _ => .old 0

compact_certificate theorem actual_source_59 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock59 i.val))=source (i.val+1888) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_59 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock59 i.val))=tail (i.val+1888) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_59
#print axioms actual_tail_59

compact_certificate def actualBlock60 : ℕ → SourceRow
  | 0 => auxSource3851
  | 1 => auxSource3852
  | 2 => auxSource3208
  | 3 => auxSource3209
  | 4 => auxSource3210
  | 5 => auxSource3211
  | 6 => auxSource3212
  | 7 => auxSource3213
  | 8 => auxSource3214
  | 9 => auxSource3215
  | 10 => auxSource3216
  | 11 => auxSource3217
  | 12 => auxSource3218
  | 13 => auxSource3219
  | 14 => auxSource3220
  | 15 => auxSource3221
  | 16 => auxSource3222
  | 17 => auxSource3223
  | 18 => auxSource3224
  | 19 => auxSource3225
  | 20 => auxSource3226
  | 21 => auxSource3227
  | 22 => auxSource3228
  | 23 => auxSource4422
  | 24 => auxSource3229
  | 25 => auxSource3230
  | 26 => auxSource3231
  | 27 => auxSource3232
  | 28 => auxSource3233
  | 29 => auxSource3234
  | 30 => auxSource3235
  | 31 => auxSource3236
  | _ => .old 0

compact_certificate theorem actual_source_60 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock60 i.val))=source (i.val+1920) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_60 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock60 i.val))=tail (i.val+1920) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_60
#print axioms actual_tail_60

compact_certificate def actualBlock61 : ℕ → SourceRow
  | 0 => auxSource3237
  | 1 => auxSource3238
  | 2 => auxSource3239
  | 3 => auxSource3240
  | 4 => auxSource3241
  | 5 => auxSource3242
  | 6 => auxSource3243
  | 7 => auxSource3244
  | 8 => auxSource3245
  | 9 => auxSource3246
  | 10 => auxSource3247
  | 11 => auxSource3248
  | 12 => auxSource3634
  | 13 => auxSource3189
  | 14 => auxSource3190
  | 15 => auxSource3191
  | 16 => auxSource3192
  | 17 => auxSource3193
  | 18 => auxSource3194
  | 19 => auxSource3195
  | 20 => auxSource3196
  | 21 => auxSource3197
  | 22 => auxSource3198
  | 23 => auxSource3199
  | 24 => auxSource3200
  | 25 => auxSource3586
  | 26 => auxSource3587
  | 27 => auxSource3588
  | 28 => auxSource3589
  | 29 => auxSource3590
  | 30 => auxSource3591
  | 31 => auxSource3592
  | _ => .old 0

compact_certificate theorem actual_source_61 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock61 i.val))=source (i.val+1952) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_61 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock61 i.val))=tail (i.val+1952) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_61
#print axioms actual_tail_61

compact_certificate def actualBlock62 : ℕ → SourceRow
  | 0 => auxSource3593
  | 1 => auxSource3594
  | 2 => auxSource3595
  | 3 => auxSource3596
  | 4 => auxSource3597
  | 5 => auxSource3598
  | 6 => auxSource3599
  | 7 => auxSource3600
  | 8 => auxSource3601
  | 9 => auxSource3602
  | 10 => auxSource3603
  | 11 => auxSource3604
  | 12 => auxSource3605
  | 13 => auxSource3606
  | 14 => auxSource3607
  | 15 => auxSource3608
  | 16 => auxSource3609
  | 17 => auxSource4428
  | 18 => auxSource3610
  | 19 => auxSource3611
  | 20 => auxSource3612
  | 21 => auxSource3613
  | 22 => auxSource3614
  | 23 => auxSource3615
  | 24 => auxSource3616
  | 25 => auxSource3617
  | 26 => auxSource3618
  | 27 => auxSource3619
  | 28 => auxSource3620
  | 29 => auxSource3621
  | 30 => auxSource3622
  | 31 => auxSource3623
  | _ => .old 0

compact_certificate theorem actual_source_62 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock62 i.val))=source (i.val+1984) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_62 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock62 i.val))=tail (i.val+1984) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_62
#print axioms actual_tail_62

compact_certificate def actualBlock63 : ℕ → SourceRow
  | 0 => auxSource3624
  | 1 => auxSource3625
  | 2 => auxSource3626
  | 3 => auxSource3627
  | 4 => auxSource3628
  | 5 => auxSource3629
  | 6 => auxSource3630
  | 7 => auxSource3631
  | 8 => auxSource3632
  | 9 => auxSource3633
  | 10 => auxSource2292
  | 11 => auxSource3067
  | 12 => auxSource3068
  | 13 => auxSource3069
  | 14 => auxSource3070
  | 15 => auxSource3071
  | 16 => auxSource3072
  | 17 => auxSource3073
  | 18 => auxSource3074
  | 19 => auxSource3075
  | 20 => auxSource3076
  | 21 => auxSource3077
  | 22 => auxSource3078
  | 23 => auxSource3079
  | 24 => auxSource3080
  | 25 => auxSource3081
  | 26 => auxSource3082
  | 27 => auxSource3083
  | 28 => auxSource3084
  | 29 => auxSource3085
  | 30 => auxSource3086
  | 31 => auxSource3087
  | _ => .old 0

compact_certificate theorem actual_source_63 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock63 i.val))=source (i.val+2016) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_63 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock63 i.val))=tail (i.val+2016) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_63
#print axioms actual_tail_63

compact_certificate def actualBlock64 : ℕ → SourceRow
  | 0 => auxSource3088
  | 1 => auxSource3089
  | 2 => auxSource3090
  | 3 => auxSource3091
  | 4 => auxSource3092
  | 5 => auxSource3093
  | 6 => auxSource3094
  | 7 => auxSource3095
  | 8 => auxSource3096
  | 9 => auxSource3097
  | 10 => auxSource3098
  | 11 => auxSource3099
  | 12 => auxSource3100
  | 13 => auxSource3101
  | 14 => auxSource3102
  | 15 => auxSource3103
  | 16 => auxSource3104
  | 17 => auxSource3105
  | 18 => auxSource3106
  | 19 => auxSource3107
  | 20 => auxSource3108
  | 21 => auxSource3109
  | 22 => auxSource3110
  | 23 => auxSource3111
  | 24 => auxSource3112
  | 25 => auxSource3113
  | 26 => auxSource3114
  | 27 => auxSource3115
  | 28 => auxSource3116
  | 29 => auxSource3117
  | 30 => auxSource3118
  | 31 => auxSource3119
  | _ => .old 0

compact_certificate theorem actual_source_64 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock64 i.val))=source (i.val+2048) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_64 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock64 i.val))=tail (i.val+2048) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_64
#print axioms actual_tail_64

compact_certificate def actualBlock65 : ℕ → SourceRow
  | 0 => auxSource3120
  | 1 => auxSource3121
  | 2 => auxSource3122
  | 3 => auxSource3123
  | 4 => auxSource3124
  | 5 => auxSource3125
  | 6 => auxSource3126
  | 7 => auxSource3127
  | 8 => auxSource4390
  | 9 => auxSource4391
  | 10 => auxSource4392
  | 11 => auxSource4449
  | 12 => auxSource4393
  | 13 => auxSource4394
  | 14 => auxSource4395
  | 15 => auxSource2452
  | 16 => auxSource2453
  | 17 => auxSource2851
  | 18 => auxSource2852
  | 19 => auxSource2853
  | 20 => auxSource2854
  | 21 => auxSource2855
  | 22 => auxSource2856
  | 23 => auxSource2857
  | 24 => auxSource2858
  | 25 => auxSource2859
  | 26 => auxSource2860
  | 27 => auxSource2861
  | 28 => auxSource2862
  | 29 => auxSource2863
  | 30 => auxSource2864
  | 31 => auxSource2865
  | _ => .old 0

compact_certificate theorem actual_source_65 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock65 i.val))=source (i.val+2080) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_65 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock65 i.val))=tail (i.val+2080) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_65
#print axioms actual_tail_65

compact_certificate def actualBlock66 : ℕ → SourceRow
  | 0 => auxSource2866
  | 1 => auxSource2867
  | 2 => auxSource2868
  | 3 => auxSource2869
  | 4 => auxSource2870
  | 5 => auxSource2871
  | 6 => auxSource2872
  | 7 => auxSource2873
  | 8 => auxSource2874
  | 9 => auxSource4418
  | 10 => auxSource2875
  | 11 => auxSource2876
  | 12 => auxSource2877
  | 13 => auxSource2878
  | 14 => auxSource2879
  | 15 => auxSource2880
  | 16 => auxSource2881
  | 17 => auxSource2882
  | 18 => auxSource2883
  | 19 => auxSource2884
  | 20 => auxSource2885
  | 21 => auxSource2886
  | 22 => auxSource2887
  | 23 => auxSource2888
  | 24 => auxSource2889
  | 25 => auxSource2890
  | 26 => auxSource2891
  | 27 => auxSource2892
  | 28 => auxSource2893
  | 29 => auxSource2894
  | 30 => auxSource2895
  | 31 => auxSource2896
  | _ => .old 0

compact_certificate theorem actual_source_66 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock66 i.val))=source (i.val+2112) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_66 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock66 i.val))=tail (i.val+2112) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_66
#print axioms actual_tail_66

compact_certificate def actualBlock67 : ℕ → SourceRow
  | 0 => auxSource2897
  | 1 => auxSource2898
  | 2 => auxSource4124
  | 3 => auxSource4125
  | 4 => auxSource4126
  | 5 => auxSource4127
  | 6 => auxSource4128
  | 7 => auxSource4129
  | 8 => auxSource4130
  | 9 => auxSource4131
  | 10 => auxSource4132
  | 11 => auxSource4133
  | 12 => auxSource4134
  | 13 => auxSource4135
  | 14 => auxSource4136
  | 15 => auxSource4441
  | 16 => auxSource4137
  | 17 => auxSource4138
  | 18 => auxSource4139
  | 19 => auxSource4140
  | 20 => auxSource4141
  | 21 => auxSource4142
  | 22 => auxSource4143
  | 23 => auxSource4144
  | 24 => auxSource4145
  | 25 => auxSource4146
  | 26 => auxSource4147
  | 27 => auxSource4148
  | 28 => auxSource4149
  | 29 => auxSource4150
  | 30 => auxSource4151
  | 31 => auxSource4152
  | _ => .old 0

compact_certificate theorem actual_source_67 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock67 i.val))=source (i.val+2144) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_67 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock67 i.val))=tail (i.val+2144) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_67
#print axioms actual_tail_67

compact_certificate def actualBlock68 : ℕ → SourceRow
  | 0 => auxSource4153
  | 1 => auxSource4154
  | 2 => auxSource4155
  | 3 => auxSource4156
  | 4 => auxSource4157
  | 5 => auxSource4158
  | 6 => auxSource4159
  | 7 => auxSource4160
  | 8 => auxSource4161
  | 9 => auxSource4162
  | 10 => auxSource2450
  | 11 => auxSource2451
  | 12 => auxSource3853
  | 13 => auxSource3388
  | 14 => auxSource3522
  | 15 => auxSource3523
  | 16 => auxSource3524
  | 17 => auxSource2362
  | 18 => auxSource2363
  | 19 => auxSource2364
  | 20 => auxSource2365
  | 21 => auxSource4406
  | 22 => auxSource2366
  | 23 => auxSource2367
  | 24 => auxSource2368
  | 25 => auxSource2369
  | 26 => auxSource2370
  | 27 => auxSource2371
  | 28 => auxSource2372
  | 29 => auxSource2373
  | 30 => auxSource2374
  | 31 => auxSource2819
  | _ => .old 0

compact_certificate theorem actual_source_68 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock68 i.val))=source (i.val+2176) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_68 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock68 i.val))=tail (i.val+2176) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_68
#print axioms actual_tail_68

compact_certificate def actualBlock69 : ℕ → SourceRow
  | 0 => auxSource2820
  | 1 => auxSource2821
  | 2 => auxSource2822
  | 3 => auxSource2823
  | 4 => auxSource2824
  | 5 => auxSource2825
  | 6 => auxSource2826
  | 7 => auxSource2827
  | 8 => auxSource2828
  | 9 => auxSource4315
  | 10 => auxSource4256
  | 11 => auxSource4257
  | 12 => auxSource4258
  | 13 => auxSource4259
  | 14 => auxSource4260
  | 15 => auxSource4261
  | 16 => auxSource4262
  | 17 => auxSource4263
  | 18 => auxSource4264
  | 19 => auxSource4444
  | 20 => auxSource4265
  | 21 => auxSource4266
  | 22 => auxSource4267
  | 23 => auxSource4268
  | 24 => auxSource4269
  | 25 => auxSource4270
  | 26 => auxSource4271
  | 27 => auxSource4272
  | 28 => auxSource4273
  | 29 => auxSource4346
  | 30 => auxSource2447
  | 31 => auxSource3958
  | _ => .old 0

compact_certificate theorem actual_source_69 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock69 i.val))=source (i.val+2208) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_69 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock69 i.val))=tail (i.val+2208) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_69
#print axioms actual_tail_69

compact_certificate def actualBlock70 : ℕ → SourceRow
  | 0 => auxSource3959
  | 1 => auxSource3960
  | 2 => auxSource3961
  | 3 => auxSource4438
  | 4 => auxSource3962
  | 5 => auxSource3963
  | 6 => auxSource3964
  | 7 => auxSource3965
  | 8 => auxSource3966
  | 9 => auxSource3967
  | 10 => auxSource3968
  | 11 => auxSource3969
  | 12 => auxSource3970
  | 13 => auxSource2835
  | 14 => auxSource2836
  | 15 => auxSource2837
  | 16 => auxSource2838
  | 17 => auxSource2839
  | 18 => auxSource2848
  | 19 => auxSource2849
  | 20 => auxSource2850
  | 21 => auxSource4370
  | 22 => auxSource2439
  | 23 => auxSource2440
  | 24 => auxSource2441
  | 25 => auxSource2442
  | 26 => auxSource2957
  | 27 => auxSource2958
  | 28 => auxSource2959
  | 29 => auxSource2960
  | 30 => auxSource2961
  | 31 => auxSource2962
  | _ => .old 0

compact_certificate theorem actual_source_70 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock70 i.val))=source (i.val+2240) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_70 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock70 i.val))=tail (i.val+2240) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_70
#print axioms actual_tail_70

compact_certificate def actualBlock71 : ℕ → SourceRow
  | 0 => auxSource2963
  | 1 => auxSource2964
  | 2 => auxSource2965
  | 3 => auxSource2966
  | 4 => auxSource2967
  | 5 => auxSource2968
  | 6 => auxSource4107
  | 7 => auxSource4108
  | 8 => auxSource4109
  | 9 => auxSource4110
  | 10 => auxSource4111
  | 11 => auxSource4112
  | 12 => auxSource4113
  | 13 => auxSource4114
  | 14 => auxSource4115
  | 15 => auxSource4116
  | 16 => auxSource4117
  | 17 => auxSource4118
  | 18 => auxSource4119
  | 19 => auxSource4120
  | 20 => auxSource4121
  | 21 => auxSource4122
  | 22 => auxSource4123
  | 23 => auxSource2131
  | 24 => auxSource81
  | 25 => auxSource80
  | 26 => auxSource82
  | 27 => auxSource79
  | 28 => auxSource83
  | 29 => auxSource78
  | 30 => auxSource84
  | 31 => auxSource77
  | _ => .old 0

compact_certificate theorem actual_source_71 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock71 i.val))=source (i.val+2272) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_71 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock71 i.val))=tail (i.val+2272) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_71
#print axioms actual_tail_71

compact_certificate def actualBlock72 : ℕ → SourceRow
  | 0 => auxSource85
  | 1 => auxSource76
  | 2 => auxSource86
  | 3 => auxSource75
  | 4 => auxSource87
  | 5 => auxSource74
  | 6 => auxSource88
  | 7 => auxSource73
  | 8 => auxSource89
  | 9 => auxSource72
  | 10 => auxSource90
  | 11 => auxSource71
  | 12 => auxSource91
  | 13 => auxSource70
  | 14 => auxSource92
  | 15 => auxSource69
  | 16 => auxSource93
  | 17 => auxSource68
  | 18 => auxSource94
  | 19 => auxSource67
  | 20 => auxSource95
  | 21 => auxSource66
  | 22 => auxSource96
  | 23 => auxSource65
  | 24 => auxSource97
  | 25 => auxSource64
  | 26 => auxSource98
  | 27 => auxSource63
  | 28 => auxSource99
  | 29 => auxSource62
  | 30 => auxSource100
  | 31 => auxSource61
  | _ => .old 0

compact_certificate theorem actual_source_72 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock72 i.val))=source (i.val+2304) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_72 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock72 i.val))=tail (i.val+2304) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_72
#print axioms actual_tail_72

compact_certificate def actualBlock73 : ℕ → SourceRow
  | 0 => auxSource101
  | 1 => auxSource60
  | 2 => auxSource102
  | 3 => auxSource59
  | 4 => auxSource103
  | 5 => auxSource58
  | 6 => auxSource104
  | 7 => auxSource57
  | 8 => auxSource105
  | 9 => auxSource56
  | 10 => auxSource106
  | 11 => auxSource55
  | 12 => auxSource107
  | 13 => auxSource54
  | 14 => auxSource108
  | 15 => auxSource53
  | 16 => auxSource109
  | 17 => auxSource52
  | 18 => auxSource110
  | 19 => auxSource51
  | 20 => auxSource111
  | 21 => auxSource50
  | 22 => auxSource112
  | 23 => auxSource49
  | 24 => auxSource113
  | 25 => auxSource48
  | 26 => auxSource114
  | 27 => auxSource47
  | 28 => auxSource115
  | 29 => auxSource46
  | 30 => auxSource116
  | 31 => auxSource45
  | _ => .old 0

compact_certificate theorem actual_source_73 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock73 i.val))=source (i.val+2336) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_73 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock73 i.val))=tail (i.val+2336) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_73
#print axioms actual_tail_73

compact_certificate def actualBlock74 : ℕ → SourceRow
  | 0 => auxSource117
  | 1 => auxSource44
  | 2 => auxSource118
  | 3 => auxSource43
  | 4 => auxSource119
  | 5 => auxSource42
  | 6 => auxSource120
  | 7 => auxSource41
  | 8 => auxSource121
  | 9 => auxSource40
  | 10 => auxSource122
  | 11 => auxSource39
  | 12 => auxSource123
  | 13 => auxSource38
  | 14 => auxSource124
  | 15 => auxSource37
  | 16 => auxSource125
  | 17 => auxSource36
  | 18 => auxSource126
  | 19 => auxSource35
  | 20 => auxSource127
  | 21 => auxSource34
  | 22 => auxSource128
  | 23 => auxSource33
  | 24 => auxSource129
  | 25 => auxSource32
  | 26 => auxSource130
  | 27 => auxSource31
  | 28 => auxSource131
  | 29 => auxSource30
  | 30 => auxSource132
  | 31 => auxSource29
  | _ => .old 0

compact_certificate theorem actual_source_74 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock74 i.val))=source (i.val+2368) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_74 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock74 i.val))=tail (i.val+2368) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_74
#print axioms actual_tail_74

compact_certificate def actualBlock75 : ℕ → SourceRow
  | 0 => auxSource133
  | 1 => auxSource28
  | 2 => auxSource134
  | 3 => auxSource27
  | 4 => auxSource135
  | 5 => auxSource26
  | 6 => auxSource136
  | 7 => auxSource25
  | 8 => auxSource137
  | 9 => auxSource24
  | 10 => auxSource138
  | 11 => auxSource23
  | 12 => auxSource139
  | 13 => auxSource22
  | 14 => auxSource140
  | 15 => auxSource21
  | 16 => auxSource141
  | 17 => auxSource20
  | 18 => auxSource142
  | 19 => auxSource19
  | 20 => auxSource143
  | 21 => auxSource18
  | 22 => auxSource144
  | 23 => auxSource17
  | 24 => auxSource145
  | 25 => auxSource16
  | 26 => auxSource146
  | 27 => auxSource15
  | 28 => auxSource147
  | 29 => auxSource14
  | 30 => auxSource148
  | 31 => auxSource13
  | _ => .old 0

compact_certificate theorem actual_source_75 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock75 i.val))=source (i.val+2400) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_75 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock75 i.val))=tail (i.val+2400) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_75
#print axioms actual_tail_75

compact_certificate def actualBlock76 : ℕ → SourceRow
  | 0 => auxSource149
  | 1 => auxSource12
  | 2 => auxSource150
  | 3 => auxSource11
  | 4 => auxSource151
  | 5 => auxSource10
  | 6 => auxSource152
  | 7 => auxSource9
  | 8 => auxSource153
  | 9 => auxSource8
  | 10 => auxSource154
  | 11 => auxSource7
  | 12 => auxSource155
  | 13 => auxSource6
  | 14 => auxSource156
  | 15 => auxSource5
  | 16 => auxSource157
  | 17 => auxSource4
  | 18 => auxSource158
  | 19 => auxSource3
  | 20 => auxSource159
  | 21 => auxSource2
  | 22 => auxSource160
  | 23 => auxSource1
  | 24 => auxSource161
  | 25 => auxSource0
  | 26 => auxSource2132
  | 27 => auxSource189
  | 28 => auxSource188
  | 29 => auxSource190
  | 30 => auxSource187
  | 31 => auxSource191
  | _ => .old 0

compact_certificate theorem actual_source_76 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock76 i.val))=source (i.val+2432) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_76 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock76 i.val))=tail (i.val+2432) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_76
#print axioms actual_tail_76

compact_certificate def actualBlock77 : ℕ → SourceRow
  | 0 => auxSource186
  | 1 => auxSource192
  | 2 => auxSource185
  | 3 => auxSource193
  | 4 => auxSource184
  | 5 => auxSource194
  | 6 => auxSource183
  | 7 => auxSource195
  | 8 => auxSource182
  | 9 => auxSource196
  | 10 => auxSource181
  | 11 => auxSource197
  | 12 => auxSource180
  | 13 => auxSource198
  | 14 => auxSource179
  | 15 => auxSource199
  | 16 => auxSource178
  | 17 => auxSource200
  | 18 => auxSource177
  | 19 => auxSource201
  | 20 => auxSource176
  | 21 => auxSource202
  | 22 => auxSource175
  | 23 => auxSource203
  | 24 => auxSource174
  | 25 => auxSource204
  | 26 => auxSource173
  | 27 => auxSource205
  | 28 => auxSource172
  | 29 => auxSource206
  | 30 => auxSource171
  | 31 => auxSource207
  | _ => .old 0

compact_certificate theorem actual_source_77 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock77 i.val))=source (i.val+2464) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_77 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock77 i.val))=tail (i.val+2464) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_77
#print axioms actual_tail_77

compact_certificate def actualBlock78 : ℕ → SourceRow
  | 0 => auxSource170
  | 1 => auxSource208
  | 2 => auxSource169
  | 3 => auxSource209
  | 4 => auxSource168
  | 5 => auxSource210
  | 6 => auxSource167
  | 7 => auxSource211
  | 8 => auxSource166
  | 9 => auxSource212
  | 10 => auxSource165
  | 11 => auxSource213
  | 12 => auxSource164
  | 13 => auxSource214
  | 14 => auxSource163
  | 15 => auxSource215
  | 16 => auxSource162
  | 17 => auxSource2133
  | 18 => auxSource243
  | 19 => auxSource242
  | 20 => auxSource244
  | 21 => auxSource241
  | 22 => auxSource245
  | 23 => auxSource240
  | 24 => auxSource246
  | 25 => auxSource239
  | 26 => auxSource247
  | 27 => auxSource238
  | 28 => auxSource248
  | 29 => auxSource237
  | 30 => auxSource249
  | 31 => auxSource236
  | _ => .old 0

compact_certificate theorem actual_source_78 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock78 i.val))=source (i.val+2496) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_78 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock78 i.val))=tail (i.val+2496) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_78
#print axioms actual_tail_78

compact_certificate def actualBlock79 : ℕ → SourceRow
  | 0 => auxSource250
  | 1 => auxSource235
  | 2 => auxSource251
  | 3 => auxSource234
  | 4 => auxSource252
  | 5 => auxSource233
  | 6 => auxSource253
  | 7 => auxSource232
  | 8 => auxSource254
  | 9 => auxSource231
  | 10 => auxSource255
  | 11 => auxSource230
  | 12 => auxSource256
  | 13 => auxSource229
  | 14 => auxSource257
  | 15 => auxSource228
  | 16 => auxSource258
  | 17 => auxSource227
  | 18 => auxSource259
  | 19 => auxSource226
  | 20 => auxSource260
  | 21 => auxSource225
  | 22 => auxSource261
  | 23 => auxSource224
  | 24 => auxSource262
  | 25 => auxSource223
  | 26 => auxSource263
  | 27 => auxSource222
  | 28 => auxSource264
  | 29 => auxSource221
  | 30 => auxSource265
  | 31 => auxSource220
  | _ => .old 0

compact_certificate theorem actual_source_79 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock79 i.val))=source (i.val+2528) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_79 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock79 i.val))=tail (i.val+2528) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_79
#print axioms actual_tail_79

compact_certificate def actualBlock80 : ℕ → SourceRow
  | 0 => auxSource266
  | 1 => auxSource219
  | 2 => auxSource267
  | 3 => auxSource218
  | 4 => auxSource268
  | 5 => auxSource217
  | 6 => auxSource269
  | 7 => auxSource216
  | 8 => auxSource2134
  | 9 => auxSource351
  | 10 => auxSource350
  | 11 => auxSource352
  | 12 => auxSource349
  | 13 => auxSource353
  | 14 => auxSource348
  | 15 => auxSource354
  | 16 => auxSource347
  | 17 => auxSource355
  | 18 => auxSource346
  | 19 => auxSource356
  | 20 => auxSource345
  | 21 => auxSource357
  | 22 => auxSource344
  | 23 => auxSource358
  | 24 => auxSource343
  | 25 => auxSource359
  | 26 => auxSource342
  | 27 => auxSource360
  | 28 => auxSource341
  | 29 => auxSource361
  | 30 => auxSource340
  | 31 => auxSource362
  | _ => .old 0

compact_certificate theorem actual_source_80 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock80 i.val))=source (i.val+2560) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_80 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock80 i.val))=tail (i.val+2560) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_80
#print axioms actual_tail_80

compact_certificate def actualBlock81 : ℕ → SourceRow
  | 0 => auxSource339
  | 1 => auxSource363
  | 2 => auxSource338
  | 3 => auxSource364
  | 4 => auxSource337
  | 5 => auxSource365
  | 6 => auxSource336
  | 7 => auxSource366
  | 8 => auxSource335
  | 9 => auxSource367
  | 10 => auxSource334
  | 11 => auxSource368
  | 12 => auxSource333
  | 13 => auxSource369
  | 14 => auxSource332
  | 15 => auxSource370
  | 16 => auxSource331
  | 17 => auxSource371
  | 18 => auxSource330
  | 19 => auxSource372
  | 20 => auxSource329
  | 21 => auxSource373
  | 22 => auxSource328
  | 23 => auxSource374
  | 24 => auxSource327
  | 25 => auxSource375
  | 26 => auxSource326
  | 27 => auxSource376
  | 28 => auxSource325
  | 29 => auxSource377
  | 30 => auxSource324
  | 31 => auxSource378
  | _ => .old 0

compact_certificate theorem actual_source_81 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock81 i.val))=source (i.val+2592) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_81 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock81 i.val))=tail (i.val+2592) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_81
#print axioms actual_tail_81

compact_certificate def actualBlock82 : ℕ → SourceRow
  | 0 => auxSource323
  | 1 => auxSource379
  | 2 => auxSource322
  | 3 => auxSource380
  | 4 => auxSource321
  | 5 => auxSource381
  | 6 => auxSource320
  | 7 => auxSource382
  | 8 => auxSource319
  | 9 => auxSource383
  | 10 => auxSource318
  | 11 => auxSource384
  | 12 => auxSource317
  | 13 => auxSource385
  | 14 => auxSource316
  | 15 => auxSource386
  | 16 => auxSource315
  | 17 => auxSource387
  | 18 => auxSource314
  | 19 => auxSource388
  | 20 => auxSource313
  | 21 => auxSource389
  | 22 => auxSource312
  | 23 => auxSource390
  | 24 => auxSource311
  | 25 => auxSource391
  | 26 => auxSource310
  | 27 => auxSource392
  | 28 => auxSource309
  | 29 => auxSource393
  | 30 => auxSource308
  | 31 => auxSource394
  | _ => .old 0

compact_certificate theorem actual_source_82 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock82 i.val))=source (i.val+2624) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_82 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock82 i.val))=tail (i.val+2624) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_82
#print axioms actual_tail_82

compact_certificate def actualBlock83 : ℕ → SourceRow
  | 0 => auxSource307
  | 1 => auxSource395
  | 2 => auxSource306
  | 3 => auxSource396
  | 4 => auxSource305
  | 5 => auxSource397
  | 6 => auxSource304
  | 7 => auxSource398
  | 8 => auxSource303
  | 9 => auxSource399
  | 10 => auxSource302
  | 11 => auxSource400
  | 12 => auxSource301
  | 13 => auxSource401
  | 14 => auxSource300
  | 15 => auxSource402
  | 16 => auxSource299
  | 17 => auxSource403
  | 18 => auxSource298
  | 19 => auxSource404
  | 20 => auxSource297
  | 21 => auxSource405
  | 22 => auxSource296
  | 23 => auxSource406
  | 24 => auxSource295
  | 25 => auxSource407
  | 26 => auxSource294
  | 27 => auxSource408
  | 28 => auxSource293
  | 29 => auxSource409
  | 30 => auxSource292
  | 31 => auxSource410
  | _ => .old 0

compact_certificate theorem actual_source_83 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock83 i.val))=source (i.val+2656) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_83 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock83 i.val))=tail (i.val+2656) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_83
#print axioms actual_tail_83

compact_certificate def actualBlock84 : ℕ → SourceRow
  | 0 => auxSource291
  | 1 => auxSource411
  | 2 => auxSource290
  | 3 => auxSource412
  | 4 => auxSource289
  | 5 => auxSource413
  | 6 => auxSource288
  | 7 => auxSource414
  | 8 => auxSource287
  | 9 => auxSource415
  | 10 => auxSource286
  | 11 => auxSource416
  | 12 => auxSource285
  | 13 => auxSource417
  | 14 => auxSource284
  | 15 => auxSource418
  | 16 => auxSource283
  | 17 => auxSource419
  | 18 => auxSource282
  | 19 => auxSource420
  | 20 => auxSource281
  | 21 => auxSource421
  | 22 => auxSource280
  | 23 => auxSource422
  | 24 => auxSource279
  | 25 => auxSource423
  | 26 => auxSource278
  | 27 => auxSource424
  | 28 => auxSource277
  | 29 => auxSource425
  | 30 => auxSource276
  | 31 => auxSource426
  | _ => .old 0

compact_certificate theorem actual_source_84 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock84 i.val))=source (i.val+2688) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_84 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock84 i.val))=tail (i.val+2688) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_84
#print axioms actual_tail_84

compact_certificate def actualBlock85 : ℕ → SourceRow
  | 0 => auxSource275
  | 1 => auxSource427
  | 2 => auxSource274
  | 3 => auxSource428
  | 4 => auxSource273
  | 5 => auxSource429
  | 6 => auxSource272
  | 7 => auxSource430
  | 8 => auxSource271
  | 9 => auxSource431
  | 10 => auxSource270
  | 11 => auxSource2135
  | 12 => auxSource441
  | 13 => auxSource440
  | 14 => auxSource442
  | 15 => auxSource439
  | 16 => auxSource443
  | 17 => auxSource438
  | 18 => auxSource444
  | 19 => auxSource437
  | 20 => auxSource445
  | 21 => auxSource436
  | 22 => auxSource446
  | 23 => auxSource435
  | 24 => auxSource447
  | 25 => auxSource434
  | 26 => auxSource448
  | 27 => auxSource433
  | 28 => auxSource449
  | 29 => auxSource432
  | 30 => auxSource2136
  | 31 => auxSource477
  | _ => .old 0

compact_certificate theorem actual_source_85 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock85 i.val))=source (i.val+2720) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_85 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock85 i.val))=tail (i.val+2720) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_85
#print axioms actual_tail_85

compact_certificate def actualBlock86 : ℕ → SourceRow
  | 0 => auxSource476
  | 1 => auxSource478
  | 2 => auxSource475
  | 3 => auxSource479
  | 4 => auxSource474
  | 5 => auxSource480
  | 6 => auxSource473
  | 7 => auxSource481
  | 8 => auxSource472
  | 9 => auxSource482
  | 10 => auxSource471
  | 11 => auxSource483
  | 12 => auxSource470
  | 13 => auxSource484
  | 14 => auxSource469
  | 15 => auxSource485
  | 16 => auxSource468
  | 17 => auxSource486
  | 18 => auxSource467
  | 19 => auxSource487
  | 20 => auxSource466
  | 21 => auxSource488
  | 22 => auxSource465
  | 23 => auxSource489
  | 24 => auxSource464
  | 25 => auxSource490
  | 26 => auxSource463
  | 27 => auxSource491
  | 28 => auxSource462
  | 29 => auxSource492
  | 30 => auxSource461
  | 31 => auxSource493
  | _ => .old 0

compact_certificate theorem actual_source_86 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock86 i.val))=source (i.val+2752) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_86 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock86 i.val))=tail (i.val+2752) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_86
#print axioms actual_tail_86

compact_certificate def actualBlock87 : ℕ → SourceRow
  | 0 => auxSource460
  | 1 => auxSource494
  | 2 => auxSource459
  | 3 => auxSource495
  | 4 => auxSource458
  | 5 => auxSource496
  | 6 => auxSource457
  | 7 => auxSource497
  | 8 => auxSource456
  | 9 => auxSource498
  | 10 => auxSource455
  | 11 => auxSource499
  | 12 => auxSource454
  | 13 => auxSource500
  | 14 => auxSource453
  | 15 => auxSource501
  | 16 => auxSource452
  | 17 => auxSource502
  | 18 => auxSource451
  | 19 => auxSource503
  | 20 => auxSource450
  | 21 => auxSource2137
  | 22 => auxSource531
  | 23 => auxSource530
  | 24 => auxSource532
  | 25 => auxSource529
  | 26 => auxSource533
  | 27 => auxSource528
  | 28 => auxSource534
  | 29 => auxSource527
  | 30 => auxSource535
  | 31 => auxSource526
  | _ => .old 0

compact_certificate theorem actual_source_87 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock87 i.val))=source (i.val+2784) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_87 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock87 i.val))=tail (i.val+2784) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_87
#print axioms actual_tail_87

compact_certificate def actualBlock88 : ℕ → SourceRow
  | 0 => auxSource536
  | 1 => auxSource525
  | 2 => auxSource537
  | 3 => auxSource524
  | 4 => auxSource538
  | 5 => auxSource523
  | 6 => auxSource539
  | 7 => auxSource522
  | 8 => auxSource540
  | 9 => auxSource521
  | 10 => auxSource541
  | 11 => auxSource520
  | 12 => auxSource542
  | 13 => auxSource519
  | 14 => auxSource543
  | 15 => auxSource518
  | 16 => auxSource544
  | 17 => auxSource517
  | 18 => auxSource545
  | 19 => auxSource516
  | 20 => auxSource546
  | 21 => auxSource515
  | 22 => auxSource547
  | 23 => auxSource514
  | 24 => auxSource548
  | 25 => auxSource513
  | 26 => auxSource549
  | 27 => auxSource512
  | 28 => auxSource550
  | 29 => auxSource511
  | 30 => auxSource551
  | 31 => auxSource510
  | _ => .old 0

compact_certificate theorem actual_source_88 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock88 i.val))=source (i.val+2816) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_88 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock88 i.val))=tail (i.val+2816) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_88
#print axioms actual_tail_88

compact_certificate def actualBlock89 : ℕ → SourceRow
  | 0 => auxSource552
  | 1 => auxSource509
  | 2 => auxSource553
  | 3 => auxSource508
  | 4 => auxSource554
  | 5 => auxSource507
  | 6 => auxSource555
  | 7 => auxSource506
  | 8 => auxSource556
  | 9 => auxSource505
  | 10 => auxSource557
  | 11 => auxSource504
  | 12 => auxSource2138
  | 13 => auxSource567
  | 14 => auxSource566
  | 15 => auxSource568
  | 16 => auxSource565
  | 17 => auxSource569
  | 18 => auxSource564
  | 19 => auxSource570
  | 20 => auxSource563
  | 21 => auxSource571
  | 22 => auxSource562
  | 23 => auxSource572
  | 24 => auxSource561
  | 25 => auxSource573
  | 26 => auxSource560
  | 27 => auxSource574
  | 28 => auxSource559
  | 29 => auxSource575
  | 30 => auxSource558
  | 31 => auxSource2139
  | _ => .old 0

compact_certificate theorem actual_source_89 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock89 i.val))=source (i.val+2848) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_89 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock89 i.val))=tail (i.val+2848) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_89
#print axioms actual_tail_89

compact_certificate def actualBlock90 : ℕ → SourceRow
  | 0 => auxSource603
  | 1 => auxSource602
  | 2 => auxSource604
  | 3 => auxSource601
  | 4 => auxSource605
  | 5 => auxSource600
  | 6 => auxSource606
  | 7 => auxSource599
  | 8 => auxSource607
  | 9 => auxSource598
  | 10 => auxSource608
  | 11 => auxSource597
  | 12 => auxSource609
  | 13 => auxSource596
  | 14 => auxSource610
  | 15 => auxSource595
  | 16 => auxSource611
  | 17 => auxSource594
  | 18 => auxSource612
  | 19 => auxSource593
  | 20 => auxSource613
  | 21 => auxSource592
  | 22 => auxSource614
  | 23 => auxSource591
  | 24 => auxSource615
  | 25 => auxSource590
  | 26 => auxSource616
  | 27 => auxSource589
  | 28 => auxSource617
  | 29 => auxSource588
  | 30 => auxSource618
  | 31 => auxSource587
  | _ => .old 0

compact_certificate theorem actual_source_90 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock90 i.val))=source (i.val+2880) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_90 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock90 i.val))=tail (i.val+2880) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_90
#print axioms actual_tail_90

compact_certificate def actualBlock91 : ℕ → SourceRow
  | 0 => auxSource619
  | 1 => auxSource586
  | 2 => auxSource620
  | 3 => auxSource585
  | 4 => auxSource621
  | 5 => auxSource584
  | 6 => auxSource622
  | 7 => auxSource583
  | 8 => auxSource623
  | 9 => auxSource582
  | 10 => auxSource624
  | 11 => auxSource581
  | 12 => auxSource625
  | 13 => auxSource580
  | 14 => auxSource626
  | 15 => auxSource579
  | 16 => auxSource627
  | 17 => auxSource578
  | 18 => auxSource628
  | 19 => auxSource577
  | 20 => auxSource629
  | 21 => auxSource576
  | 22 => auxSource2140
  | 23 => auxSource639
  | 24 => auxSource638
  | 25 => auxSource640
  | 26 => auxSource637
  | 27 => auxSource641
  | 28 => auxSource636
  | 29 => auxSource642
  | 30 => auxSource635
  | 31 => auxSource643
  | _ => .old 0

compact_certificate theorem actual_source_91 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock91 i.val))=source (i.val+2912) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_91 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock91 i.val))=tail (i.val+2912) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_91
#print axioms actual_tail_91

compact_certificate def actualBlock92 : ℕ → SourceRow
  | 0 => auxSource634
  | 1 => auxSource644
  | 2 => auxSource633
  | 3 => auxSource645
  | 4 => auxSource632
  | 5 => auxSource646
  | 6 => auxSource631
  | 7 => auxSource647
  | 8 => auxSource630
  | 9 => auxSource2141
  | 10 => auxSource675
  | 11 => auxSource674
  | 12 => auxSource676
  | 13 => auxSource673
  | 14 => auxSource677
  | 15 => auxSource672
  | 16 => auxSource678
  | 17 => auxSource671
  | 18 => auxSource679
  | 19 => auxSource670
  | 20 => auxSource680
  | 21 => auxSource669
  | 22 => auxSource681
  | 23 => auxSource668
  | 24 => auxSource682
  | 25 => auxSource667
  | 26 => auxSource683
  | 27 => auxSource666
  | 28 => auxSource684
  | 29 => auxSource665
  | 30 => auxSource685
  | 31 => auxSource664
  | _ => .old 0

compact_certificate theorem actual_source_92 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock92 i.val))=source (i.val+2944) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_92 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock92 i.val))=tail (i.val+2944) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_92
#print axioms actual_tail_92

compact_certificate def actualBlock93 : ℕ → SourceRow
  | 0 => auxSource686
  | 1 => auxSource663
  | 2 => auxSource687
  | 3 => auxSource662
  | 4 => auxSource688
  | 5 => auxSource661
  | 6 => auxSource689
  | 7 => auxSource660
  | 8 => auxSource690
  | 9 => auxSource659
  | 10 => auxSource691
  | 11 => auxSource658
  | 12 => auxSource692
  | 13 => auxSource657
  | 14 => auxSource693
  | 15 => auxSource656
  | 16 => auxSource694
  | 17 => auxSource655
  | 18 => auxSource695
  | 19 => auxSource654
  | 20 => auxSource696
  | 21 => auxSource653
  | 22 => auxSource697
  | 23 => auxSource652
  | 24 => auxSource698
  | 25 => auxSource651
  | 26 => auxSource699
  | 27 => auxSource650
  | 28 => auxSource700
  | 29 => auxSource649
  | 30 => auxSource701
  | 31 => auxSource648
  | _ => .old 0

compact_certificate theorem actual_source_93 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock93 i.val))=source (i.val+2976) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_93 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock93 i.val))=tail (i.val+2976) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_93
#print axioms actual_tail_93

compact_certificate def actualBlock94 : ℕ → SourceRow
  | 0 => auxSource2142
  | 1 => auxSource711
  | 2 => auxSource710
  | 3 => auxSource712
  | 4 => auxSource709
  | 5 => auxSource713
  | 6 => auxSource708
  | 7 => auxSource714
  | 8 => auxSource707
  | 9 => auxSource715
  | 10 => auxSource706
  | 11 => auxSource716
  | 12 => auxSource705
  | 13 => auxSource717
  | 14 => auxSource704
  | 15 => auxSource718
  | 16 => auxSource703
  | 17 => auxSource719
  | 18 => auxSource702
  | 19 => auxSource2143
  | 20 => auxSource747
  | 21 => auxSource746
  | 22 => auxSource748
  | 23 => auxSource745
  | 24 => auxSource749
  | 25 => auxSource744
  | 26 => auxSource750
  | 27 => auxSource743
  | 28 => auxSource751
  | 29 => auxSource742
  | 30 => auxSource752
  | 31 => auxSource741
  | _ => .old 0

compact_certificate theorem actual_source_94 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock94 i.val))=source (i.val+3008) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_94 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock94 i.val))=tail (i.val+3008) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_94
#print axioms actual_tail_94

compact_certificate def actualBlock95 : ℕ → SourceRow
  | 0 => auxSource753
  | 1 => auxSource740
  | 2 => auxSource754
  | 3 => auxSource739
  | 4 => auxSource755
  | 5 => auxSource738
  | 6 => auxSource756
  | 7 => auxSource737
  | 8 => auxSource757
  | 9 => auxSource736
  | 10 => auxSource758
  | 11 => auxSource735
  | 12 => auxSource759
  | 13 => auxSource734
  | 14 => auxSource760
  | 15 => auxSource733
  | 16 => auxSource761
  | 17 => auxSource732
  | 18 => auxSource762
  | 19 => auxSource731
  | 20 => auxSource763
  | 21 => auxSource730
  | 22 => auxSource764
  | 23 => auxSource729
  | 24 => auxSource765
  | 25 => auxSource728
  | 26 => auxSource766
  | 27 => auxSource727
  | 28 => auxSource767
  | 29 => auxSource726
  | 30 => auxSource768
  | 31 => auxSource725
  | _ => .old 0

compact_certificate theorem actual_source_95 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock95 i.val))=source (i.val+3040) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_95 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock95 i.val))=tail (i.val+3040) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_95
#print axioms actual_tail_95

compact_certificate def actualBlock96 : ℕ → SourceRow
  | 0 => auxSource769
  | 1 => auxSource724
  | 2 => auxSource770
  | 3 => auxSource723
  | 4 => auxSource771
  | 5 => auxSource722
  | 6 => auxSource772
  | 7 => auxSource721
  | 8 => auxSource773
  | 9 => auxSource720
  | 10 => auxSource2144
  | 11 => auxSource777
  | 12 => auxSource776
  | 13 => auxSource778
  | 14 => auxSource775
  | 15 => auxSource779
  | 16 => auxSource774
  | 17 => auxSource2145
  | 18 => auxSource789
  | 19 => auxSource788
  | 20 => auxSource790
  | 21 => auxSource787
  | 22 => auxSource791
  | 23 => auxSource786
  | 24 => auxSource792
  | 25 => auxSource785
  | 26 => auxSource793
  | 27 => auxSource784
  | 28 => auxSource794
  | 29 => auxSource783
  | 30 => auxSource795
  | 31 => auxSource782
  | _ => .old 0

compact_certificate theorem actual_source_96 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock96 i.val))=source (i.val+3072) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_96 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock96 i.val))=tail (i.val+3072) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_96
#print axioms actual_tail_96

compact_certificate def actualBlock97 : ℕ → SourceRow
  | 0 => auxSource796
  | 1 => auxSource781
  | 2 => auxSource797
  | 3 => auxSource780
  | 4 => auxSource2146
  | 5 => auxSource807
  | 6 => auxSource806
  | 7 => auxSource808
  | 8 => auxSource805
  | 9 => auxSource809
  | 10 => auxSource804
  | 11 => auxSource810
  | 12 => auxSource803
  | 13 => auxSource811
  | 14 => auxSource802
  | 15 => auxSource812
  | 16 => auxSource801
  | 17 => auxSource813
  | 18 => auxSource800
  | 19 => auxSource814
  | 20 => auxSource799
  | 21 => auxSource815
  | 22 => auxSource798
  | 23 => auxSource2147
  | 24 => auxSource825
  | 25 => auxSource824
  | 26 => auxSource826
  | 27 => auxSource823
  | 28 => auxSource827
  | 29 => auxSource822
  | 30 => auxSource828
  | 31 => auxSource821
  | _ => .old 0

compact_certificate theorem actual_source_97 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock97 i.val))=source (i.val+3104) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_97 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock97 i.val))=tail (i.val+3104) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_97
#print axioms actual_tail_97

compact_certificate theorem actual_source_98 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock98 i.val))=source (i.val+3136) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock98 j))=source (j+3136)
  have h : ∀ i<32, P (i+0) :=
    (finite_range% P 0 [
    8 => (fun i hi => actual_source_98_part0 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_98_part1 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_98_part2 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_98_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_98
compact_certificate theorem actual_tail_98 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock98 i.val))=tail (i.val+3136) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock98 j))=tail (j+3136)
  have h : ∀ i<32, P (i+0) :=
    (finite_range% P 0 [
    8 => (fun i hi => actual_tail_98_part0 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_98_part1 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_98_part2 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_98_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_98

compact_certificate theorem actual_source_99 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock99 i.val))=source (i.val+3168) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock99 j))=source (j+3168)
  have h : ∀ i<32, P (i+0) :=
    (finite_range% P 0 [
    8 => (fun i hi => actual_source_99_part0 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_99_part1 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_99_part2 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_99_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_99
compact_certificate theorem actual_tail_99 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock99 i.val))=tail (i.val+3168) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock99 j))=tail (j+3168)
  have h : ∀ i<32, P (i+0) :=
    (finite_range% P 0 [
    8 => (fun i hi => actual_tail_99_part0 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_99_part1 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_99_part2 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_99_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_99

compact_certificate theorem actual_source_100 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock100 i.val))=source (i.val+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawSourcePoly 1 (actualBlock100 j))=source (j+3200)
  have h : ∀ i<32, P (i+0) :=
    (finite_range% P 0 [
    8 => (fun i hi => actual_source_100_part0 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_100_part1 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_100_part2 ⟨i,hi⟩),
    8 => (fun i hi => actual_source_100_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_source_100
compact_certificate theorem actual_tail_100 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock100 i.val))=tail (i.val+3200) := by
  let P : ℕ → Prop := fun j => normalizedPoly (rawTailPoly (actualBlock100 j))=tail (j+3200)
  have h : ∀ i<32, P (i+0) :=
    (finite_range% P 0 [
    8 => (fun i hi => actual_tail_100_part0 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_100_part1 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_100_part2 ⟨i,hi⟩),
    8 => (fun i hi => actual_tail_100_part3 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms actual_tail_100

compact_certificate def actualBlock101 : ℕ → SourceRow
  | 0 => auxSource913
  | 1 => auxSource914
  | 2 => auxSource915
  | 3 => auxSource916
  | 4 => auxSource917
  | 5 => auxSource918
  | 6 => auxSource919
  | 7 => auxSource920
  | 8 => auxSource921
  | 9 => auxSource922
  | 10 => auxSource923
  | 11 => auxSource924
  | 12 => auxSource925
  | 13 => auxSource926
  | 14 => auxSource927
  | 15 => auxSource928
  | 16 => auxSource929
  | 17 => auxSource930
  | 18 => auxSource931
  | 19 => auxSource932
  | 20 => auxSource933
  | 21 => auxSource934
  | 22 => auxSource935
  | 23 => auxSource936
  | 24 => auxSource937
  | 25 => auxSource938
  | 26 => auxSource939
  | 27 => auxSource940
  | 28 => auxSource941
  | 29 => auxSource942
  | 30 => auxSource943
  | 31 => auxSource944
  | _ => .old 0

compact_certificate theorem actual_source_101 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock101 i.val))=source (i.val+3232) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_101 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock101 i.val))=tail (i.val+3232) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_101
#print axioms actual_tail_101

compact_certificate def actualBlock102 : ℕ → SourceRow
  | 0 => auxSource945
  | 1 => auxSource946
  | 2 => auxSource947
  | 3 => auxSource948
  | 4 => auxSource949
  | 5 => auxSource950
  | 6 => auxSource951
  | 7 => auxSource952
  | 8 => auxSource953
  | 9 => auxSource954
  | 10 => auxSource955
  | 11 => auxSource956
  | 12 => auxSource957
  | 13 => auxSource958
  | 14 => auxSource959
  | 15 => auxSource960
  | 16 => auxSource961
  | 17 => auxSource962
  | 18 => auxSource963
  | 19 => auxSource964
  | 20 => auxSource965
  | 21 => auxSource966
  | 22 => auxSource967
  | 23 => auxSource968
  | 24 => auxSource969
  | 25 => auxSource970
  | 26 => auxSource971
  | 27 => auxSource972
  | 28 => auxSource973
  | 29 => auxSource974
  | 30 => auxSource975
  | 31 => auxSource976
  | _ => .old 0

compact_certificate theorem actual_source_102 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock102 i.val))=source (i.val+3264) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_102 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock102 i.val))=tail (i.val+3264) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_102
#print axioms actual_tail_102

compact_certificate def actualBlock103 : ℕ → SourceRow
  | 0 => auxSource977
  | 1 => auxSource978
  | 2 => auxSource979
  | 3 => auxSource980
  | 4 => auxSource981
  | 5 => auxSource982
  | 6 => auxSource983
  | 7 => auxSource984
  | 8 => auxSource985
  | 9 => auxSource986
  | 10 => auxSource987
  | 11 => auxSource988
  | 12 => auxSource989
  | 13 => auxSource990
  | 14 => auxSource991
  | 15 => auxSource992
  | 16 => auxSource993
  | 17 => auxSource994
  | 18 => auxSource995
  | 19 => auxSource996
  | 20 => auxSource997
  | 21 => auxSource998
  | 22 => auxSource999
  | 23 => auxSource1000
  | 24 => auxSource1001
  | 25 => auxSource1002
  | 26 => auxSource1003
  | 27 => auxSource1004
  | 28 => auxSource1005
  | 29 => auxSource1006
  | 30 => auxSource1007
  | 31 => auxSource1008
  | _ => .old 0

compact_certificate theorem actual_source_103 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock103 i.val))=source (i.val+3296) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_103 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock103 i.val))=tail (i.val+3296) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_103
#print axioms actual_tail_103

compact_certificate def actualBlock104 : ℕ → SourceRow
  | 0 => auxSource1009
  | 1 => auxSource1010
  | 2 => auxSource1011
  | 3 => auxSource1012
  | 4 => auxSource1013
  | 5 => auxSource1014
  | 6 => auxSource1015
  | 7 => auxSource1016
  | 8 => auxSource1017
  | 9 => auxSource1018
  | 10 => auxSource1019
  | 11 => auxSource1020
  | 12 => auxSource1021
  | 13 => auxSource1022
  | 14 => auxSource1023
  | 15 => auxSource1024
  | 16 => auxSource1025
  | 17 => auxSource1026
  | 18 => auxSource1027
  | 19 => auxSource1028
  | 20 => auxSource1029
  | 21 => auxSource1030
  | 22 => auxSource1031
  | 23 => auxSource1032
  | 24 => auxSource1033
  | 25 => auxSource1034
  | 26 => auxSource1035
  | 27 => auxSource1036
  | 28 => auxSource1037
  | 29 => auxSource1038
  | 30 => auxSource1039
  | 31 => auxSource1040
  | _ => .old 0

compact_certificate theorem actual_source_104 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock104 i.val))=source (i.val+3328) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_104 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock104 i.val))=tail (i.val+3328) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_104
#print axioms actual_tail_104

compact_certificate def actualBlock105 : ℕ → SourceRow
  | 0 => auxSource1041
  | 1 => auxSource1042
  | 2 => auxSource1043
  | 3 => auxSource1044
  | 4 => auxSource1045
  | 5 => auxSource1046
  | 6 => auxSource1047
  | 7 => auxSource1048
  | 8 => auxSource1049
  | 9 => auxSource1050
  | 10 => auxSource1051
  | 11 => auxSource1052
  | 12 => auxSource1053
  | 13 => auxSource1054
  | 14 => auxSource1055
  | 15 => auxSource1056
  | 16 => auxSource1057
  | 17 => auxSource1058
  | 18 => auxSource1059
  | 19 => auxSource1060
  | 20 => auxSource1061
  | 21 => auxSource1062
  | 22 => auxSource1063
  | 23 => auxSource1064
  | 24 => auxSource1065
  | 25 => auxSource1066
  | 26 => auxSource1067
  | 27 => auxSource1068
  | 28 => auxSource1069
  | 29 => auxSource1070
  | 30 => auxSource1071
  | 31 => auxSource1072
  | _ => .old 0

compact_certificate theorem actual_source_105 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock105 i.val))=source (i.val+3360) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_105 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock105 i.val))=tail (i.val+3360) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_105
#print axioms actual_tail_105

compact_certificate def actualBlock106 : ℕ → SourceRow
  | 0 => auxSource1073
  | 1 => auxSource1074
  | 2 => auxSource1075
  | 3 => auxSource1076
  | 4 => auxSource1077
  | 5 => auxSource1078
  | 6 => auxSource1079
  | 7 => auxSource1080
  | 8 => auxSource1081
  | 9 => auxSource1082
  | 10 => auxSource1083
  | 11 => auxSource1084
  | 12 => auxSource1085
  | 13 => auxSource1086
  | 14 => auxSource1087
  | 15 => auxSource1088
  | 16 => auxSource1089
  | 17 => auxSource1090
  | 18 => auxSource1091
  | 19 => auxSource1092
  | 20 => auxSource1093
  | 21 => auxSource1094
  | 22 => auxSource1095
  | 23 => auxSource1096
  | 24 => auxSource1097
  | 25 => auxSource1098
  | 26 => auxSource1099
  | 27 => auxSource1100
  | 28 => auxSource1101
  | 29 => auxSource1102
  | 30 => auxSource1103
  | 31 => auxSource1104
  | _ => .old 0

compact_certificate theorem actual_source_106 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock106 i.val))=source (i.val+3392) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_106 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock106 i.val))=tail (i.val+3392) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_106
#print axioms actual_tail_106

compact_certificate def actualBlock107 : ℕ → SourceRow
  | 0 => auxSource1105
  | 1 => auxSource1106
  | 2 => auxSource1107
  | 3 => auxSource1108
  | 4 => auxSource1109
  | 5 => auxSource1110
  | 6 => auxSource1111
  | 7 => auxSource1112
  | 8 => auxSource1113
  | 9 => auxSource1114
  | 10 => auxSource1115
  | 11 => auxSource1116
  | 12 => auxSource1117
  | 13 => auxSource1118
  | 14 => auxSource1119
  | 15 => auxSource1120
  | 16 => auxSource1121
  | 17 => auxSource1122
  | 18 => auxSource1123
  | 19 => auxSource1124
  | 20 => auxSource1125
  | 21 => auxSource1126
  | 22 => auxSource1127
  | 23 => auxSource1128
  | 24 => auxSource1129
  | 25 => auxSource1130
  | 26 => auxSource1131
  | 27 => auxSource1132
  | 28 => auxSource1133
  | 29 => auxSource1134
  | 30 => auxSource1135
  | 31 => auxSource1136
  | _ => .old 0

compact_certificate theorem actual_source_107 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock107 i.val))=source (i.val+3424) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_107 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock107 i.val))=tail (i.val+3424) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_107
#print axioms actual_tail_107

compact_certificate def actualBlock108 : ℕ → SourceRow
  | 0 => auxSource1137
  | 1 => auxSource1138
  | 2 => auxSource1139
  | 3 => auxSource1140
  | 4 => auxSource1141
  | 5 => auxSource1142
  | 6 => auxSource1143
  | 7 => auxSource1144
  | 8 => auxSource1145
  | 9 => auxSource1146
  | 10 => auxSource1147
  | 11 => auxSource1148
  | 12 => auxSource1149
  | 13 => auxSource1150
  | 14 => auxSource1151
  | 15 => auxSource1152
  | 16 => auxSource1153
  | 17 => auxSource1154
  | 18 => auxSource1155
  | 19 => auxSource1156
  | 20 => auxSource1157
  | 21 => auxSource1158
  | 22 => auxSource1159
  | 23 => auxSource1160
  | 24 => auxSource1161
  | 25 => auxSource1162
  | 26 => auxSource1163
  | 27 => auxSource1164
  | 28 => auxSource1165
  | 29 => auxSource1166
  | 30 => auxSource1167
  | 31 => auxSource1168
  | _ => .old 0

compact_certificate theorem actual_source_108 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock108 i.val))=source (i.val+3456) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_108 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock108 i.val))=tail (i.val+3456) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_108
#print axioms actual_tail_108

compact_certificate def actualBlock109 : ℕ → SourceRow
  | 0 => auxSource1169
  | 1 => auxSource1170
  | 2 => auxSource1171
  | 3 => auxSource1172
  | 4 => auxSource1173
  | 5 => auxSource1174
  | 6 => auxSource1175
  | 7 => auxSource1176
  | 8 => auxSource1177
  | 9 => auxSource1178
  | 10 => auxSource1179
  | 11 => auxSource1180
  | 12 => auxSource1181
  | 13 => auxSource1182
  | 14 => auxSource1183
  | 15 => auxSource1184
  | 16 => auxSource1185
  | 17 => auxSource1186
  | 18 => auxSource1187
  | 19 => auxSource1188
  | 20 => auxSource1189
  | 21 => auxSource1190
  | 22 => auxSource1191
  | 23 => auxSource1192
  | 24 => auxSource1193
  | 25 => auxSource1194
  | 26 => auxSource1195
  | 27 => auxSource1196
  | 28 => auxSource1197
  | 29 => auxSource1198
  | 30 => auxSource1199
  | 31 => auxSource1200
  | _ => .old 0

compact_certificate theorem actual_source_109 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock109 i.val))=source (i.val+3488) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_109 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock109 i.val))=tail (i.val+3488) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_109
#print axioms actual_tail_109

compact_certificate def actualBlock110 : ℕ → SourceRow
  | 0 => auxSource1201
  | 1 => auxSource1202
  | 2 => auxSource1203
  | 3 => auxSource1204
  | 4 => auxSource1205
  | 5 => auxSource1206
  | 6 => auxSource1207
  | 7 => auxSource1208
  | 8 => auxSource1209
  | 9 => auxSource1210
  | 10 => auxSource1211
  | 11 => auxSource1212
  | 12 => auxSource1213
  | 13 => auxSource1214
  | 14 => auxSource1215
  | 15 => auxSource1216
  | 16 => auxSource1217
  | 17 => auxSource1218
  | 18 => auxSource1219
  | 19 => auxSource1220
  | 20 => auxSource1221
  | 21 => auxSource1222
  | 22 => auxSource1223
  | 23 => auxSource1224
  | 24 => auxSource1225
  | 25 => auxSource1226
  | 26 => auxSource1227
  | 27 => auxSource1228
  | 28 => auxSource1229
  | 29 => auxSource1230
  | 30 => auxSource1231
  | 31 => auxSource1232
  | _ => .old 0

compact_certificate theorem actual_source_110 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock110 i.val))=source (i.val+3520) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_110 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock110 i.val))=tail (i.val+3520) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_110
#print axioms actual_tail_110

compact_certificate def actualBlock111 : ℕ → SourceRow
  | 0 => auxSource1233
  | 1 => auxSource1234
  | 2 => auxSource1235
  | 3 => auxSource1236
  | 4 => auxSource1237
  | 5 => auxSource1238
  | 6 => auxSource1239
  | 7 => auxSource1240
  | 8 => auxSource1241
  | 9 => auxSource1242
  | 10 => auxSource1243
  | 11 => auxSource1244
  | 12 => auxSource1245
  | 13 => auxSource1246
  | 14 => auxSource1247
  | 15 => auxSource1248
  | 16 => auxSource1249
  | 17 => auxSource1250
  | 18 => auxSource1251
  | 19 => auxSource1252
  | 20 => auxSource1253
  | 21 => auxSource1254
  | 22 => auxSource1255
  | 23 => auxSource1256
  | 24 => auxSource1257
  | 25 => auxSource1258
  | 26 => auxSource1259
  | 27 => auxSource1260
  | 28 => auxSource1261
  | 29 => auxSource1262
  | 30 => auxSource1263
  | 31 => auxSource1264
  | _ => .old 0

compact_certificate theorem actual_source_111 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock111 i.val))=source (i.val+3552) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_111 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock111 i.val))=tail (i.val+3552) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_111
#print axioms actual_tail_111

compact_certificate def actualBlock112 : ℕ → SourceRow
  | 0 => auxSource1265
  | 1 => auxSource1266
  | 2 => auxSource1267
  | 3 => auxSource1268
  | 4 => auxSource1269
  | 5 => auxSource1270
  | 6 => auxSource1271
  | 7 => auxSource1272
  | 8 => auxSource1273
  | 9 => auxSource1274
  | 10 => auxSource1275
  | 11 => auxSource1276
  | 12 => auxSource1277
  | 13 => auxSource1278
  | 14 => auxSource1279
  | 15 => auxSource1280
  | 16 => auxSource1281
  | 17 => auxSource1282
  | 18 => auxSource1283
  | 19 => auxSource1284
  | 20 => auxSource1285
  | 21 => auxSource1286
  | 22 => auxSource1287
  | 23 => auxSource1288
  | 24 => auxSource1289
  | 25 => auxSource1290
  | 26 => auxSource1291
  | 27 => auxSource1292
  | 28 => auxSource1293
  | 29 => auxSource1294
  | 30 => auxSource1295
  | 31 => auxSource1296
  | _ => .old 0

compact_certificate theorem actual_source_112 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock112 i.val))=source (i.val+3584) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_112 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock112 i.val))=tail (i.val+3584) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_112
#print axioms actual_tail_112

compact_certificate def actualBlock113 : ℕ → SourceRow
  | 0 => auxSource1297
  | 1 => auxSource1298
  | 2 => auxSource1299
  | 3 => auxSource1300
  | 4 => auxSource1301
  | 5 => auxSource1302
  | 6 => auxSource1303
  | 7 => auxSource1304
  | 8 => auxSource1305
  | 9 => auxSource1306
  | 10 => auxSource1307
  | 11 => auxSource1308
  | 12 => auxSource1309
  | 13 => auxSource1310
  | 14 => auxSource1311
  | 15 => auxSource1312
  | 16 => auxSource1313
  | 17 => auxSource1314
  | 18 => auxSource1315
  | 19 => auxSource1316
  | 20 => auxSource1317
  | 21 => auxSource1318
  | 22 => auxSource1319
  | 23 => auxSource1320
  | 24 => auxSource1321
  | 25 => auxSource1322
  | 26 => auxSource1323
  | 27 => auxSource1324
  | 28 => auxSource1325
  | 29 => auxSource1326
  | 30 => auxSource1327
  | 31 => auxSource1328
  | _ => .old 0

compact_certificate theorem actual_source_113 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock113 i.val))=source (i.val+3616) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_113 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock113 i.val))=tail (i.val+3616) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_113
#print axioms actual_tail_113

compact_certificate def actualBlock114 : ℕ → SourceRow
  | 0 => auxSource1329
  | 1 => auxSource1330
  | 2 => auxSource1331
  | 3 => auxSource1332
  | 4 => auxSource1333
  | 5 => auxSource1334
  | 6 => auxSource1335
  | 7 => auxSource1336
  | 8 => auxSource1337
  | 9 => auxSource1338
  | 10 => auxSource1339
  | 11 => auxSource1340
  | 12 => auxSource1341
  | 13 => auxSource1342
  | 14 => auxSource1343
  | 15 => auxSource1344
  | 16 => auxSource1345
  | 17 => auxSource1346
  | 18 => auxSource1347
  | 19 => auxSource1348
  | 20 => auxSource1349
  | 21 => auxSource1350
  | 22 => auxSource1351
  | 23 => auxSource1352
  | 24 => auxSource1353
  | 25 => auxSource1354
  | 26 => auxSource1355
  | 27 => auxSource1356
  | 28 => auxSource1357
  | 29 => auxSource1358
  | 30 => auxSource1359
  | 31 => auxSource1360
  | _ => .old 0

compact_certificate theorem actual_source_114 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock114 i.val))=source (i.val+3648) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_114 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock114 i.val))=tail (i.val+3648) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_114
#print axioms actual_tail_114

compact_certificate def actualBlock115 : ℕ → SourceRow
  | 0 => auxSource1361
  | 1 => auxSource1362
  | 2 => auxSource1363
  | 3 => auxSource1364
  | 4 => auxSource1365
  | 5 => auxSource1366
  | 6 => auxSource1367
  | 7 => auxSource1368
  | 8 => auxSource1369
  | 9 => auxSource1370
  | 10 => auxSource1371
  | 11 => auxSource1372
  | 12 => auxSource1373
  | 13 => auxSource1374
  | 14 => auxSource1375
  | 15 => auxSource1376
  | 16 => auxSource1377
  | 17 => auxSource1378
  | 18 => auxSource1379
  | 19 => auxSource1380
  | 20 => auxSource1381
  | 21 => auxSource1382
  | 22 => auxSource1383
  | 23 => auxSource1384
  | 24 => auxSource1385
  | 25 => auxSource1386
  | 26 => auxSource1387
  | 27 => auxSource1388
  | 28 => auxSource1389
  | 29 => auxSource1390
  | 30 => auxSource1391
  | 31 => auxSource1392
  | _ => .old 0

compact_certificate theorem actual_source_115 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock115 i.val))=source (i.val+3680) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_115 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock115 i.val))=tail (i.val+3680) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_115
#print axioms actual_tail_115

compact_certificate def actualBlock116 : ℕ → SourceRow
  | 0 => auxSource1393
  | 1 => auxSource1394
  | 2 => auxSource1395
  | 3 => auxSource1396
  | 4 => auxSource1397
  | 5 => auxSource1398
  | 6 => auxSource1399
  | 7 => auxSource1400
  | 8 => auxSource1401
  | 9 => auxSource1402
  | 10 => auxSource1403
  | 11 => auxSource1404
  | 12 => auxSource1405
  | 13 => auxSource1406
  | 14 => auxSource1407
  | 15 => auxSource1408
  | 16 => auxSource1409
  | 17 => auxSource1410
  | 18 => auxSource1411
  | 19 => auxSource1412
  | 20 => auxSource1413
  | 21 => auxSource1414
  | 22 => auxSource1415
  | 23 => auxSource1416
  | 24 => auxSource1417
  | 25 => auxSource1418
  | 26 => auxSource1419
  | 27 => auxSource1420
  | 28 => auxSource1421
  | 29 => auxSource1422
  | 30 => auxSource1423
  | 31 => auxSource1424
  | _ => .old 0

compact_certificate theorem actual_source_116 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock116 i.val))=source (i.val+3712) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_116 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock116 i.val))=tail (i.val+3712) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_116
#print axioms actual_tail_116

compact_certificate def actualBlock117 : ℕ → SourceRow
  | 0 => auxSource1425
  | 1 => auxSource1426
  | 2 => auxSource1427
  | 3 => auxSource1428
  | 4 => auxSource1429
  | 5 => auxSource1430
  | 6 => auxSource1431
  | 7 => auxSource1432
  | 8 => auxSource1433
  | 9 => auxSource1434
  | 10 => auxSource1435
  | 11 => auxSource1436
  | 12 => auxSource1437
  | 13 => auxSource1438
  | 14 => auxSource1439
  | 15 => auxSource1440
  | 16 => auxSource1441
  | 17 => auxSource1442
  | 18 => auxSource1443
  | 19 => auxSource1444
  | 20 => auxSource1445
  | 21 => auxSource1446
  | 22 => auxSource1447
  | 23 => auxSource1448
  | 24 => auxSource1449
  | 25 => auxSource1450
  | 26 => auxSource1451
  | 27 => auxSource1452
  | 28 => auxSource1453
  | 29 => auxSource1454
  | 30 => auxSource1455
  | 31 => auxSource1456
  | _ => .old 0

compact_certificate theorem actual_source_117 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock117 i.val))=source (i.val+3744) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_117 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock117 i.val))=tail (i.val+3744) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_117
#print axioms actual_tail_117

compact_certificate def actualBlock118 : ℕ → SourceRow
  | 0 => auxSource1457
  | 1 => auxSource1458
  | 2 => auxSource1459
  | 3 => auxSource1460
  | 4 => auxSource1461
  | 5 => auxSource1462
  | 6 => auxSource1463
  | 7 => auxSource1464
  | 8 => auxSource1465
  | 9 => auxSource1466
  | 10 => auxSource1467
  | 11 => auxSource1468
  | 12 => auxSource1469
  | 13 => auxSource1470
  | 14 => auxSource1471
  | 15 => auxSource1472
  | 16 => auxSource1473
  | 17 => auxSource1474
  | 18 => auxSource1475
  | 19 => auxSource1476
  | 20 => auxSource1477
  | 21 => auxSource1478
  | 22 => auxSource1479
  | 23 => auxSource1480
  | 24 => auxSource1481
  | 25 => auxSource1482
  | 26 => auxSource1483
  | 27 => auxSource1484
  | 28 => auxSource1485
  | 29 => auxSource1486
  | 30 => auxSource1487
  | 31 => auxSource1488
  | _ => .old 0

compact_certificate theorem actual_source_118 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock118 i.val))=source (i.val+3776) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_118 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock118 i.val))=tail (i.val+3776) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_118
#print axioms actual_tail_118

compact_certificate def actualBlock119 : ℕ → SourceRow
  | 0 => auxSource1489
  | 1 => auxSource1490
  | 2 => auxSource1491
  | 3 => auxSource1492
  | 4 => auxSource1493
  | 5 => auxSource1494
  | 6 => auxSource1495
  | 7 => auxSource1496
  | 8 => auxSource1497
  | 9 => auxSource1498
  | 10 => auxSource1499
  | 11 => auxSource1500
  | 12 => auxSource1501
  | 13 => auxSource1502
  | 14 => auxSource1503
  | 15 => auxSource1504
  | 16 => auxSource1505
  | 17 => auxSource1506
  | 18 => auxSource1507
  | 19 => auxSource1508
  | 20 => auxSource1509
  | 21 => auxSource1510
  | 22 => auxSource1511
  | 23 => auxSource1512
  | 24 => auxSource1513
  | 25 => auxSource1514
  | 26 => auxSource1515
  | 27 => auxSource1516
  | 28 => auxSource1517
  | 29 => auxSource1518
  | 30 => auxSource1519
  | 31 => auxSource1520
  | _ => .old 0

compact_certificate theorem actual_source_119 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock119 i.val))=source (i.val+3808) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_119 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock119 i.val))=tail (i.val+3808) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_119
#print axioms actual_tail_119

compact_certificate def actualBlock120 : ℕ → SourceRow
  | 0 => auxSource1521
  | 1 => auxSource1522
  | 2 => auxSource1523
  | 3 => auxSource1524
  | 4 => auxSource1525
  | 5 => auxSource1526
  | 6 => auxSource1527
  | 7 => auxSource1528
  | 8 => auxSource1529
  | 9 => auxSource1530
  | 10 => auxSource1531
  | 11 => auxSource1532
  | 12 => auxSource1533
  | 13 => auxSource1534
  | 14 => auxSource1535
  | 15 => auxSource1536
  | 16 => auxSource1537
  | 17 => auxSource1538
  | 18 => auxSource1539
  | 19 => auxSource1540
  | 20 => auxSource1541
  | 21 => auxSource1542
  | 22 => auxSource1543
  | 23 => auxSource1544
  | 24 => auxSource1545
  | 25 => auxSource1546
  | 26 => auxSource1547
  | 27 => auxSource1548
  | 28 => auxSource1549
  | 29 => auxSource1550
  | 30 => auxSource1551
  | 31 => auxSource1552
  | _ => .old 0

compact_certificate theorem actual_source_120 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock120 i.val))=source (i.val+3840) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_120 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock120 i.val))=tail (i.val+3840) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_120
#print axioms actual_tail_120

compact_certificate def actualBlock121 : ℕ → SourceRow
  | 0 => auxSource1553
  | 1 => auxSource1554
  | 2 => auxSource1555
  | 3 => auxSource1556
  | 4 => auxSource1557
  | 5 => auxSource1558
  | 6 => auxSource1559
  | 7 => auxSource1560
  | 8 => auxSource1561
  | 9 => auxSource1562
  | 10 => auxSource1563
  | 11 => auxSource1564
  | 12 => auxSource1565
  | 13 => auxSource1566
  | 14 => auxSource1567
  | 15 => auxSource1568
  | 16 => auxSource1569
  | 17 => auxSource1570
  | 18 => auxSource1571
  | 19 => auxSource1572
  | 20 => auxSource1573
  | 21 => auxSource1574
  | 22 => auxSource1575
  | 23 => auxSource1576
  | 24 => auxSource1577
  | 25 => auxSource1578
  | 26 => auxSource1579
  | 27 => auxSource1580
  | 28 => auxSource1581
  | 29 => auxSource1582
  | 30 => auxSource1583
  | 31 => auxSource1584
  | _ => .old 0

compact_certificate theorem actual_source_121 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock121 i.val))=source (i.val+3872) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_121 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock121 i.val))=tail (i.val+3872) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_121
#print axioms actual_tail_121

compact_certificate def actualBlock122 : ℕ → SourceRow
  | 0 => auxSource1585
  | 1 => auxSource1586
  | 2 => auxSource1587
  | 3 => auxSource1588
  | 4 => auxSource1589
  | 5 => auxSource1590
  | 6 => auxSource1591
  | 7 => auxSource1592
  | 8 => auxSource1593
  | 9 => auxSource1594
  | 10 => auxSource1595
  | 11 => auxSource1596
  | 12 => auxSource1597
  | 13 => auxSource1598
  | 14 => auxSource1599
  | 15 => auxSource1600
  | 16 => auxSource1601
  | 17 => auxSource1602
  | 18 => auxSource1603
  | 19 => auxSource1604
  | 20 => auxSource1605
  | 21 => auxSource1606
  | 22 => auxSource1607
  | 23 => auxSource1608
  | 24 => auxSource1609
  | 25 => auxSource1610
  | 26 => auxSource1611
  | 27 => auxSource1612
  | 28 => auxSource1613
  | 29 => auxSource1614
  | 30 => auxSource1615
  | 31 => auxSource1616
  | _ => .old 0

compact_certificate theorem actual_source_122 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock122 i.val))=source (i.val+3904) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_122 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock122 i.val))=tail (i.val+3904) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_122
#print axioms actual_tail_122

compact_certificate def actualBlock123 : ℕ → SourceRow
  | 0 => auxSource1617
  | 1 => auxSource1618
  | 2 => auxSource1619
  | 3 => auxSource1620
  | 4 => auxSource1621
  | 5 => auxSource1622
  | 6 => auxSource1623
  | 7 => auxSource1624
  | 8 => auxSource1625
  | 9 => auxSource1626
  | 10 => auxSource1627
  | 11 => auxSource1628
  | 12 => auxSource1629
  | 13 => auxSource1630
  | 14 => auxSource1631
  | 15 => auxSource1632
  | 16 => auxSource1633
  | 17 => auxSource1634
  | 18 => auxSource1635
  | 19 => auxSource1636
  | 20 => auxSource1637
  | 21 => auxSource1638
  | 22 => auxSource1639
  | 23 => auxSource1640
  | 24 => auxSource1641
  | 25 => auxSource1642
  | 26 => auxSource1643
  | 27 => auxSource1644
  | 28 => auxSource1645
  | 29 => auxSource1646
  | 30 => auxSource1647
  | 31 => auxSource1648
  | _ => .old 0

compact_certificate theorem actual_source_123 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock123 i.val))=source (i.val+3936) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_123 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock123 i.val))=tail (i.val+3936) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_123
#print axioms actual_tail_123

compact_certificate def actualBlock124 : ℕ → SourceRow
  | 0 => auxSource1649
  | 1 => auxSource1650
  | 2 => auxSource1651
  | 3 => auxSource1652
  | 4 => auxSource1653
  | 5 => auxSource1654
  | 6 => auxSource1655
  | 7 => auxSource1656
  | 8 => auxSource1657
  | 9 => auxSource1658
  | 10 => auxSource1659
  | 11 => auxSource1660
  | 12 => auxSource1661
  | 13 => auxSource1662
  | 14 => auxSource1663
  | 15 => auxSource1664
  | 16 => auxSource1665
  | 17 => auxSource1666
  | 18 => auxSource1667
  | 19 => auxSource1668
  | 20 => auxSource1669
  | 21 => auxSource1670
  | 22 => auxSource1671
  | 23 => auxSource1672
  | 24 => auxSource1673
  | 25 => auxSource1674
  | 26 => auxSource1675
  | 27 => auxSource1676
  | 28 => auxSource1677
  | 29 => auxSource1678
  | 30 => auxSource1679
  | 31 => auxSource1680
  | _ => .old 0

compact_certificate theorem actual_source_124 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock124 i.val))=source (i.val+3968) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_124 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock124 i.val))=tail (i.val+3968) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_124
#print axioms actual_tail_124

compact_certificate def actualBlock125 : ℕ → SourceRow
  | 0 => auxSource1681
  | 1 => auxSource1682
  | 2 => auxSource1683
  | 3 => auxSource1684
  | 4 => auxSource1685
  | 5 => auxSource1686
  | 6 => auxSource1687
  | 7 => auxSource1688
  | 8 => auxSource1689
  | 9 => auxSource1690
  | 10 => auxSource1691
  | 11 => auxSource1692
  | 12 => auxSource1693
  | 13 => auxSource1694
  | 14 => auxSource1695
  | 15 => auxSource1696
  | 16 => auxSource1697
  | 17 => auxSource1698
  | 18 => auxSource1699
  | 19 => auxSource1700
  | 20 => auxSource1701
  | 21 => auxSource1702
  | 22 => auxSource1703
  | 23 => auxSource1704
  | 24 => auxSource1705
  | 25 => auxSource1706
  | 26 => auxSource1707
  | 27 => auxSource1708
  | 28 => auxSource1709
  | 29 => auxSource1710
  | 30 => auxSource1711
  | 31 => auxSource1712
  | _ => .old 0

compact_certificate theorem actual_source_125 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock125 i.val))=source (i.val+4000) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_125 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock125 i.val))=tail (i.val+4000) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_125
#print axioms actual_tail_125

compact_certificate def actualBlock126 : ℕ → SourceRow
  | 0 => auxSource1713
  | 1 => auxSource1714
  | 2 => auxSource1715
  | 3 => auxSource1716
  | 4 => auxSource1717
  | 5 => auxSource1718
  | 6 => auxSource1719
  | 7 => auxSource1720
  | 8 => auxSource1721
  | 9 => auxSource1722
  | 10 => auxSource1723
  | 11 => auxSource1724
  | 12 => auxSource1725
  | 13 => auxSource1726
  | 14 => auxSource1727
  | 15 => auxSource1728
  | 16 => auxSource1729
  | 17 => auxSource1730
  | 18 => auxSource1731
  | 19 => auxSource1732
  | 20 => auxSource1733
  | 21 => auxSource1734
  | 22 => auxSource1735
  | 23 => auxSource1736
  | 24 => auxSource1737
  | 25 => auxSource1738
  | 26 => auxSource1739
  | 27 => auxSource1740
  | 28 => auxSource1741
  | 29 => auxSource1742
  | 30 => auxSource1743
  | 31 => auxSource1744
  | _ => .old 0

compact_certificate theorem actual_source_126 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock126 i.val))=source (i.val+4032) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_126 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock126 i.val))=tail (i.val+4032) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_126
#print axioms actual_tail_126

compact_certificate def actualBlock127 : ℕ → SourceRow
  | 0 => auxSource1745
  | 1 => auxSource1746
  | 2 => auxSource1747
  | 3 => auxSource1748
  | 4 => auxSource1749
  | 5 => auxSource1750
  | 6 => auxSource1751
  | 7 => auxSource1752
  | 8 => auxSource1753
  | 9 => auxSource1754
  | 10 => auxSource1755
  | 11 => auxSource1756
  | 12 => auxSource1757
  | 13 => auxSource1758
  | 14 => auxSource1759
  | 15 => auxSource1760
  | 16 => auxSource1761
  | 17 => auxSource1762
  | 18 => auxSource1763
  | 19 => auxSource1764
  | 20 => auxSource1765
  | 21 => auxSource1766
  | 22 => auxSource1767
  | 23 => auxSource1768
  | 24 => auxSource1769
  | 25 => auxSource1770
  | 26 => auxSource1771
  | 27 => auxSource1772
  | 28 => auxSource1773
  | 29 => auxSource1774
  | 30 => auxSource1775
  | 31 => auxSource1776
  | _ => .old 0

compact_certificate theorem actual_source_127 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock127 i.val))=source (i.val+4064) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_127 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock127 i.val))=tail (i.val+4064) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_127
#print axioms actual_tail_127

compact_certificate def actualBlock128 : ℕ → SourceRow
  | 0 => auxSource1777
  | 1 => auxSource1778
  | 2 => auxSource1779
  | 3 => auxSource1780
  | 4 => auxSource1781
  | 5 => auxSource1782
  | 6 => auxSource1783
  | 7 => auxSource1784
  | 8 => auxSource1785
  | 9 => auxSource1786
  | 10 => auxSource1787
  | 11 => auxSource1788
  | 12 => auxSource1789
  | 13 => auxSource1790
  | 14 => auxSource1791
  | 15 => auxSource1792
  | 16 => auxSource1793
  | 17 => auxSource1794
  | 18 => auxSource1795
  | 19 => auxSource1796
  | 20 => auxSource1797
  | 21 => auxSource1798
  | 22 => auxSource1799
  | 23 => auxSource1800
  | 24 => auxSource1801
  | 25 => auxSource1802
  | 26 => auxSource1803
  | 27 => auxSource1804
  | 28 => auxSource1805
  | 29 => auxSource1806
  | 30 => auxSource1807
  | 31 => auxSource1808
  | _ => .old 0

compact_certificate theorem actual_source_128 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock128 i.val))=source (i.val+4096) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_128 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock128 i.val))=tail (i.val+4096) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_128
#print axioms actual_tail_128

compact_certificate def actualBlock129 : ℕ → SourceRow
  | 0 => auxSource1809
  | 1 => auxSource1810
  | 2 => auxSource1811
  | 3 => auxSource1812
  | 4 => auxSource1813
  | 5 => auxSource1814
  | 6 => auxSource1815
  | 7 => auxSource1816
  | 8 => auxSource1817
  | 9 => auxSource1818
  | 10 => auxSource1819
  | 11 => auxSource1820
  | 12 => auxSource1821
  | 13 => auxSource1822
  | 14 => auxSource1823
  | 15 => auxSource1824
  | 16 => auxSource1825
  | 17 => auxSource1826
  | 18 => auxSource1827
  | 19 => auxSource1828
  | 20 => auxSource1829
  | 21 => auxSource1830
  | 22 => auxSource1831
  | 23 => auxSource1832
  | 24 => auxSource1833
  | 25 => auxSource1834
  | 26 => auxSource1835
  | 27 => auxSource1836
  | 28 => auxSource1837
  | 29 => auxSource1838
  | 30 => auxSource1839
  | 31 => auxSource1840
  | _ => .old 0

compact_certificate theorem actual_source_129 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock129 i.val))=source (i.val+4128) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_129 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock129 i.val))=tail (i.val+4128) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_129
#print axioms actual_tail_129

compact_certificate def actualBlock130 : ℕ → SourceRow
  | 0 => auxSource1841
  | 1 => auxSource1842
  | 2 => auxSource1843
  | 3 => auxSource1844
  | 4 => auxSource1845
  | 5 => auxSource1846
  | 6 => auxSource1847
  | 7 => auxSource1848
  | 8 => auxSource1849
  | 9 => auxSource1850
  | 10 => auxSource1851
  | 11 => auxSource1852
  | 12 => auxSource1853
  | 13 => auxSource1854
  | 14 => auxSource1855
  | 15 => auxSource1856
  | 16 => auxSource1857
  | 17 => auxSource1858
  | 18 => auxSource1859
  | 19 => auxSource1860
  | 20 => auxSource1861
  | 21 => auxSource1862
  | 22 => auxSource1863
  | 23 => auxSource1864
  | 24 => auxSource1865
  | 25 => auxSource1866
  | 26 => auxSource1867
  | 27 => auxSource1868
  | 28 => auxSource1869
  | 29 => auxSource1870
  | 30 => auxSource1871
  | 31 => auxSource1872
  | _ => .old 0

compact_certificate theorem actual_source_130 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock130 i.val))=source (i.val+4160) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_130 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock130 i.val))=tail (i.val+4160) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_130
#print axioms actual_tail_130

compact_certificate def actualBlock131 : ℕ → SourceRow
  | 0 => auxSource1873
  | 1 => auxSource1874
  | 2 => auxSource1875
  | 3 => auxSource1876
  | 4 => auxSource1877
  | 5 => auxSource1878
  | 6 => auxSource1879
  | 7 => auxSource1880
  | 8 => auxSource1881
  | 9 => auxSource1882
  | 10 => auxSource1883
  | 11 => auxSource1884
  | 12 => auxSource1885
  | 13 => auxSource1886
  | 14 => auxSource1887
  | 15 => auxSource1888
  | 16 => auxSource1889
  | 17 => auxSource1890
  | 18 => auxSource1891
  | 19 => auxSource1892
  | 20 => auxSource1893
  | 21 => auxSource1894
  | 22 => auxSource1895
  | 23 => auxSource1896
  | 24 => auxSource1897
  | 25 => auxSource1898
  | 26 => auxSource1899
  | 27 => auxSource1900
  | 28 => auxSource1901
  | 29 => auxSource1902
  | 30 => auxSource1903
  | 31 => auxSource1904
  | _ => .old 0

compact_certificate theorem actual_source_131 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock131 i.val))=source (i.val+4192) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_131 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock131 i.val))=tail (i.val+4192) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_131
#print axioms actual_tail_131

compact_certificate def actualBlock132 : ℕ → SourceRow
  | 0 => auxSource1905
  | 1 => auxSource1906
  | 2 => auxSource1907
  | 3 => auxSource1908
  | 4 => auxSource1909
  | 5 => auxSource1910
  | 6 => auxSource1911
  | 7 => auxSource1912
  | 8 => auxSource1913
  | 9 => auxSource1914
  | 10 => auxSource1915
  | 11 => auxSource1916
  | 12 => auxSource1917
  | 13 => auxSource1918
  | 14 => auxSource1919
  | 15 => auxSource1920
  | 16 => auxSource1921
  | 17 => auxSource1922
  | 18 => auxSource1923
  | 19 => auxSource1924
  | 20 => auxSource1925
  | 21 => auxSource1926
  | 22 => auxSource1927
  | 23 => auxSource1928
  | 24 => auxSource1929
  | 25 => auxSource1930
  | 26 => auxSource1931
  | 27 => auxSource1932
  | 28 => auxSource1933
  | 29 => auxSource1934
  | 30 => auxSource1935
  | 31 => auxSource1936
  | _ => .old 0

compact_certificate theorem actual_source_132 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock132 i.val))=source (i.val+4224) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_132 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock132 i.val))=tail (i.val+4224) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_132
#print axioms actual_tail_132

compact_certificate def actualBlock133 : ℕ → SourceRow
  | 0 => auxSource1937
  | 1 => auxSource1938
  | 2 => auxSource1939
  | 3 => auxSource1940
  | 4 => auxSource1941
  | 5 => auxSource1942
  | 6 => auxSource1943
  | 7 => auxSource1944
  | 8 => auxSource1945
  | 9 => auxSource1946
  | 10 => auxSource1947
  | 11 => auxSource1948
  | 12 => auxSource1949
  | 13 => auxSource1950
  | 14 => auxSource1951
  | 15 => auxSource1952
  | 16 => auxSource1953
  | 17 => auxSource1954
  | 18 => auxSource1955
  | 19 => auxSource1956
  | 20 => auxSource1957
  | 21 => auxSource1958
  | 22 => auxSource1959
  | 23 => auxSource1960
  | 24 => auxSource1961
  | 25 => auxSource1962
  | 26 => auxSource1963
  | 27 => auxSource1964
  | 28 => auxSource1965
  | 29 => auxSource1966
  | 30 => auxSource1967
  | 31 => auxSource1968
  | _ => .old 0

compact_certificate theorem actual_source_133 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock133 i.val))=source (i.val+4256) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_133 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock133 i.val))=tail (i.val+4256) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_133
#print axioms actual_tail_133

compact_certificate def actualBlock134 : ℕ → SourceRow
  | 0 => auxSource1969
  | 1 => auxSource1970
  | 2 => auxSource1971
  | 3 => auxSource1972
  | 4 => auxSource1973
  | 5 => auxSource1974
  | 6 => auxSource1975
  | 7 => auxSource1976
  | 8 => auxSource1977
  | 9 => auxSource1978
  | 10 => auxSource1979
  | 11 => auxSource1980
  | 12 => auxSource1981
  | 13 => auxSource1982
  | 14 => auxSource1983
  | 15 => auxSource1984
  | 16 => auxSource1985
  | 17 => auxSource1986
  | 18 => auxSource1987
  | 19 => auxSource1988
  | 20 => auxSource1989
  | 21 => auxSource1990
  | 22 => auxSource1991
  | 23 => auxSource1992
  | 24 => auxSource1993
  | 25 => auxSource1994
  | 26 => auxSource1995
  | 27 => auxSource1996
  | 28 => auxSource1997
  | 29 => auxSource1998
  | 30 => auxSource1999
  | 31 => auxSource2000
  | _ => .old 0

compact_certificate theorem actual_source_134 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock134 i.val))=source (i.val+4288) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_134 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock134 i.val))=tail (i.val+4288) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_134
#print axioms actual_tail_134

compact_certificate def actualBlock135 : ℕ → SourceRow
  | 0 => auxSource2001
  | 1 => auxSource2002
  | 2 => auxSource2003
  | 3 => auxSource2004
  | 4 => auxSource2005
  | 5 => auxSource2006
  | 6 => auxSource2007
  | 7 => auxSource2008
  | 8 => auxSource2009
  | 9 => auxSource2010
  | 10 => auxSource2011
  | 11 => auxSource2012
  | 12 => auxSource2013
  | 13 => auxSource2014
  | 14 => auxSource2015
  | 15 => auxSource2016
  | 16 => auxSource2017
  | 17 => auxSource2018
  | 18 => auxSource2019
  | 19 => auxSource2020
  | 20 => auxSource2021
  | 21 => auxSource2022
  | 22 => auxSource2023
  | 23 => auxSource2024
  | 24 => auxSource2025
  | 25 => auxSource2026
  | 26 => auxSource2027
  | 27 => auxSource2028
  | 28 => auxSource2029
  | 29 => auxSource2030
  | 30 => auxSource2031
  | 31 => auxSource2032
  | _ => .old 0

compact_certificate theorem actual_source_135 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock135 i.val))=source (i.val+4320) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_135 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock135 i.val))=tail (i.val+4320) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_135
#print axioms actual_tail_135

compact_certificate def actualBlock136 : ℕ → SourceRow
  | 0 => auxSource2033
  | 1 => auxSource2034
  | 2 => auxSource2035
  | 3 => auxSource2036
  | 4 => auxSource2037
  | 5 => auxSource2038
  | 6 => auxSource2039
  | 7 => auxSource2040
  | 8 => auxSource2041
  | 9 => auxSource2042
  | 10 => auxSource2043
  | 11 => auxSource2044
  | 12 => auxSource2045
  | 13 => auxSource2046
  | 14 => auxSource2047
  | 15 => auxSource2048
  | 16 => auxSource2049
  | 17 => auxSource2050
  | 18 => auxSource2051
  | 19 => auxSource2052
  | 20 => auxSource2053
  | 21 => auxSource2054
  | 22 => auxSource2055
  | 23 => auxSource2056
  | 24 => auxSource2057
  | 25 => auxSource2058
  | 26 => auxSource2059
  | 27 => auxSource2060
  | 28 => auxSource2061
  | 29 => auxSource2062
  | 30 => auxSource2063
  | 31 => auxSource2064
  | _ => .old 0

compact_certificate theorem actual_source_136 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock136 i.val))=source (i.val+4352) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_136 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock136 i.val))=tail (i.val+4352) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_136
#print axioms actual_tail_136

compact_certificate def actualBlock137 : ℕ → SourceRow
  | 0 => auxSource2065
  | 1 => auxSource2066
  | 2 => auxSource2067
  | 3 => auxSource2068
  | 4 => auxSource2069
  | 5 => auxSource2070
  | 6 => auxSource2071
  | 7 => auxSource2072
  | 8 => auxSource2073
  | 9 => auxSource2074
  | 10 => auxSource2075
  | 11 => auxSource2076
  | 12 => auxSource2077
  | 13 => auxSource2078
  | 14 => auxSource2079
  | 15 => auxSource2080
  | 16 => auxSource2081
  | 17 => auxSource2082
  | 18 => auxSource2083
  | 19 => auxSource2084
  | 20 => auxSource2085
  | 21 => auxSource2086
  | 22 => auxSource2087
  | 23 => auxSource2088
  | 24 => auxSource2089
  | 25 => auxSource2090
  | 26 => auxSource2091
  | 27 => auxSource2092
  | 28 => auxSource2093
  | 29 => auxSource2094
  | 30 => auxSource2095
  | 31 => auxSource2096
  | _ => .old 0

compact_certificate theorem actual_source_137 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock137 i.val))=source (i.val+4384) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_137 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock137 i.val))=tail (i.val+4384) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_137
#print axioms actual_tail_137

compact_certificate def actualBlock138 : ℕ → SourceRow
  | 0 => auxSource2097
  | 1 => auxSource2098
  | 2 => auxSource2099
  | 3 => auxSource2100
  | 4 => auxSource2101
  | 5 => auxSource2102
  | 6 => auxSource2103
  | 7 => auxSource2104
  | 8 => auxSource2105
  | 9 => auxSource2106
  | 10 => auxSource2107
  | 11 => auxSource2108
  | 12 => auxSource2109
  | 13 => auxSource2110
  | 14 => auxSource2111
  | 15 => auxSource2112
  | 16 => auxSource2113
  | 17 => auxSource2114
  | 18 => auxSource2115
  | 19 => auxSource2116
  | 20 => auxSource2117
  | 21 => auxSource2118
  | 22 => auxSource2119
  | 23 => auxSource2120
  | 24 => auxSource2121
  | 25 => auxSource2122
  | 26 => auxSource2123
  | 27 => auxSource2124
  | 28 => auxSource2125
  | 29 => auxSource2126
  | 30 => auxSource2127
  | 31 => auxSource2128
  | _ => .old 0

compact_certificate theorem actual_source_138 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock138 i.val))=source (i.val+4416) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_138 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock138 i.val))=tail (i.val+4416) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_138
#print axioms actual_tail_138

compact_certificate def actualBlock139 : ℕ → SourceRow
  | 0 => auxSource2129
  | 1 => auxSource2130
  | 2 => auxSource4450
  | 3 => auxSource4451
  | 4 => auxSource4452
  | 5 => auxSource4453
  | 6 => auxSource4454
  | 7 => auxSource4455
  | 8 => auxSource4456
  | 9 => auxSource4457
  | 10 => auxSource4458
  | 11 => auxSource4459
  | 12 => auxSource4460
  | 13 => auxSource4461
  | 14 => auxSource4462
  | 15 => auxSource4463
  | 16 => auxSource4464
  | 17 => auxSource4465
  | 18 => auxSource4466
  | 19 => auxSource4467
  | 20 => auxSource4468
  | 21 => auxSource4469
  | 22 => auxSource4470
  | 23 => auxSource4471
  | 24 => auxSource4472
  | 25 => auxSource4473
  | 26 => auxSource4474
  | 27 => auxSource4475
  | 28 => auxSource4476
  | 29 => auxSource4477
  | 30 => auxSource4478
  | 31 => auxSource4479
  | _ => .old 0

compact_certificate theorem actual_source_139 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock139 i.val))=source (i.val+4448) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_139 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock139 i.val))=tail (i.val+4448) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_139
#print axioms actual_tail_139

compact_certificate def actualBlock140 : ℕ → SourceRow
  | 0 => auxSource4480
  | 1 => auxSource4481
  | 2 => auxSource4482
  | 3 => auxSource4483
  | 4 => auxSource4484
  | 5 => auxSource4485
  | 6 => auxSource4486
  | 7 => auxSource4487
  | 8 => auxSource4488
  | 9 => auxSource4489
  | 10 => auxSource4490
  | 11 => auxSource4491
  | 12 => auxSource4492
  | 13 => auxSource4493
  | 14 => auxSource4494
  | 15 => auxSource4495
  | 16 => auxSource4496
  | 17 => auxSource4497
  | 18 => auxSource4498
  | 19 => auxSource4499
  | 20 => auxSource4500
  | 21 => auxSource4501
  | 22 => auxSource4502
  | 23 => auxSource4503
  | 24 => auxSource4504
  | 25 => auxSource4505
  | 26 => auxSource4506
  | 27 => auxSource4507
  | 28 => auxSource4508
  | 29 => auxSource4509
  | 30 => auxSource4510
  | 31 => auxSource4511
  | _ => .old 0

compact_certificate theorem actual_source_140 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock140 i.val))=source (i.val+4480) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_140 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock140 i.val))=tail (i.val+4480) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_140
#print axioms actual_tail_140

compact_certificate def actualBlock141 : ℕ → SourceRow
  | 0 => auxSource4512
  | 1 => auxSource4513
  | 2 => auxSource4514
  | 3 => auxSource4515
  | 4 => auxSource4516
  | 5 => auxSource4517
  | 6 => auxSource4518
  | 7 => auxSource4519
  | 8 => auxSource4520
  | 9 => auxSource4521
  | 10 => auxSource4522
  | 11 => auxSource4523
  | 12 => auxSource4524
  | 13 => auxSource4525
  | 14 => auxSource4526
  | 15 => auxSource4527
  | 16 => auxSource4528
  | 17 => auxSource4529
  | 18 => auxSource4530
  | 19 => auxSource4531
  | 20 => auxSource4532
  | 21 => auxSource4533
  | 22 => auxSource4534
  | 23 => auxSource4535
  | 24 => auxSource4536
  | 25 => auxSource4537
  | 26 => auxSource4538
  | 27 => auxSource4539
  | 28 => auxSource4540
  | 29 => auxSource4541
  | 30 => auxSource4542
  | 31 => auxSource4543
  | _ => .old 0

compact_certificate theorem actual_source_141 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock141 i.val))=source (i.val+4512) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_141 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock141 i.val))=tail (i.val+4512) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_141
#print axioms actual_tail_141

compact_certificate def actualBlock142 : ℕ → SourceRow
  | 0 => auxSource4544
  | 1 => auxSource4545
  | 2 => auxSource4546
  | 3 => auxSource4547
  | 4 => auxSource4548
  | 5 => auxSource4549
  | 6 => auxSource4550
  | 7 => auxSource4551
  | 8 => auxSource4552
  | 9 => auxSource4553
  | 10 => auxSource4554
  | 11 => auxSource4555
  | 12 => auxSource4556
  | 13 => auxSource4557
  | 14 => auxSource4558
  | 15 => auxSource4559
  | 16 => auxSource4560
  | 17 => auxSource4561
  | 18 => auxSource4562
  | 19 => auxSource4563
  | 20 => auxSource4564
  | 21 => auxSource4565
  | 22 => auxSource4566
  | 23 => auxSource4567
  | 24 => auxSource4568
  | 25 => auxSource4569
  | 26 => auxSource4570
  | 27 => auxSource4571
  | 28 => auxSource4572
  | 29 => auxSource4573
  | 30 => auxSource4574
  | 31 => auxSource4575
  | _ => .old 0

compact_certificate theorem actual_source_142 : ∀ i : Fin 32,
    normalizedPoly (rawSourcePoly 1 (actualBlock142 i.val))=source (i.val+4544) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_142 : ∀ i : Fin 32,
    normalizedPoly (rawTailPoly (actualBlock142 i.val))=tail (i.val+4544) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_142
#print axioms actual_tail_142

compact_certificate def actualBlock143 : ℕ → SourceRow
  | 0 => auxSource4576
  | 1 => auxSource4577
  | 2 => auxSource4578
  | 3 => auxSource4579
  | 4 => auxSource4580
  | 5 => auxSource4581
  | 6 => auxSource4582
  | 7 => auxSource4583
  | 8 => auxSource4584
  | 9 => auxSource4585
  | 10 => auxSource4586
  | 11 => auxSource4587
  | 12 => auxSource4588
  | 13 => auxSource4589
  | 14 => auxSource4590
  | 15 => auxSource4591
  | 16 => auxSource4592
  | 17 => auxSource4593
  | 18 => auxSource4594
  | 19 => auxSource4595
  | 20 => auxSource4596
  | 21 => auxSource4597
  | 22 => auxSource4598
  | 23 => auxSource4599
  | _ => .old 0

compact_certificate theorem actual_source_143 : ∀ i : Fin 24,
    normalizedPoly (rawSourcePoly 1 (actualBlock143 i.val))=source (i.val+4576) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
compact_certificate theorem actual_tail_143 : ∀ i : Fin 24,
    normalizedPoly (rawTailPoly (actualBlock143 i.val))=tail (i.val+4576) := by
  simp only [normalizedPoly, ← QuantitativeArithmeticSevenLaurentRows.substituteCompute_eq]
  decide +kernel
#print axioms actual_source_143
#print axioms actual_tail_143

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

