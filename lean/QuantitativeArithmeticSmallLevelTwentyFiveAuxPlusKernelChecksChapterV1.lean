module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusOperationStages2V1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusOperationStages0V1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusOperationStages1V1
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusKernelDataChapterV1

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

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentEliminationCheck30SingleFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows
certificate_batch {
compact_certificate theorem operations_checked_30_single0 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 960)=normal 960 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single0 : ∀ t ∈ operations 960,
    t.2.1<4600+960 := by decide +kernel
#print axioms operations_checked_30_single0
#print axioms operations_prior_30_single0

compact_certificate theorem operations_checked_30_single1 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 961)=normal 961 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single1 : ∀ t ∈ operations 961,
    t.2.1<4600+961 := by decide +kernel
#print axioms operations_checked_30_single1
#print axioms operations_prior_30_single1

compact_certificate theorem operations_checked_30_single2 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 962)=normal 962 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single2 : ∀ t ∈ operations 962,
    t.2.1<4600+962 := by decide +kernel
#print axioms operations_checked_30_single2
#print axioms operations_prior_30_single2

compact_certificate theorem operations_checked_30_single3 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 963)=normal 963 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single3 : ∀ t ∈ operations 963,
    t.2.1<4600+963 := by decide +kernel
#print axioms operations_checked_30_single3
#print axioms operations_prior_30_single3

compact_certificate theorem operations_checked_30_single4 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 964)=normal 964 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single4 : ∀ t ∈ operations 964,
    t.2.1<4600+964 := by decide +kernel
#print axioms operations_checked_30_single4
#print axioms operations_prior_30_single4

compact_certificate theorem operations_checked_30_single5 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 965)=normal 965 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single5 : ∀ t ∈ operations 965,
    t.2.1<4600+965 := by decide +kernel
#print axioms operations_checked_30_single5
#print axioms operations_prior_30_single5

compact_certificate theorem operations_checked_30_single6 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 966)=normal 966 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single6 : ∀ t ∈ operations 966,
    t.2.1<4600+966 := by decide +kernel
#print axioms operations_checked_30_single6
#print axioms operations_prior_30_single6

compact_certificate theorem operations_checked_30_single7 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 967)=normal 967 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single7 : ∀ t ∈ operations 967,
    t.2.1<4600+967 := by decide +kernel
#print axioms operations_checked_30_single7
#print axioms operations_prior_30_single7

compact_certificate theorem operations_checked_30_single8 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 968)=normal 968 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single8 : ∀ t ∈ operations 968,
    t.2.1<4600+968 := by decide +kernel
#print axioms operations_checked_30_single8
#print axioms operations_prior_30_single8

compact_certificate theorem operations_checked_30_single9 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 969)=normal 969 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single9 : ∀ t ∈ operations 969,
    t.2.1<4600+969 := by decide +kernel
#print axioms operations_checked_30_single9
#print axioms operations_prior_30_single9

compact_certificate theorem operations_checked_30_single10 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 970)=normal 970 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single10 : ∀ t ∈ operations 970,
    t.2.1<4600+970 := by decide +kernel
#print axioms operations_checked_30_single10
#print axioms operations_prior_30_single10

compact_certificate theorem operations_checked_30_single11 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 971)=normal 971 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single11 : ∀ t ∈ operations 971,
    t.2.1<4600+971 := by decide +kernel
#print axioms operations_checked_30_single11
#print axioms operations_prior_30_single11

compact_certificate theorem operations_checked_30_single12 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 972)=normal 972 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single12 : ∀ t ∈ operations 972,
    t.2.1<4600+972 := by decide +kernel
#print axioms operations_checked_30_single12
#print axioms operations_prior_30_single12

compact_certificate theorem operations_checked_30_single13 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 973)=normal 973 := by
  exact boundedOperation973Done
compact_certificate theorem operations_prior_30_single13 : ∀ t ∈ operations 973,
    t.2.1<4600+973 := by decide +kernel
#print axioms operations_checked_30_single13
#print axioms operations_prior_30_single13

compact_certificate theorem operations_checked_30_single14 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 974)=normal 974 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single14 : ∀ t ∈ operations 974,
    t.2.1<4600+974 := by decide +kernel
#print axioms operations_checked_30_single14
#print axioms operations_prior_30_single14

compact_certificate theorem operations_checked_30_single15 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 975)=normal 975 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single15 : ∀ t ∈ operations 975,
    t.2.1<4600+975 := by decide +kernel
#print axioms operations_checked_30_single15
#print axioms operations_prior_30_single15

compact_certificate theorem operations_checked_30_single16 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 976)=normal 976 := by
  exact boundedOperation976Done
compact_certificate theorem operations_prior_30_single16 : ∀ t ∈ operations 976,
    t.2.1<4600+976 := by decide +kernel
#print axioms operations_checked_30_single16
#print axioms operations_prior_30_single16

compact_certificate theorem operations_checked_30_single17 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 977)=normal 977 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single17 : ∀ t ∈ operations 977,
    t.2.1<4600+977 := by decide +kernel
#print axioms operations_checked_30_single17
#print axioms operations_prior_30_single17

compact_certificate theorem operations_checked_30_single18 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 978)=normal 978 := by
  exact boundedOperation978Done
compact_certificate theorem operations_prior_30_single18 : ∀ t ∈ operations 978,
    t.2.1<4600+978 := by decide +kernel
#print axioms operations_checked_30_single18
#print axioms operations_prior_30_single18

compact_certificate theorem operations_checked_30_single19 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 979)=normal 979 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single19 : ∀ t ∈ operations 979,
    t.2.1<4600+979 := by decide +kernel
#print axioms operations_checked_30_single19
#print axioms operations_prior_30_single19

compact_certificate theorem operations_checked_30_single20 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 980)=normal 980 := by
  simp only [← substituteCompute_eq]
  decide +kernel
compact_certificate theorem operations_prior_30_single20 : ∀ t ∈ operations 980,
    t.2.1<4600+980 := by decide +kernel
#print axioms operations_checked_30_single20
#print axioms operations_prior_30_single20

compact_certificate theorem operations_checked_30_single21 :
    substitute (fun j => if j<4600 then source j else normal (j-4600))
      (operations 981)=normal 981 := by
  exact boundedOperation981Done
compact_certificate theorem operations_prior_30_single21 : ∀ t ∈ operations 981,
    t.2.1<4600+981 := by decide +kernel
#print axioms operations_checked_30_single21
#print axioms operations_prior_30_single21
}

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentEliminationCheckFamilyV4 -/
section
-- Editor-info-based tactic linting is unavailable inside compact certificates.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Explicit certificate statements sharing their proof procedures. -/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

certificate_batch {
compact_certificate theorem operations_checked_0 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+0))=normal (i.val+0) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_0

compact_certificate theorem operations_checked_1 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+32))=normal (i.val+32) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_1


compact_certificate theorem operations_checked_2 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+64))=normal (i.val+64) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_2

compact_certificate theorem operations_checked_3 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+96))=normal (i.val+96) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_3


compact_certificate theorem operations_checked_4 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+128))=normal (i.val+128) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_4

compact_certificate theorem operations_checked_5 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+160))=normal (i.val+160) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_5


compact_certificate theorem operations_checked_6 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+192))=normal (i.val+192) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_6

compact_certificate theorem operations_checked_7 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+224))=normal (i.val+224) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_7


compact_certificate theorem operations_checked_8 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+256))=normal (i.val+256) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_8

compact_certificate theorem operations_checked_9 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+288))=normal (i.val+288) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_9


compact_certificate theorem operations_checked_10 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+320))=normal (i.val+320) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_10

compact_certificate theorem operations_checked_11 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+352))=normal (i.val+352) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_11


compact_certificate theorem operations_checked_12 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+384))=normal (i.val+384) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_12

compact_certificate theorem operations_checked_13 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+416))=normal (i.val+416) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_13


compact_certificate theorem operations_checked_14 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+448))=normal (i.val+448) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_14

compact_certificate theorem operations_checked_15 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+480))=normal (i.val+480) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_15


compact_certificate theorem operations_checked_16 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+512))=normal (i.val+512) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_16

compact_certificate theorem operations_checked_17 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+544))=normal (i.val+544) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_17


compact_certificate theorem operations_checked_18 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+576))=normal (i.val+576) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_18

compact_certificate theorem operations_checked_19 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+608))=normal (i.val+608) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_19


compact_certificate theorem operations_checked_20 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+640))=normal (i.val+640) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_20

compact_certificate theorem operations_checked_21 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+672))=normal (i.val+672) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_21


compact_certificate theorem operations_checked_22 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+704))=normal (i.val+704) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_22

compact_certificate theorem operations_checked_23 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+736))=normal (i.val+736) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_23


compact_certificate theorem operations_checked_24 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+768))=normal (i.val+768) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_24

compact_certificate theorem operations_checked_25 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+800))=normal (i.val+800) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_25


compact_certificate theorem operations_checked_26 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+832))=normal (i.val+832) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_26

compact_certificate theorem operations_checked_27 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+864))=normal (i.val+864) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_27


compact_certificate theorem operations_checked_28 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+896))=normal (i.val+896) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · exact boundedOperation908Done
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_28

compact_certificate theorem operations_checked_29 : ∀ i : Fin 32, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+928))=normal (i.val+928) := by
  intro i
  fin_cases i
  · simp only [← substituteCompute_eq]
    decide +kernel
  · exact boundedOperation929Done
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · exact boundedOperation953Done
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
  · simp only [← substituteCompute_eq]
    decide +kernel
#print axioms operations_checked_29

compact_facts [
  (operations_prior_0 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+0), t.2.1<4600+i.val+0),
  (operations_prior_1 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+32), t.2.1<4600+i.val+32)
] by
  decide +kernel


compact_facts [
  (operations_prior_2 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+64), t.2.1<4600+i.val+64),
  (operations_prior_3 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+96), t.2.1<4600+i.val+96)
] by
  decide +kernel


compact_facts [
  (operations_prior_4 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+128), t.2.1<4600+i.val+128),
  (operations_prior_5 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+160), t.2.1<4600+i.val+160)
] by
  decide +kernel


compact_facts [
  (operations_prior_6 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+192), t.2.1<4600+i.val+192),
  (operations_prior_7 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+224), t.2.1<4600+i.val+224)
] by
  decide +kernel


compact_facts [
  (operations_prior_8 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+256), t.2.1<4600+i.val+256),
  (operations_prior_9 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+288), t.2.1<4600+i.val+288)
] by
  decide +kernel


compact_facts [
  (operations_prior_10 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+320), t.2.1<4600+i.val+320),
  (operations_prior_11 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+352), t.2.1<4600+i.val+352)
] by
  decide +kernel


compact_facts [
  (operations_prior_12 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+384), t.2.1<4600+i.val+384),
  (operations_prior_13 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+416), t.2.1<4600+i.val+416)
] by
  decide +kernel


compact_facts [
  (operations_prior_14 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+448), t.2.1<4600+i.val+448),
  (operations_prior_15 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+480), t.2.1<4600+i.val+480)
] by
  decide +kernel


compact_facts [
  (operations_prior_16 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+512), t.2.1<4600+i.val+512),
  (operations_prior_17 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+544), t.2.1<4600+i.val+544)
] by
  decide +kernel


compact_facts [
  (operations_prior_18 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+576), t.2.1<4600+i.val+576),
  (operations_prior_19 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+608), t.2.1<4600+i.val+608)
] by
  decide +kernel


compact_facts [
  (operations_prior_20 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+640), t.2.1<4600+i.val+640),
  (operations_prior_21 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+672), t.2.1<4600+i.val+672)
] by
  decide +kernel


compact_facts [
  (operations_prior_22 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+704), t.2.1<4600+i.val+704),
  (operations_prior_23 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+736), t.2.1<4600+i.val+736)
] by
  decide +kernel


compact_facts [
  (operations_prior_24 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+768), t.2.1<4600+i.val+768),
  (operations_prior_25 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+800), t.2.1<4600+i.val+800)
] by
  decide +kernel


compact_facts [
  (operations_prior_26 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+832), t.2.1<4600+i.val+832),
  (operations_prior_27 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+864), t.2.1<4600+i.val+864)
] by
  decide +kernel


compact_facts [
  (operations_prior_28 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+896), t.2.1<4600+i.val+896),
  (operations_prior_29 : ∀ i : Fin 32, ∀ t ∈ operations (i.val+928), t.2.1<4600+i.val+928)
] by
  decide +kernel

compact_certificate theorem operations_checked_30 : ∀ i : Fin 22, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations (i.val+960))=normal (i.val+960) := by
  let P : ℕ → Prop := fun i => substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations i)=normal i
  have h : ∀ i<22, P (i+960) :=
    (finite_range% P 960 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single7),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single8),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single9),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single10),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single11),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single12),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single13),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single14),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single15),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single16),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single17),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single18),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single19),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single20),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_checked_30_single21)
  ])
  intro i
  simpa only [Nat.add_assoc] using h i.val i.isLt
#print axioms operations_checked_30

compact_certificate theorem operations_prior_30 : ∀ i : Fin 22, ∀ t ∈ operations (i.val+960), t.2.1<4600+i.val+960 := by
  let P : ℕ → Prop := fun i => ∀ t ∈ operations i, t.2.1<4600+i
  have h : ∀ i<22, P (i+960) :=
    (finite_range% P 960 [
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single0),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single1),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single2),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single3),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single4),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single5),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single6),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single7),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single8),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single9),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single10),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single11),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single12),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single13),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single14),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single15),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single16),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single17),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single18),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single19),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single20),
    1 => (QuantitativeArithmeticFiniteRangeCertificates.singleton operations_prior_30_single21)
  ])
  intro i
  simpa only [Nat.add_assoc] using h i.val i.isLt
#print axioms operations_prior_30
}

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelCoordinatesInverseBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

certificate_batch {
compact_certificate theorem coordinate_position_part0 : ∀ i : Fin 32,
    coordinate (position (i.val+0))=i.val+0 := by decide +kernel
#print axioms coordinate_position_part0

compact_certificate theorem coordinate_position_part1 : ∀ i : Fin 32,
    coordinate (position (i.val+32))=i.val+32 := by decide +kernel
#print axioms coordinate_position_part1

compact_certificate theorem coordinate_position_part2 : ∀ i : Fin 32,
    coordinate (position (i.val+64))=i.val+64 := by decide +kernel
#print axioms coordinate_position_part2

compact_certificate theorem coordinate_position_part3 : ∀ i : Fin 32,
    coordinate (position (i.val+96))=i.val+96 := by decide +kernel
#print axioms coordinate_position_part3

compact_certificate theorem coordinate_position_part4 : ∀ i : Fin 32,
    coordinate (position (i.val+128))=i.val+128 := by decide +kernel
#print axioms coordinate_position_part4

compact_certificate theorem coordinate_position_part5 : ∀ i : Fin 32,
    coordinate (position (i.val+160))=i.val+160 := by decide +kernel
#print axioms coordinate_position_part5

compact_certificate theorem coordinate_position_part6 : ∀ i : Fin 32,
    coordinate (position (i.val+192))=i.val+192 := by decide +kernel
#print axioms coordinate_position_part6

compact_certificate theorem coordinate_position_part7 : ∀ i : Fin 32,
    coordinate (position (i.val+224))=i.val+224 := by decide +kernel
#print axioms coordinate_position_part7

compact_certificate theorem coordinate_position_part8 : ∀ i : Fin 32,
    coordinate (position (i.val+256))=i.val+256 := by decide +kernel
#print axioms coordinate_position_part8

compact_certificate theorem coordinate_position_part9 : ∀ i : Fin 32,
    coordinate (position (i.val+288))=i.val+288 := by decide +kernel
#print axioms coordinate_position_part9

compact_certificate theorem coordinate_position_part10 : ∀ i : Fin 32,
    coordinate (position (i.val+320))=i.val+320 := by decide +kernel
#print axioms coordinate_position_part10

compact_certificate theorem coordinate_position_part11 : ∀ i : Fin 32,
    coordinate (position (i.val+352))=i.val+352 := by decide +kernel
#print axioms coordinate_position_part11

compact_certificate theorem coordinate_position_part12 : ∀ i : Fin 32,
    coordinate (position (i.val+384))=i.val+384 := by decide +kernel
#print axioms coordinate_position_part12

compact_certificate theorem coordinate_position_part13 : ∀ i : Fin 32,
    coordinate (position (i.val+416))=i.val+416 := by decide +kernel
#print axioms coordinate_position_part13

compact_certificate theorem coordinate_position_part14 : ∀ i : Fin 32,
    coordinate (position (i.val+448))=i.val+448 := by decide +kernel
#print axioms coordinate_position_part14

compact_certificate theorem coordinate_position_part15 : ∀ i : Fin 32,
    coordinate (position (i.val+480))=i.val+480 := by decide +kernel
#print axioms coordinate_position_part15

compact_certificate theorem coordinate_position_part16 : ∀ i : Fin 32,
    coordinate (position (i.val+512))=i.val+512 := by decide +kernel
#print axioms coordinate_position_part16

compact_certificate theorem coordinate_position_part17 : ∀ i : Fin 32,
    coordinate (position (i.val+544))=i.val+544 := by decide +kernel
#print axioms coordinate_position_part17

compact_certificate theorem coordinate_position_part18 : ∀ i : Fin 32,
    coordinate (position (i.val+576))=i.val+576 := by decide +kernel
#print axioms coordinate_position_part18

compact_certificate theorem coordinate_position_part19 : ∀ i : Fin 32,
    coordinate (position (i.val+608))=i.val+608 := by decide +kernel
#print axioms coordinate_position_part19

compact_certificate theorem coordinate_position_part20 : ∀ i : Fin 32,
    coordinate (position (i.val+640))=i.val+640 := by decide +kernel
#print axioms coordinate_position_part20

compact_certificate theorem coordinate_position_part21 : ∀ i : Fin 32,
    coordinate (position (i.val+672))=i.val+672 := by decide +kernel
#print axioms coordinate_position_part21

compact_certificate theorem coordinate_position_part22 : ∀ i : Fin 32,
    coordinate (position (i.val+704))=i.val+704 := by decide +kernel
#print axioms coordinate_position_part22

compact_certificate theorem coordinate_position_part23 : ∀ i : Fin 32,
    coordinate (position (i.val+736))=i.val+736 := by decide +kernel
#print axioms coordinate_position_part23

compact_certificate theorem coordinate_position_part24 : ∀ i : Fin 32,
    coordinate (position (i.val+768))=i.val+768 := by decide +kernel
#print axioms coordinate_position_part24

compact_certificate theorem coordinate_position_part25 : ∀ i : Fin 32,
    coordinate (position (i.val+800))=i.val+800 := by decide +kernel
#print axioms coordinate_position_part25

compact_certificate theorem coordinate_position_part26 : ∀ i : Fin 32,
    coordinate (position (i.val+832))=i.val+832 := by decide +kernel
#print axioms coordinate_position_part26

compact_certificate theorem coordinate_position_part27 : ∀ i : Fin 32,
    coordinate (position (i.val+864))=i.val+864 := by decide +kernel
#print axioms coordinate_position_part27

compact_certificate theorem coordinate_position_part28 : ∀ i : Fin 32,
    coordinate (position (i.val+896))=i.val+896 := by decide +kernel
#print axioms coordinate_position_part28

compact_certificate theorem coordinate_position_part29 : ∀ i : Fin 32,
    coordinate (position (i.val+928))=i.val+928 := by decide +kernel
#print axioms coordinate_position_part29

compact_certificate theorem coordinate_position_part30 : ∀ i : Fin 32,
    coordinate (position (i.val+960))=i.val+960 := by decide +kernel
#print axioms coordinate_position_part30

compact_certificate theorem coordinate_position_part31 : ∀ i : Fin 32,
    coordinate (position (i.val+992))=i.val+992 := by decide +kernel
#print axioms coordinate_position_part31

compact_certificate theorem coordinate_position_part32 : ∀ i : Fin 26,
    coordinate (position (i.val+1024))=i.val+1024 := by decide +kernel
#print axioms coordinate_position_part32

}

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentTriangularCheckFamilyV4 -/
section
/-! Explicit certificate statements sharing their proof procedures. -/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

certificate_batch {
compact_facts [
  (triangular_checked_0 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+0),(0,0,0,0,0,0,0))] (triTail (i.val+0))=normal (i.val+0)),
  (triangular_checked_1 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+32),(0,0,0,0,0,0,0))] (triTail (i.val+32))=normal (i.val+32))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_2 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+64),(0,0,0,0,0,0,0))] (triTail (i.val+64))=normal (i.val+64)),
  (triangular_checked_3 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+96),(0,0,0,0,0,0,0))] (triTail (i.val+96))=normal (i.val+96))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_4 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+128),(0,0,0,0,0,0,0))] (triTail (i.val+128))=normal (i.val+128)),
  (triangular_checked_5 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+160),(0,0,0,0,0,0,0))] (triTail (i.val+160))=normal (i.val+160))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_6 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+192),(0,0,0,0,0,0,0))] (triTail (i.val+192))=normal (i.val+192)),
  (triangular_checked_7 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+224),(0,0,0,0,0,0,0))] (triTail (i.val+224))=normal (i.val+224))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_8 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+256),(0,0,0,0,0,0,0))] (triTail (i.val+256))=normal (i.val+256)),
  (triangular_checked_9 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+288),(0,0,0,0,0,0,0))] (triTail (i.val+288))=normal (i.val+288))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_10 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+320),(0,0,0,0,0,0,0))] (triTail (i.val+320))=normal (i.val+320)),
  (triangular_checked_11 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+352),(0,0,0,0,0,0,0))] (triTail (i.val+352))=normal (i.val+352))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_12 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+384),(0,0,0,0,0,0,0))] (triTail (i.val+384))=normal (i.val+384)),
  (triangular_checked_13 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+416),(0,0,0,0,0,0,0))] (triTail (i.val+416))=normal (i.val+416))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_14 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+448),(0,0,0,0,0,0,0))] (triTail (i.val+448))=normal (i.val+448)),
  (triangular_checked_15 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+480),(0,0,0,0,0,0,0))] (triTail (i.val+480))=normal (i.val+480))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_16 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+512),(0,0,0,0,0,0,0))] (triTail (i.val+512))=normal (i.val+512)),
  (triangular_checked_17 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+544),(0,0,0,0,0,0,0))] (triTail (i.val+544))=normal (i.val+544))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_18 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+576),(0,0,0,0,0,0,0))] (triTail (i.val+576))=normal (i.val+576)),
  (triangular_checked_19 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+608),(0,0,0,0,0,0,0))] (triTail (i.val+608))=normal (i.val+608))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_20 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+640),(0,0,0,0,0,0,0))] (triTail (i.val+640))=normal (i.val+640)),
  (triangular_checked_21 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+672),(0,0,0,0,0,0,0))] (triTail (i.val+672))=normal (i.val+672))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_22 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+704),(0,0,0,0,0,0,0))] (triTail (i.val+704))=normal (i.val+704)),
  (triangular_checked_23 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+736),(0,0,0,0,0,0,0))] (triTail (i.val+736))=normal (i.val+736))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_24 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+768),(0,0,0,0,0,0,0))] (triTail (i.val+768))=normal (i.val+768)),
  (triangular_checked_25 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+800),(0,0,0,0,0,0,0))] (triTail (i.val+800))=normal (i.val+800))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_26 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+832),(0,0,0,0,0,0,0))] (triTail (i.val+832))=normal (i.val+832)),
  (triangular_checked_27 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+864),(0,0,0,0,0,0,0))] (triTail (i.val+864))=normal (i.val+864))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_28 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+896),(0,0,0,0,0,0,0))] (triTail (i.val+896))=normal (i.val+896)),
  (triangular_checked_29 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+928),(0,0,0,0,0,0,0))] (triTail (i.val+928))=normal (i.val+928))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_30 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+960),(0,0,0,0,0,0,0))] (triTail (i.val+960))=normal (i.val+960)),
  (triangular_checked_31 : ∀ i : Fin 32, mergeFuel 20000 [(1,coordinate (i.val+992),(0,0,0,0,0,0,0))] (triTail (i.val+992))=normal (i.val+992))
] by
  simp only [← mergeCompute_eq]
  decide +kernel


compact_facts [
  (triangular_checked_32 : ∀ i : Fin 26, mergeFuel 20000 [(1,coordinate (i.val+1024),(0,0,0,0,0,0,0))] (triTail (i.val+1024))=normal (i.val+1024))
] by
  simp only [← mergeCompute_eq]
  decide +kernel

compact_facts [
  (triangular_prior_0 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+0), t.2.1<1050 ∧ i.val+0<position t.2.1),
  (triangular_prior_1 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+32), t.2.1<1050 ∧ i.val+32<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_2 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+64), t.2.1<1050 ∧ i.val+64<position t.2.1),
  (triangular_prior_3 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+96), t.2.1<1050 ∧ i.val+96<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_4 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+128), t.2.1<1050 ∧ i.val+128<position t.2.1),
  (triangular_prior_5 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+160), t.2.1<1050 ∧ i.val+160<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_6 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+192), t.2.1<1050 ∧ i.val+192<position t.2.1),
  (triangular_prior_7 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+224), t.2.1<1050 ∧ i.val+224<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_8 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+256), t.2.1<1050 ∧ i.val+256<position t.2.1),
  (triangular_prior_9 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+288), t.2.1<1050 ∧ i.val+288<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_10 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+320), t.2.1<1050 ∧ i.val+320<position t.2.1),
  (triangular_prior_11 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+352), t.2.1<1050 ∧ i.val+352<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_12 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+384), t.2.1<1050 ∧ i.val+384<position t.2.1),
  (triangular_prior_13 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+416), t.2.1<1050 ∧ i.val+416<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_14 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+448), t.2.1<1050 ∧ i.val+448<position t.2.1),
  (triangular_prior_15 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+480), t.2.1<1050 ∧ i.val+480<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_16 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+512), t.2.1<1050 ∧ i.val+512<position t.2.1),
  (triangular_prior_17 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+544), t.2.1<1050 ∧ i.val+544<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_18 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+576), t.2.1<1050 ∧ i.val+576<position t.2.1),
  (triangular_prior_19 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+608), t.2.1<1050 ∧ i.val+608<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_20 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+640), t.2.1<1050 ∧ i.val+640<position t.2.1),
  (triangular_prior_21 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+672), t.2.1<1050 ∧ i.val+672<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_22 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+704), t.2.1<1050 ∧ i.val+704<position t.2.1),
  (triangular_prior_23 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+736), t.2.1<1050 ∧ i.val+736<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_24 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+768), t.2.1<1050 ∧ i.val+768<position t.2.1),
  (triangular_prior_25 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+800), t.2.1<1050 ∧ i.val+800<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_26 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+832), t.2.1<1050 ∧ i.val+832<position t.2.1),
  (triangular_prior_27 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+864), t.2.1<1050 ∧ i.val+864<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_28 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+896), t.2.1<1050 ∧ i.val+896<position t.2.1),
  (triangular_prior_29 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+928), t.2.1<1050 ∧ i.val+928<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_30 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+960), t.2.1<1050 ∧ i.val+960<position t.2.1),
  (triangular_prior_31 : ∀ i : Fin 32, ∀ t ∈ triTail (i.val+992), t.2.1<1050 ∧ i.val+992<position t.2.1)
] by
  decide +kernel


compact_facts [
  (triangular_prior_32 : ∀ i : Fin 26, ∀ t ∈ triTail (i.val+1024), t.2.1<1050 ∧ i.val+1024<position t.2.1)
] by
  decide +kernel
}

end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

