module
public meta import QuantitativeArithmeticSparseCertificateComputeV5
public meta import SmallLevelCertificateBatchCommandV1
public meta import SmallLevelSparsePolynomialLiteralV1

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelPolynomialCoefficientAssemblyV1
public import SmallLevelSparseCoefficientAssemblyV1
public import SmallLevelSparseCoefficientPartitionV1
public import SmallLevelTwentySixResultantPolynomialDataV1
public import SmallLevelTwentySixWeightAbelMMMDataV1
public meta import QuantitativeArithmeticCompactCommandsV1

public import SmallLevelTwentySixResultantCoefficientsMMMCertificateDataV1
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false


certificate_batch {
/-! ## SmallLevelTwentySixResultantCoefficientsMMMRowIndexXBundleSeriesV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantCoefficientsMMM
open Complex QuantitativeArithmeticSparsePolynomialCertificate

/-! Complete coefficient rows, checked directly by sparse integer arithmetic.
No intermediate partial-result polynomials or stage-by-stage proofs are needed. -/

compact_certificate theorem row1_x00 (y z w : ℂ) :
    q0000 y z w*r0100 y z w +
    q0100 y z w*r0000 y z w +
    q0400 y z w*v0100 y z w +
    q0500 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (product q0000Data r0100Data) (product q0100Data r0000Data)) (product q0400Data v0100Data)) (product q0500Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0100, q0400, q0500, r0000, r0100, v0000, v0100] using he


compact_certificate theorem row1_x01 (y z w : ℂ) :
    q0000 y z w*r0101 y z w +
    q0001 y z w*r0100 y z w +
    q0100 y z w*r0001 y z w +
    q0101 y z w*r0000 y z w +
    q0400 y z w*v0101 y z w +
    q0401 y z w*v0100 y z w +
    q0500 y z w*v0001 y z w +
    q0501 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0101Data) (product q0001Data r0100Data)) (product q0100Data r0001Data)) (product q0101Data r0000Data)) (product q0400Data v0101Data)) (product q0401Data v0100Data)) (product q0500Data v0001Data)) (product q0501Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0100, q0101, q0400, q0401, q0500, q0501, r0000, r0001, r0100, r0101, v0000, v0001, v0100, v0101] using he


compact_certificate theorem row1_x02 (y z w : ℂ) :
    q0000 y z w*r0102 y z w +
    q0001 y z w*r0101 y z w +
    q0002 y z w*r0100 y z w +
    q0100 y z w*r0002 y z w +
    q0101 y z w*r0001 y z w +
    q0102 y z w*r0000 y z w +
    q0400 y z w*v0102 y z w +
    q0401 y z w*v0101 y z w +
    q0402 y z w*v0100 y z w +
    q0500 y z w*v0002 y z w +
    q0501 y z w*v0001 y z w +
    q0502 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0102Data) (product q0001Data r0101Data)) (product q0002Data r0100Data)) (product q0100Data r0002Data)) (product q0101Data r0001Data)) (product q0102Data r0000Data)) (product q0400Data v0102Data)) (product q0401Data v0101Data)) (product q0402Data v0100Data)) (product q0500Data v0002Data)) (product q0501Data v0001Data)) (product q0502Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0002, q0100, q0101, q0102, q0400, q0401, q0402, q0500, q0501, q0502, r0000, r0001, r0002, r0100, r0101, r0102, v0000, v0001, v0002, v0100, v0101, v0102] using he


compact_certificate theorem row1_x03 (y z w : ℂ) :
    q0000 y z w*r0103 y z w +
    q0001 y z w*r0102 y z w +
    q0002 y z w*r0101 y z w +
    q0003 y z w*r0100 y z w +
    q0100 y z w*r0003 y z w +
    q0101 y z w*r0002 y z w +
    q0102 y z w*r0001 y z w +
    q0103 y z w*r0000 y z w +
    q0400 y z w*v0103 y z w +
    q0401 y z w*v0102 y z w +
    q0402 y z w*v0101 y z w +
    q0403 y z w*v0100 y z w +
    q0500 y z w*v0003 y z w +
    q0501 y z w*v0002 y z w +
    q0502 y z w*v0001 y z w +
    q0503 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0103Data) (product q0001Data r0102Data)) (product q0002Data r0101Data)) (product q0003Data r0100Data)) (product q0100Data r0003Data)) (product q0101Data r0002Data)) (product q0102Data r0001Data)) (product q0103Data r0000Data)) (product q0400Data v0103Data)) (product q0401Data v0102Data)) (product q0402Data v0101Data)) (product q0403Data v0100Data)) (product q0500Data v0003Data)) (product q0501Data v0002Data)) (product q0502Data v0001Data)) (product q0503Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0002, q0003, q0100, q0101, q0102, q0103, q0400, q0401, q0402, q0403, q0500, q0501, q0502, q0503, r0000, r0001, r0002, r0003, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0100, v0101, v0102, v0103] using he


compact_certificate theorem row1_x04 (y z w : ℂ) :
    q0001 y z w*r0103 y z w +
    q0002 y z w*r0102 y z w +
    q0003 y z w*r0101 y z w +
    q0004 y z w*r0100 y z w +
    q0101 y z w*r0003 y z w +
    q0102 y z w*r0002 y z w +
    q0103 y z w*r0001 y z w +
    q0104 y z w*r0000 y z w +
    q0400 y z w*v0104 y z w +
    q0401 y z w*v0103 y z w +
    q0402 y z w*v0102 y z w +
    q0403 y z w*v0101 y z w +
    q0404 y z w*v0100 y z w +
    q0500 y z w*v0004 y z w +
    q0501 y z w*v0003 y z w +
    q0502 y z w*v0002 y z w +
    q0503 y z w*v0001 y z w +
    q0504 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0001Data r0103Data) (product q0002Data r0102Data)) (product q0003Data r0101Data)) (product q0004Data r0100Data)) (product q0101Data r0003Data)) (product q0102Data r0002Data)) (product q0103Data r0001Data)) (product q0104Data r0000Data)) (product q0400Data v0104Data)) (product q0401Data v0103Data)) (product q0402Data v0102Data)) (product q0403Data v0101Data)) (product q0404Data v0100Data)) (product q0500Data v0004Data)) (product q0501Data v0003Data)) (product q0502Data v0002Data)) (product q0503Data v0001Data)) (product q0504Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0001, q0002, q0003, q0004, q0101, q0102, q0103, q0104, q0400, q0401, q0402, q0403, q0404, q0500, q0501, q0502, q0503, q0504, r0000, r0001, r0002, r0003, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0100, v0101, v0102, v0103, v0104] using he


compact_certificate theorem row1_x05 (y z w : ℂ) :
    q0002 y z w*r0103 y z w +
    q0003 y z w*r0102 y z w +
    q0004 y z w*r0101 y z w +
    q0005 y z w*r0100 y z w +
    q0100 y z w*r0005 y z w +
    q0102 y z w*r0003 y z w +
    q0103 y z w*r0002 y z w +
    q0104 y z w*r0001 y z w +
    q0105 y z w*r0000 y z w +
    q0400 y z w*v0105 y z w +
    q0401 y z w*v0104 y z w +
    q0402 y z w*v0103 y z w +
    q0403 y z w*v0102 y z w +
    q0404 y z w*v0101 y z w +
    q0405 y z w*v0100 y z w +
    q0500 y z w*v0005 y z w +
    q0501 y z w*v0004 y z w +
    q0502 y z w*v0003 y z w +
    q0503 y z w*v0002 y z w +
    q0504 y z w*v0001 y z w +
    q0505 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0002Data r0103Data) (product q0003Data r0102Data)) (product q0004Data r0101Data)) (product q0005Data r0100Data)) (product q0100Data r0005Data)) (product q0102Data r0003Data)) (product q0103Data r0002Data)) (product q0104Data r0001Data)) (product q0105Data r0000Data)) (product q0400Data v0105Data)) (product q0401Data v0104Data)) (product q0402Data v0103Data)) (product q0403Data v0102Data)) (product q0404Data v0101Data)) (product q0405Data v0100Data)) (product q0500Data v0005Data)) (product q0501Data v0004Data)) (product q0502Data v0003Data)) (product q0503Data v0002Data)) (product q0504Data v0001Data)) (product q0505Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0002, q0003, q0004, q0005, q0100, q0102, q0103, q0104, q0105, q0400, q0401, q0402, q0403, q0404, q0405, q0500, q0501, q0502, q0503, q0504, q0505, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0100, v0101, v0102, v0103, v0104, v0105] using he


compact_certificate theorem row1_x06 (y z w : ℂ) :
    q0003 y z w*r0103 y z w +
    q0004 y z w*r0102 y z w +
    q0005 y z w*r0101 y z w +
    q0006 y z w*r0100 y z w +
    q0101 y z w*r0005 y z w +
    q0103 y z w*r0003 y z w +
    q0104 y z w*r0002 y z w +
    q0105 y z w*r0001 y z w +
    q0106 y z w*r0000 y z w +
    q0400 y z w*v0106 y z w +
    q0401 y z w*v0105 y z w +
    q0402 y z w*v0104 y z w +
    q0403 y z w*v0103 y z w +
    q0404 y z w*v0102 y z w +
    q0405 y z w*v0101 y z w +
    q0406 y z w*v0100 y z w +
    q0500 y z w*v0006 y z w +
    q0501 y z w*v0005 y z w +
    q0502 y z w*v0004 y z w +
    q0503 y z w*v0003 y z w +
    q0504 y z w*v0002 y z w +
    q0505 y z w*v0001 y z w +
    q0506 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0003Data r0103Data) (product q0004Data r0102Data)) (product q0005Data r0101Data)) (product q0006Data r0100Data)) (product q0101Data r0005Data)) (product q0103Data r0003Data)) (product q0104Data r0002Data)) (product q0105Data r0001Data)) (product q0106Data r0000Data)) (product q0400Data v0106Data)) (product q0401Data v0105Data)) (product q0402Data v0104Data)) (product q0403Data v0103Data)) (product q0404Data v0102Data)) (product q0405Data v0101Data)) (product q0406Data v0100Data)) (product q0500Data v0006Data)) (product q0501Data v0005Data)) (product q0502Data v0004Data)) (product q0503Data v0003Data)) (product q0504Data v0002Data)) (product q0505Data v0001Data)) (product q0506Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0003, q0004, q0005, q0006, q0101, q0103, q0104, q0105, q0106, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0500, q0501, q0502, q0503, q0504, q0505, q0506, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0100, v0101, v0102, v0103, v0104, v0105, v0106] using he


compact_certificate theorem row1_x07 (y z w : ℂ) :
    q0004 y z w*r0103 y z w +
    q0005 y z w*r0102 y z w +
    q0006 y z w*r0101 y z w +
    q0007 y z w*r0100 y z w +
    q0102 y z w*r0005 y z w +
    q0104 y z w*r0003 y z w +
    q0105 y z w*r0002 y z w +
    q0106 y z w*r0001 y z w +
    q0107 y z w*r0000 y z w +
    q0400 y z w*v0107 y z w +
    q0401 y z w*v0106 y z w +
    q0402 y z w*v0105 y z w +
    q0403 y z w*v0104 y z w +
    q0404 y z w*v0103 y z w +
    q0405 y z w*v0102 y z w +
    q0406 y z w*v0101 y z w +
    q0407 y z w*v0100 y z w +
    q0500 y z w*v0007 y z w +
    q0501 y z w*v0006 y z w +
    q0502 y z w*v0005 y z w +
    q0503 y z w*v0004 y z w +
    q0504 y z w*v0003 y z w +
    q0505 y z w*v0002 y z w +
    q0506 y z w*v0001 y z w +
    q0507 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0004Data r0103Data) (product q0005Data r0102Data)) (product q0006Data r0101Data)) (product q0007Data r0100Data)) (product q0102Data r0005Data)) (product q0104Data r0003Data)) (product q0105Data r0002Data)) (product q0106Data r0001Data)) (product q0107Data r0000Data)) (product q0400Data v0107Data)) (product q0401Data v0106Data)) (product q0402Data v0105Data)) (product q0403Data v0104Data)) (product q0404Data v0103Data)) (product q0405Data v0102Data)) (product q0406Data v0101Data)) (product q0407Data v0100Data)) (product q0500Data v0007Data)) (product q0501Data v0006Data)) (product q0502Data v0005Data)) (product q0503Data v0004Data)) (product q0504Data v0003Data)) (product q0505Data v0002Data)) (product q0506Data v0001Data)) (product q0507Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0004, q0005, q0006, q0007, q0102, q0104, q0105, q0106, q0107, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107] using he


compact_certificate theorem row1_x08 (y z w : ℂ) :
    q0005 y z w*r0103 y z w +
    q0006 y z w*r0102 y z w +
    q0007 y z w*r0101 y z w +
    q0008 y z w*r0100 y z w +
    q0103 y z w*r0005 y z w +
    q0105 y z w*r0003 y z w +
    q0106 y z w*r0002 y z w +
    q0107 y z w*r0001 y z w +
    q0108 y z w*r0000 y z w +
    q0400 y z w*v0108 y z w +
    q0401 y z w*v0107 y z w +
    q0402 y z w*v0106 y z w +
    q0403 y z w*v0105 y z w +
    q0404 y z w*v0104 y z w +
    q0405 y z w*v0103 y z w +
    q0406 y z w*v0102 y z w +
    q0407 y z w*v0101 y z w +
    q0408 y z w*v0100 y z w +
    q0500 y z w*v0008 y z w +
    q0501 y z w*v0007 y z w +
    q0502 y z w*v0006 y z w +
    q0503 y z w*v0005 y z w +
    q0504 y z w*v0004 y z w +
    q0505 y z w*v0003 y z w +
    q0506 y z w*v0002 y z w +
    q0507 y z w*v0001 y z w +
    q0508 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0005Data r0103Data) (product q0006Data r0102Data)) (product q0007Data r0101Data)) (product q0008Data r0100Data)) (product q0103Data r0005Data)) (product q0105Data r0003Data)) (product q0106Data r0002Data)) (product q0107Data r0001Data)) (product q0108Data r0000Data)) (product q0400Data v0108Data)) (product q0401Data v0107Data)) (product q0402Data v0106Data)) (product q0403Data v0105Data)) (product q0404Data v0104Data)) (product q0405Data v0103Data)) (product q0406Data v0102Data)) (product q0407Data v0101Data)) (product q0408Data v0100Data)) (product q0500Data v0008Data)) (product q0501Data v0007Data)) (product q0502Data v0006Data)) (product q0503Data v0005Data)) (product q0504Data v0004Data)) (product q0505Data v0003Data)) (product q0506Data v0002Data)) (product q0507Data v0001Data)) (product q0508Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0005, q0006, q0007, q0008, q0103, q0105, q0106, q0107, q0108, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108] using he


compact_certificate theorem row1_x09 (y z w : ℂ) :
    q0006 y z w*r0103 y z w +
    q0007 y z w*r0102 y z w +
    q0008 y z w*r0101 y z w +
    q0009 y z w*r0100 y z w +
    q0104 y z w*r0005 y z w +
    q0106 y z w*r0003 y z w +
    q0107 y z w*r0002 y z w +
    q0108 y z w*r0001 y z w +
    q0109 y z w*r0000 y z w +
    q0400 y z w*v0109 y z w +
    q0401 y z w*v0108 y z w +
    q0402 y z w*v0107 y z w +
    q0403 y z w*v0106 y z w +
    q0404 y z w*v0105 y z w +
    q0405 y z w*v0104 y z w +
    q0406 y z w*v0103 y z w +
    q0407 y z w*v0102 y z w +
    q0408 y z w*v0101 y z w +
    q0409 y z w*v0100 y z w +
    q0500 y z w*v0009 y z w +
    q0501 y z w*v0008 y z w +
    q0502 y z w*v0007 y z w +
    q0503 y z w*v0006 y z w +
    q0504 y z w*v0005 y z w +
    q0505 y z w*v0004 y z w +
    q0506 y z w*v0003 y z w +
    q0507 y z w*v0002 y z w +
    q0508 y z w*v0001 y z w +
    q0509 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0006Data r0103Data) (product q0007Data r0102Data)) (product q0008Data r0101Data)) (product q0009Data r0100Data)) (product q0104Data r0005Data)) (product q0106Data r0003Data)) (product q0107Data r0002Data)) (product q0108Data r0001Data)) (product q0109Data r0000Data)) (product q0400Data v0109Data)) (product q0401Data v0108Data)) (product q0402Data v0107Data)) (product q0403Data v0106Data)) (product q0404Data v0105Data)) (product q0405Data v0104Data)) (product q0406Data v0103Data)) (product q0407Data v0102Data)) (product q0408Data v0101Data)) (product q0409Data v0100Data)) (product q0500Data v0009Data)) (product q0501Data v0008Data)) (product q0502Data v0007Data)) (product q0503Data v0006Data)) (product q0504Data v0005Data)) (product q0505Data v0004Data)) (product q0506Data v0003Data)) (product q0507Data v0002Data)) (product q0508Data v0001Data)) (product q0509Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0006, q0007, q0008, q0009, q0104, q0106, q0107, q0108, q0109, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109] using he


compact_certificate theorem row1_x10 (y z w : ℂ) :
    q0007 y z w*r0103 y z w +
    q0008 y z w*r0102 y z w +
    q0009 y z w*r0101 y z w +
    q0010 y z w*r0100 y z w +
    q0105 y z w*r0005 y z w +
    q0107 y z w*r0003 y z w +
    q0108 y z w*r0002 y z w +
    q0109 y z w*r0001 y z w +
    q0110 y z w*r0000 y z w +
    q0400 y z w*v0110 y z w +
    q0401 y z w*v0109 y z w +
    q0402 y z w*v0108 y z w +
    q0403 y z w*v0107 y z w +
    q0404 y z w*v0106 y z w +
    q0405 y z w*v0105 y z w +
    q0406 y z w*v0104 y z w +
    q0407 y z w*v0103 y z w +
    q0408 y z w*v0102 y z w +
    q0409 y z w*v0101 y z w +
    q0410 y z w*v0100 y z w +
    q0500 y z w*v0010 y z w +
    q0501 y z w*v0009 y z w +
    q0502 y z w*v0008 y z w +
    q0503 y z w*v0007 y z w +
    q0504 y z w*v0006 y z w +
    q0505 y z w*v0005 y z w +
    q0506 y z w*v0004 y z w +
    q0507 y z w*v0003 y z w +
    q0508 y z w*v0002 y z w +
    q0509 y z w*v0001 y z w +
    q0510 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0007Data r0103Data) (product q0008Data r0102Data)) (product q0009Data r0101Data)) (product q0010Data r0100Data)) (product q0105Data r0005Data)) (product q0107Data r0003Data)) (product q0108Data r0002Data)) (product q0109Data r0001Data)) (product q0110Data r0000Data)) (product q0400Data v0110Data)) (product q0401Data v0109Data)) (product q0402Data v0108Data)) (product q0403Data v0107Data)) (product q0404Data v0106Data)) (product q0405Data v0105Data)) (product q0406Data v0104Data)) (product q0407Data v0103Data)) (product q0408Data v0102Data)) (product q0409Data v0101Data)) (product q0410Data v0100Data)) (product q0500Data v0010Data)) (product q0501Data v0009Data)) (product q0502Data v0008Data)) (product q0503Data v0007Data)) (product q0504Data v0006Data)) (product q0505Data v0005Data)) (product q0506Data v0004Data)) (product q0507Data v0003Data)) (product q0508Data v0002Data)) (product q0509Data v0001Data)) (product q0510Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0007, q0008, q0009, q0010, q0105, q0107, q0108, q0109, q0110, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he


compact_certificate theorem row1_x11 (y z w : ℂ) :
    q0008 y z w*r0103 y z w +
    q0009 y z w*r0102 y z w +
    q0010 y z w*r0101 y z w +
    q0011 y z w*r0100 y z w +
    q0106 y z w*r0005 y z w +
    q0108 y z w*r0003 y z w +
    q0109 y z w*r0002 y z w +
    q0110 y z w*r0001 y z w +
    q0111 y z w*r0000 y z w +
    q0401 y z w*v0110 y z w +
    q0402 y z w*v0109 y z w +
    q0403 y z w*v0108 y z w +
    q0404 y z w*v0107 y z w +
    q0405 y z w*v0106 y z w +
    q0406 y z w*v0105 y z w +
    q0407 y z w*v0104 y z w +
    q0408 y z w*v0103 y z w +
    q0409 y z w*v0102 y z w +
    q0410 y z w*v0101 y z w +
    q0411 y z w*v0100 y z w +
    q0500 y z w*v0011 y z w +
    q0501 y z w*v0010 y z w +
    q0502 y z w*v0009 y z w +
    q0503 y z w*v0008 y z w +
    q0504 y z w*v0007 y z w +
    q0505 y z w*v0006 y z w +
    q0506 y z w*v0005 y z w +
    q0507 y z w*v0004 y z w +
    q0508 y z w*v0003 y z w +
    q0509 y z w*v0002 y z w +
    q0510 y z w*v0001 y z w +
    q0511 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0008Data r0103Data) (product q0009Data r0102Data)) (product q0010Data r0101Data)) (product q0011Data r0100Data)) (product q0106Data r0005Data)) (product q0108Data r0003Data)) (product q0109Data r0002Data)) (product q0110Data r0001Data)) (product q0111Data r0000Data)) (product q0401Data v0110Data)) (product q0402Data v0109Data)) (product q0403Data v0108Data)) (product q0404Data v0107Data)) (product q0405Data v0106Data)) (product q0406Data v0105Data)) (product q0407Data v0104Data)) (product q0408Data v0103Data)) (product q0409Data v0102Data)) (product q0410Data v0101Data)) (product q0411Data v0100Data)) (product q0500Data v0011Data)) (product q0501Data v0010Data)) (product q0502Data v0009Data)) (product q0503Data v0008Data)) (product q0504Data v0007Data)) (product q0505Data v0006Data)) (product q0506Data v0005Data)) (product q0507Data v0004Data)) (product q0508Data v0003Data)) (product q0509Data v0002Data)) (product q0510Data v0001Data)) (product q0511Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0008, q0009, q0010, q0011, q0106, q0108, q0109, q0110, q0111, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he


compact_certificate theorem row1_x12 (y z w : ℂ) :
    q0009 y z w*r0103 y z w +
    q0010 y z w*r0102 y z w +
    q0011 y z w*r0101 y z w +
    q0012 y z w*r0100 y z w +
    q0107 y z w*r0005 y z w +
    q0109 y z w*r0003 y z w +
    q0110 y z w*r0002 y z w +
    q0111 y z w*r0001 y z w +
    q0112 y z w*r0000 y z w +
    q0402 y z w*v0110 y z w +
    q0403 y z w*v0109 y z w +
    q0404 y z w*v0108 y z w +
    q0405 y z w*v0107 y z w +
    q0406 y z w*v0106 y z w +
    q0407 y z w*v0105 y z w +
    q0408 y z w*v0104 y z w +
    q0409 y z w*v0103 y z w +
    q0410 y z w*v0102 y z w +
    q0411 y z w*v0101 y z w +
    q0412 y z w*v0100 y z w +
    q0501 y z w*v0011 y z w +
    q0502 y z w*v0010 y z w +
    q0503 y z w*v0009 y z w +
    q0504 y z w*v0008 y z w +
    q0505 y z w*v0007 y z w +
    q0506 y z w*v0006 y z w +
    q0507 y z w*v0005 y z w +
    q0508 y z w*v0004 y z w +
    q0509 y z w*v0003 y z w +
    q0510 y z w*v0002 y z w +
    q0511 y z w*v0001 y z w +
    q0512 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0009Data r0103Data) (product q0010Data r0102Data)) (product q0011Data r0101Data)) (product q0012Data r0100Data)) (product q0107Data r0005Data)) (product q0109Data r0003Data)) (product q0110Data r0002Data)) (product q0111Data r0001Data)) (product q0112Data r0000Data)) (product q0402Data v0110Data)) (product q0403Data v0109Data)) (product q0404Data v0108Data)) (product q0405Data v0107Data)) (product q0406Data v0106Data)) (product q0407Data v0105Data)) (product q0408Data v0104Data)) (product q0409Data v0103Data)) (product q0410Data v0102Data)) (product q0411Data v0101Data)) (product q0412Data v0100Data)) (product q0501Data v0011Data)) (product q0502Data v0010Data)) (product q0503Data v0009Data)) (product q0504Data v0008Data)) (product q0505Data v0007Data)) (product q0506Data v0006Data)) (product q0507Data v0005Data)) (product q0508Data v0004Data)) (product q0509Data v0003Data)) (product q0510Data v0002Data)) (product q0511Data v0001Data)) (product q0512Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0009, q0010, q0011, q0012, q0107, q0109, q0110, q0111, q0112, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he


compact_certificate theorem row1_x13 (y z w : ℂ) :
    q0010 y z w*r0103 y z w +
    q0011 y z w*r0102 y z w +
    q0012 y z w*r0101 y z w +
    q0013 y z w*r0100 y z w +
    q0108 y z w*r0005 y z w +
    q0110 y z w*r0003 y z w +
    q0111 y z w*r0002 y z w +
    q0112 y z w*r0001 y z w +
    q0113 y z w*r0000 y z w +
    q0403 y z w*v0110 y z w +
    q0404 y z w*v0109 y z w +
    q0405 y z w*v0108 y z w +
    q0406 y z w*v0107 y z w +
    q0407 y z w*v0106 y z w +
    q0408 y z w*v0105 y z w +
    q0409 y z w*v0104 y z w +
    q0410 y z w*v0103 y z w +
    q0411 y z w*v0102 y z w +
    q0412 y z w*v0101 y z w +
    q0413 y z w*v0100 y z w +
    q0502 y z w*v0011 y z w +
    q0503 y z w*v0010 y z w +
    q0504 y z w*v0009 y z w +
    q0505 y z w*v0008 y z w +
    q0506 y z w*v0007 y z w +
    q0507 y z w*v0006 y z w +
    q0508 y z w*v0005 y z w +
    q0509 y z w*v0004 y z w +
    q0510 y z w*v0003 y z w +
    q0511 y z w*v0002 y z w +
    q0512 y z w*v0001 y z w +
    q0513 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0010Data r0103Data) (product q0011Data r0102Data)) (product q0012Data r0101Data)) (product q0013Data r0100Data)) (product q0108Data r0005Data)) (product q0110Data r0003Data)) (product q0111Data r0002Data)) (product q0112Data r0001Data)) (product q0113Data r0000Data)) (product q0403Data v0110Data)) (product q0404Data v0109Data)) (product q0405Data v0108Data)) (product q0406Data v0107Data)) (product q0407Data v0106Data)) (product q0408Data v0105Data)) (product q0409Data v0104Data)) (product q0410Data v0103Data)) (product q0411Data v0102Data)) (product q0412Data v0101Data)) (product q0413Data v0100Data)) (product q0502Data v0011Data)) (product q0503Data v0010Data)) (product q0504Data v0009Data)) (product q0505Data v0008Data)) (product q0506Data v0007Data)) (product q0507Data v0006Data)) (product q0508Data v0005Data)) (product q0509Data v0004Data)) (product q0510Data v0003Data)) (product q0511Data v0002Data)) (product q0512Data v0001Data)) (product q0513Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0010, q0011, q0012, q0013, q0108, q0110, q0111, q0112, q0113, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he


compact_certificate theorem row1_x14 (y z w : ℂ) :
    q0011 y z w*r0103 y z w +
    q0012 y z w*r0102 y z w +
    q0013 y z w*r0101 y z w +
    q0014 y z w*r0100 y z w +
    q0109 y z w*r0005 y z w +
    q0111 y z w*r0003 y z w +
    q0112 y z w*r0002 y z w +
    q0113 y z w*r0001 y z w +
    q0114 y z w*r0000 y z w +
    q0404 y z w*v0110 y z w +
    q0405 y z w*v0109 y z w +
    q0406 y z w*v0108 y z w +
    q0407 y z w*v0107 y z w +
    q0408 y z w*v0106 y z w +
    q0409 y z w*v0105 y z w +
    q0410 y z w*v0104 y z w +
    q0411 y z w*v0103 y z w +
    q0412 y z w*v0102 y z w +
    q0413 y z w*v0101 y z w +
    q0414 y z w*v0100 y z w +
    q0503 y z w*v0011 y z w +
    q0504 y z w*v0010 y z w +
    q0505 y z w*v0009 y z w +
    q0506 y z w*v0008 y z w +
    q0507 y z w*v0007 y z w +
    q0508 y z w*v0006 y z w +
    q0509 y z w*v0005 y z w +
    q0510 y z w*v0004 y z w +
    q0511 y z w*v0003 y z w +
    q0512 y z w*v0002 y z w +
    q0513 y z w*v0001 y z w +
    q0514 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0011Data r0103Data) (product q0012Data r0102Data)) (product q0013Data r0101Data)) (product q0014Data r0100Data)) (product q0109Data r0005Data)) (product q0111Data r0003Data)) (product q0112Data r0002Data)) (product q0113Data r0001Data)) (product q0114Data r0000Data)) (product q0404Data v0110Data)) (product q0405Data v0109Data)) (product q0406Data v0108Data)) (product q0407Data v0107Data)) (product q0408Data v0106Data)) (product q0409Data v0105Data)) (product q0410Data v0104Data)) (product q0411Data v0103Data)) (product q0412Data v0102Data)) (product q0413Data v0101Data)) (product q0414Data v0100Data)) (product q0503Data v0011Data)) (product q0504Data v0010Data)) (product q0505Data v0009Data)) (product q0506Data v0008Data)) (product q0507Data v0007Data)) (product q0508Data v0006Data)) (product q0509Data v0005Data)) (product q0510Data v0004Data)) (product q0511Data v0003Data)) (product q0512Data v0002Data)) (product q0513Data v0001Data)) (product q0514Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0011, q0012, q0013, q0014, q0109, q0111, q0112, q0113, q0114, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he


compact_certificate theorem row1_x15 (y z w : ℂ) :
    q0012 y z w*r0103 y z w +
    q0013 y z w*r0102 y z w +
    q0014 y z w*r0101 y z w +
    q0015 y z w*r0100 y z w +
    q0110 y z w*r0005 y z w +
    q0112 y z w*r0003 y z w +
    q0113 y z w*r0002 y z w +
    q0114 y z w*r0001 y z w +
    q0115 y z w*r0000 y z w +
    q0405 y z w*v0110 y z w +
    q0406 y z w*v0109 y z w +
    q0407 y z w*v0108 y z w +
    q0408 y z w*v0107 y z w +
    q0409 y z w*v0106 y z w +
    q0410 y z w*v0105 y z w +
    q0411 y z w*v0104 y z w +
    q0412 y z w*v0103 y z w +
    q0413 y z w*v0102 y z w +
    q0414 y z w*v0101 y z w +
    q0415 y z w*v0100 y z w +
    q0504 y z w*v0011 y z w +
    q0505 y z w*v0010 y z w +
    q0506 y z w*v0009 y z w +
    q0507 y z w*v0008 y z w +
    q0508 y z w*v0007 y z w +
    q0509 y z w*v0006 y z w +
    q0510 y z w*v0005 y z w +
    q0511 y z w*v0004 y z w +
    q0512 y z w*v0003 y z w +
    q0513 y z w*v0002 y z w +
    q0514 y z w*v0001 y z w +
    q0515 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0012Data r0103Data) (product q0013Data r0102Data)) (product q0014Data r0101Data)) (product q0015Data r0100Data)) (product q0110Data r0005Data)) (product q0112Data r0003Data)) (product q0113Data r0002Data)) (product q0114Data r0001Data)) (product q0115Data r0000Data)) (product q0405Data v0110Data)) (product q0406Data v0109Data)) (product q0407Data v0108Data)) (product q0408Data v0107Data)) (product q0409Data v0106Data)) (product q0410Data v0105Data)) (product q0411Data v0104Data)) (product q0412Data v0103Data)) (product q0413Data v0102Data)) (product q0414Data v0101Data)) (product q0415Data v0100Data)) (product q0504Data v0011Data)) (product q0505Data v0010Data)) (product q0506Data v0009Data)) (product q0507Data v0008Data)) (product q0508Data v0007Data)) (product q0509Data v0006Data)) (product q0510Data v0005Data)) (product q0511Data v0004Data)) (product q0512Data v0003Data)) (product q0513Data v0002Data)) (product q0514Data v0001Data)) (product q0515Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0012, q0013, q0014, q0015, q0110, q0112, q0113, q0114, q0115, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he


compact_certificate theorem row1_x16 (y z w : ℂ) :
    q0013 y z w*r0103 y z w +
    q0014 y z w*r0102 y z w +
    q0015 y z w*r0101 y z w +
    q0016 y z w*r0100 y z w +
    q0111 y z w*r0005 y z w +
    q0113 y z w*r0003 y z w +
    q0114 y z w*r0002 y z w +
    q0115 y z w*r0001 y z w +
    q0116 y z w*r0000 y z w +
    q0406 y z w*v0110 y z w +
    q0407 y z w*v0109 y z w +
    q0408 y z w*v0108 y z w +
    q0409 y z w*v0107 y z w +
    q0410 y z w*v0106 y z w +
    q0411 y z w*v0105 y z w +
    q0412 y z w*v0104 y z w +
    q0413 y z w*v0103 y z w +
    q0414 y z w*v0102 y z w +
    q0415 y z w*v0101 y z w +
    q0416 y z w*v0100 y z w +
    q0505 y z w*v0011 y z w +
    q0506 y z w*v0010 y z w +
    q0507 y z w*v0009 y z w +
    q0508 y z w*v0008 y z w +
    q0509 y z w*v0007 y z w +
    q0510 y z w*v0006 y z w +
    q0511 y z w*v0005 y z w +
    q0512 y z w*v0004 y z w +
    q0513 y z w*v0003 y z w +
    q0514 y z w*v0002 y z w +
    q0515 y z w*v0001 y z w +
    q0516 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0013Data r0103Data) (product q0014Data r0102Data)) (product q0015Data r0101Data)) (product q0016Data r0100Data)) (product q0111Data r0005Data)) (product q0113Data r0003Data)) (product q0114Data r0002Data)) (product q0115Data r0001Data)) (product q0116Data r0000Data)) (product q0406Data v0110Data)) (product q0407Data v0109Data)) (product q0408Data v0108Data)) (product q0409Data v0107Data)) (product q0410Data v0106Data)) (product q0411Data v0105Data)) (product q0412Data v0104Data)) (product q0413Data v0103Data)) (product q0414Data v0102Data)) (product q0415Data v0101Data)) (product q0416Data v0100Data)) (product q0505Data v0011Data)) (product q0506Data v0010Data)) (product q0507Data v0009Data)) (product q0508Data v0008Data)) (product q0509Data v0007Data)) (product q0510Data v0006Data)) (product q0511Data v0005Data)) (product q0512Data v0004Data)) (product q0513Data v0003Data)) (product q0514Data v0002Data)) (product q0515Data v0001Data)) (product q0516Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0013, q0014, q0015, q0016, q0111, q0113, q0114, q0115, q0116, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he



end SmallLevelTwentySixResultantCoefficientsMMM
end
end

}
