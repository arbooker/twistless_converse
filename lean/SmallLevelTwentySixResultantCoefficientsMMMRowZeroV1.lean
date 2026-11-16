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

compact_certificate theorem row0_x00 (y z w : ℂ) :
    q0000 y z w*r0000 y z w +
    q0400 y z w*v0000 y z w=d00 y z w := by
  have h : (merge (product q0000Data r0000Data) (product q0400Data v0000Data)) = d00Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0400, r0000, v0000, d00] using he


compact_certificate theorem row0_x01 (y z w : ℂ) :
    q0000 y z w*r0001 y z w +
    q0001 y z w*r0000 y z w +
    q0400 y z w*v0001 y z w +
    q0401 y z w*v0000 y z w=d01 y z w := by
  have h : (merge (merge (merge (product q0000Data r0001Data) (product q0001Data r0000Data)) (product q0400Data v0001Data)) (product q0401Data v0000Data)) = d01Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0400, q0401, r0000, r0001, v0000, v0001, d01] using he


compact_certificate theorem row0_x02 (y z w : ℂ) :
    q0000 y z w*r0002 y z w +
    q0001 y z w*r0001 y z w +
    q0002 y z w*r0000 y z w +
    q0400 y z w*v0002 y z w +
    q0401 y z w*v0001 y z w +
    q0402 y z w*v0000 y z w=d02 y z w := by
  have h : (merge (merge (merge (merge (merge (product q0000Data r0002Data) (product q0001Data r0001Data)) (product q0002Data r0000Data)) (product q0400Data v0002Data)) (product q0401Data v0001Data)) (product q0402Data v0000Data)) = d02Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0002, q0400, q0401, q0402, r0000, r0001, r0002, v0000, v0001, v0002, d02] using he


compact_certificate theorem row0_x03 (y z w : ℂ) :
    q0000 y z w*r0003 y z w +
    q0001 y z w*r0002 y z w +
    q0002 y z w*r0001 y z w +
    q0003 y z w*r0000 y z w +
    q0400 y z w*v0003 y z w +
    q0401 y z w*v0002 y z w +
    q0402 y z w*v0001 y z w +
    q0403 y z w*v0000 y z w=d03 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0003Data) (product q0001Data r0002Data)) (product q0002Data r0001Data)) (product q0003Data r0000Data)) (product q0400Data v0003Data)) (product q0401Data v0002Data)) (product q0402Data v0001Data)) (product q0403Data v0000Data)) = d03Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0002, q0003, q0400, q0401, q0402, q0403, r0000, r0001, r0002, r0003, v0000, v0001, v0002, v0003, d03] using he


compact_certificate theorem row0_x04 (y z w : ℂ) :
    q0001 y z w*r0003 y z w +
    q0002 y z w*r0002 y z w +
    q0003 y z w*r0001 y z w +
    q0004 y z w*r0000 y z w +
    q0400 y z w*v0004 y z w +
    q0401 y z w*v0003 y z w +
    q0402 y z w*v0002 y z w +
    q0403 y z w*v0001 y z w +
    q0404 y z w*v0000 y z w=d04 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (product q0001Data r0003Data) (product q0002Data r0002Data)) (product q0003Data r0001Data)) (product q0004Data r0000Data)) (product q0400Data v0004Data)) (product q0401Data v0003Data)) (product q0402Data v0002Data)) (product q0403Data v0001Data)) (product q0404Data v0000Data)) = d04Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0001, q0002, q0003, q0004, q0400, q0401, q0402, q0403, q0404, r0000, r0001, r0002, r0003, v0000, v0001, v0002, v0003, v0004, d04] using he


compact_certificate theorem row0_x05 (y z w : ℂ) :
    q0000 y z w*r0005 y z w +
    q0002 y z w*r0003 y z w +
    q0003 y z w*r0002 y z w +
    q0004 y z w*r0001 y z w +
    q0005 y z w*r0000 y z w +
    q0400 y z w*v0005 y z w +
    q0401 y z w*v0004 y z w +
    q0402 y z w*v0003 y z w +
    q0403 y z w*v0002 y z w +
    q0404 y z w*v0001 y z w +
    q0405 y z w*v0000 y z w=d05 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0005Data) (product q0002Data r0003Data)) (product q0003Data r0002Data)) (product q0004Data r0001Data)) (product q0005Data r0000Data)) (product q0400Data v0005Data)) (product q0401Data v0004Data)) (product q0402Data v0003Data)) (product q0403Data v0002Data)) (product q0404Data v0001Data)) (product q0405Data v0000Data)) = d05Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0002, q0003, q0004, q0005, q0400, q0401, q0402, q0403, q0404, q0405, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, d05] using he


compact_certificate theorem row0_x06 (y z w : ℂ) :
    q0001 y z w*r0005 y z w +
    q0003 y z w*r0003 y z w +
    q0004 y z w*r0002 y z w +
    q0005 y z w*r0001 y z w +
    q0006 y z w*r0000 y z w +
    q0400 y z w*v0006 y z w +
    q0401 y z w*v0005 y z w +
    q0402 y z w*v0004 y z w +
    q0403 y z w*v0003 y z w +
    q0404 y z w*v0002 y z w +
    q0405 y z w*v0001 y z w +
    q0406 y z w*v0000 y z w=d06 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0001Data r0005Data) (product q0003Data r0003Data)) (product q0004Data r0002Data)) (product q0005Data r0001Data)) (product q0006Data r0000Data)) (product q0400Data v0006Data)) (product q0401Data v0005Data)) (product q0402Data v0004Data)) (product q0403Data v0003Data)) (product q0404Data v0002Data)) (product q0405Data v0001Data)) (product q0406Data v0000Data)) = d06Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0001, q0003, q0004, q0005, q0006, q0400, q0401, q0402, q0403, q0404, q0405, q0406, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, d06] using he


compact_certificate theorem row0_x07 (y z w : ℂ) :
    q0002 y z w*r0005 y z w +
    q0004 y z w*r0003 y z w +
    q0005 y z w*r0002 y z w +
    q0006 y z w*r0001 y z w +
    q0007 y z w*r0000 y z w +
    q0400 y z w*v0007 y z w +
    q0401 y z w*v0006 y z w +
    q0402 y z w*v0005 y z w +
    q0403 y z w*v0004 y z w +
    q0404 y z w*v0003 y z w +
    q0405 y z w*v0002 y z w +
    q0406 y z w*v0001 y z w +
    q0407 y z w*v0000 y z w=d07 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0002Data r0005Data) (product q0004Data r0003Data)) (product q0005Data r0002Data)) (product q0006Data r0001Data)) (product q0007Data r0000Data)) (product q0400Data v0007Data)) (product q0401Data v0006Data)) (product q0402Data v0005Data)) (product q0403Data v0004Data)) (product q0404Data v0003Data)) (product q0405Data v0002Data)) (product q0406Data v0001Data)) (product q0407Data v0000Data)) = d07Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0002, q0004, q0005, q0006, q0007, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, d07] using he


compact_certificate theorem row0_x08 (y z w : ℂ) :
    q0003 y z w*r0005 y z w +
    q0005 y z w*r0003 y z w +
    q0006 y z w*r0002 y z w +
    q0007 y z w*r0001 y z w +
    q0008 y z w*r0000 y z w +
    q0400 y z w*v0008 y z w +
    q0401 y z w*v0007 y z w +
    q0402 y z w*v0006 y z w +
    q0403 y z w*v0005 y z w +
    q0404 y z w*v0004 y z w +
    q0405 y z w*v0003 y z w +
    q0406 y z w*v0002 y z w +
    q0407 y z w*v0001 y z w +
    q0408 y z w*v0000 y z w=d08 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0003Data r0005Data) (product q0005Data r0003Data)) (product q0006Data r0002Data)) (product q0007Data r0001Data)) (product q0008Data r0000Data)) (product q0400Data v0008Data)) (product q0401Data v0007Data)) (product q0402Data v0006Data)) (product q0403Data v0005Data)) (product q0404Data v0004Data)) (product q0405Data v0003Data)) (product q0406Data v0002Data)) (product q0407Data v0001Data)) (product q0408Data v0000Data)) = d08Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0003, q0005, q0006, q0007, q0008, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, d08] using he


compact_certificate theorem row0_x09 (y z w : ℂ) :
    q0004 y z w*r0005 y z w +
    q0006 y z w*r0003 y z w +
    q0007 y z w*r0002 y z w +
    q0008 y z w*r0001 y z w +
    q0009 y z w*r0000 y z w +
    q0400 y z w*v0009 y z w +
    q0401 y z w*v0008 y z w +
    q0402 y z w*v0007 y z w +
    q0403 y z w*v0006 y z w +
    q0404 y z w*v0005 y z w +
    q0405 y z w*v0004 y z w +
    q0406 y z w*v0003 y z w +
    q0407 y z w*v0002 y z w +
    q0408 y z w*v0001 y z w +
    q0409 y z w*v0000 y z w=d09 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0004Data r0005Data) (product q0006Data r0003Data)) (product q0007Data r0002Data)) (product q0008Data r0001Data)) (product q0009Data r0000Data)) (product q0400Data v0009Data)) (product q0401Data v0008Data)) (product q0402Data v0007Data)) (product q0403Data v0006Data)) (product q0404Data v0005Data)) (product q0405Data v0004Data)) (product q0406Data v0003Data)) (product q0407Data v0002Data)) (product q0408Data v0001Data)) (product q0409Data v0000Data)) = d09Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0004, q0006, q0007, q0008, q0009, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, d09] using he


compact_certificate theorem row0_x10 (y z w : ℂ) :
    q0005 y z w*r0005 y z w +
    q0007 y z w*r0003 y z w +
    q0008 y z w*r0002 y z w +
    q0009 y z w*r0001 y z w +
    q0010 y z w*r0000 y z w +
    q0400 y z w*v0010 y z w +
    q0401 y z w*v0009 y z w +
    q0402 y z w*v0008 y z w +
    q0403 y z w*v0007 y z w +
    q0404 y z w*v0006 y z w +
    q0405 y z w*v0005 y z w +
    q0406 y z w*v0004 y z w +
    q0407 y z w*v0003 y z w +
    q0408 y z w*v0002 y z w +
    q0409 y z w*v0001 y z w +
    q0410 y z w*v0000 y z w=d10 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0005Data r0005Data) (product q0007Data r0003Data)) (product q0008Data r0002Data)) (product q0009Data r0001Data)) (product q0010Data r0000Data)) (product q0400Data v0010Data)) (product q0401Data v0009Data)) (product q0402Data v0008Data)) (product q0403Data v0007Data)) (product q0404Data v0006Data)) (product q0405Data v0005Data)) (product q0406Data v0004Data)) (product q0407Data v0003Data)) (product q0408Data v0002Data)) (product q0409Data v0001Data)) (product q0410Data v0000Data)) = d10Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0005, q0007, q0008, q0009, q0010, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, d10] using he


compact_certificate theorem row0_x11 (y z w : ℂ) :
    q0006 y z w*r0005 y z w +
    q0008 y z w*r0003 y z w +
    q0009 y z w*r0002 y z w +
    q0010 y z w*r0001 y z w +
    q0011 y z w*r0000 y z w +
    q0400 y z w*v0011 y z w +
    q0401 y z w*v0010 y z w +
    q0402 y z w*v0009 y z w +
    q0403 y z w*v0008 y z w +
    q0404 y z w*v0007 y z w +
    q0405 y z w*v0006 y z w +
    q0406 y z w*v0005 y z w +
    q0407 y z w*v0004 y z w +
    q0408 y z w*v0003 y z w +
    q0409 y z w*v0002 y z w +
    q0410 y z w*v0001 y z w +
    q0411 y z w*v0000 y z w=d11 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0006Data r0005Data) (product q0008Data r0003Data)) (product q0009Data r0002Data)) (product q0010Data r0001Data)) (product q0011Data r0000Data)) (product q0400Data v0011Data)) (product q0401Data v0010Data)) (product q0402Data v0009Data)) (product q0403Data v0008Data)) (product q0404Data v0007Data)) (product q0405Data v0006Data)) (product q0406Data v0005Data)) (product q0407Data v0004Data)) (product q0408Data v0003Data)) (product q0409Data v0002Data)) (product q0410Data v0001Data)) (product q0411Data v0000Data)) = d11Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0006, q0008, q0009, q0010, q0011, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d11] using he


compact_certificate theorem row0_x12 (y z w : ℂ) :
    q0007 y z w*r0005 y z w +
    q0009 y z w*r0003 y z w +
    q0010 y z w*r0002 y z w +
    q0011 y z w*r0001 y z w +
    q0012 y z w*r0000 y z w +
    q0401 y z w*v0011 y z w +
    q0402 y z w*v0010 y z w +
    q0403 y z w*v0009 y z w +
    q0404 y z w*v0008 y z w +
    q0405 y z w*v0007 y z w +
    q0406 y z w*v0006 y z w +
    q0407 y z w*v0005 y z w +
    q0408 y z w*v0004 y z w +
    q0409 y z w*v0003 y z w +
    q0410 y z w*v0002 y z w +
    q0411 y z w*v0001 y z w +
    q0412 y z w*v0000 y z w=d12 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0007Data r0005Data) (product q0009Data r0003Data)) (product q0010Data r0002Data)) (product q0011Data r0001Data)) (product q0012Data r0000Data)) (product q0401Data v0011Data)) (product q0402Data v0010Data)) (product q0403Data v0009Data)) (product q0404Data v0008Data)) (product q0405Data v0007Data)) (product q0406Data v0006Data)) (product q0407Data v0005Data)) (product q0408Data v0004Data)) (product q0409Data v0003Data)) (product q0410Data v0002Data)) (product q0411Data v0001Data)) (product q0412Data v0000Data)) = d12Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0007, q0009, q0010, q0011, q0012, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d12] using he


compact_certificate theorem row0_x13 (y z w : ℂ) :
    q0008 y z w*r0005 y z w +
    q0010 y z w*r0003 y z w +
    q0011 y z w*r0002 y z w +
    q0012 y z w*r0001 y z w +
    q0013 y z w*r0000 y z w +
    q0402 y z w*v0011 y z w +
    q0403 y z w*v0010 y z w +
    q0404 y z w*v0009 y z w +
    q0405 y z w*v0008 y z w +
    q0406 y z w*v0007 y z w +
    q0407 y z w*v0006 y z w +
    q0408 y z w*v0005 y z w +
    q0409 y z w*v0004 y z w +
    q0410 y z w*v0003 y z w +
    q0411 y z w*v0002 y z w +
    q0412 y z w*v0001 y z w +
    q0413 y z w*v0000 y z w=d13 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0008Data r0005Data) (product q0010Data r0003Data)) (product q0011Data r0002Data)) (product q0012Data r0001Data)) (product q0013Data r0000Data)) (product q0402Data v0011Data)) (product q0403Data v0010Data)) (product q0404Data v0009Data)) (product q0405Data v0008Data)) (product q0406Data v0007Data)) (product q0407Data v0006Data)) (product q0408Data v0005Data)) (product q0409Data v0004Data)) (product q0410Data v0003Data)) (product q0411Data v0002Data)) (product q0412Data v0001Data)) (product q0413Data v0000Data)) = d13Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0008, q0010, q0011, q0012, q0013, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d13] using he


compact_certificate theorem row0_x14 (y z w : ℂ) :
    q0009 y z w*r0005 y z w +
    q0011 y z w*r0003 y z w +
    q0012 y z w*r0002 y z w +
    q0013 y z w*r0001 y z w +
    q0014 y z w*r0000 y z w +
    q0403 y z w*v0011 y z w +
    q0404 y z w*v0010 y z w +
    q0405 y z w*v0009 y z w +
    q0406 y z w*v0008 y z w +
    q0407 y z w*v0007 y z w +
    q0408 y z w*v0006 y z w +
    q0409 y z w*v0005 y z w +
    q0410 y z w*v0004 y z w +
    q0411 y z w*v0003 y z w +
    q0412 y z w*v0002 y z w +
    q0413 y z w*v0001 y z w +
    q0414 y z w*v0000 y z w=d14 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0009Data r0005Data) (product q0011Data r0003Data)) (product q0012Data r0002Data)) (product q0013Data r0001Data)) (product q0014Data r0000Data)) (product q0403Data v0011Data)) (product q0404Data v0010Data)) (product q0405Data v0009Data)) (product q0406Data v0008Data)) (product q0407Data v0007Data)) (product q0408Data v0006Data)) (product q0409Data v0005Data)) (product q0410Data v0004Data)) (product q0411Data v0003Data)) (product q0412Data v0002Data)) (product q0413Data v0001Data)) (product q0414Data v0000Data)) = d14Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0009, q0011, q0012, q0013, q0014, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d14] using he



compact_certificate theorem row0_x15 (y z w : ℂ) :
    q0010 y z w*r0005 y z w +
    q0012 y z w*r0003 y z w +
    q0013 y z w*r0002 y z w +
    q0014 y z w*r0001 y z w +
    q0015 y z w*r0000 y z w +
    q0404 y z w*v0011 y z w +
    q0405 y z w*v0010 y z w +
    q0406 y z w*v0009 y z w +
    q0407 y z w*v0008 y z w +
    q0408 y z w*v0007 y z w +
    q0409 y z w*v0006 y z w +
    q0410 y z w*v0005 y z w +
    q0411 y z w*v0004 y z w +
    q0412 y z w*v0003 y z w +
    q0413 y z w*v0002 y z w +
    q0414 y z w*v0001 y z w +
    q0415 y z w*v0000 y z w=d15 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0010Data r0005Data) (product q0012Data r0003Data)) (product q0013Data r0002Data)) (product q0014Data r0001Data)) (product q0015Data r0000Data)) (product q0404Data v0011Data)) (product q0405Data v0010Data)) (product q0406Data v0009Data)) (product q0407Data v0008Data)) (product q0408Data v0007Data)) (product q0409Data v0006Data)) (product q0410Data v0005Data)) (product q0411Data v0004Data)) (product q0412Data v0003Data)) (product q0413Data v0002Data)) (product q0414Data v0001Data)) (product q0415Data v0000Data)) = d15Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0010, q0012, q0013, q0014, q0015, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d15] using he


compact_certificate theorem row0_x16 (y z w : ℂ) :
    q0011 y z w*r0005 y z w +
    q0013 y z w*r0003 y z w +
    q0014 y z w*r0002 y z w +
    q0015 y z w*r0001 y z w +
    q0016 y z w*r0000 y z w +
    q0405 y z w*v0011 y z w +
    q0406 y z w*v0010 y z w +
    q0407 y z w*v0009 y z w +
    q0408 y z w*v0008 y z w +
    q0409 y z w*v0007 y z w +
    q0410 y z w*v0006 y z w +
    q0411 y z w*v0005 y z w +
    q0412 y z w*v0004 y z w +
    q0413 y z w*v0003 y z w +
    q0414 y z w*v0002 y z w +
    q0415 y z w*v0001 y z w +
    q0416 y z w*v0000 y z w=d16 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0011Data r0005Data) (product q0013Data r0003Data)) (product q0014Data r0002Data)) (product q0015Data r0001Data)) (product q0016Data r0000Data)) (product q0405Data v0011Data)) (product q0406Data v0010Data)) (product q0407Data v0009Data)) (product q0408Data v0008Data)) (product q0409Data v0007Data)) (product q0410Data v0006Data)) (product q0411Data v0005Data)) (product q0412Data v0004Data)) (product q0413Data v0003Data)) (product q0414Data v0002Data)) (product q0415Data v0001Data)) (product q0416Data v0000Data)) = d16Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0011, q0013, q0014, q0015, q0016, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d16] using he


compact_certificate theorem row0_x17 (y z w : ℂ) :
    q0012 y z w*r0005 y z w +
    q0014 y z w*r0003 y z w +
    q0015 y z w*r0002 y z w +
    q0016 y z w*r0001 y z w +
    q0017 y z w*r0000 y z w +
    q0406 y z w*v0011 y z w +
    q0407 y z w*v0010 y z w +
    q0408 y z w*v0009 y z w +
    q0409 y z w*v0008 y z w +
    q0410 y z w*v0007 y z w +
    q0411 y z w*v0006 y z w +
    q0412 y z w*v0005 y z w +
    q0413 y z w*v0004 y z w +
    q0414 y z w*v0003 y z w +
    q0415 y z w*v0002 y z w +
    q0416 y z w*v0001 y z w +
    q0417 y z w*v0000 y z w=d17 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0012Data r0005Data) (product q0014Data r0003Data)) (product q0015Data r0002Data)) (product q0016Data r0001Data)) (product q0017Data r0000Data)) (product q0406Data v0011Data)) (product q0407Data v0010Data)) (product q0408Data v0009Data)) (product q0409Data v0008Data)) (product q0410Data v0007Data)) (product q0411Data v0006Data)) (product q0412Data v0005Data)) (product q0413Data v0004Data)) (product q0414Data v0003Data)) (product q0415Data v0002Data)) (product q0416Data v0001Data)) (product q0417Data v0000Data)) = d17Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0012, q0014, q0015, q0016, q0017, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d17] using he


compact_certificate theorem row0_x18 (y z w : ℂ) :
    q0013 y z w*r0005 y z w +
    q0015 y z w*r0003 y z w +
    q0016 y z w*r0002 y z w +
    q0017 y z w*r0001 y z w +
    q0018 y z w*r0000 y z w +
    q0407 y z w*v0011 y z w +
    q0408 y z w*v0010 y z w +
    q0409 y z w*v0009 y z w +
    q0410 y z w*v0008 y z w +
    q0411 y z w*v0007 y z w +
    q0412 y z w*v0006 y z w +
    q0413 y z w*v0005 y z w +
    q0414 y z w*v0004 y z w +
    q0415 y z w*v0003 y z w +
    q0416 y z w*v0002 y z w +
    q0417 y z w*v0001 y z w +
    q0418 y z w*v0000 y z w=d18 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0013Data r0005Data) (product q0015Data r0003Data)) (product q0016Data r0002Data)) (product q0017Data r0001Data)) (product q0018Data r0000Data)) (product q0407Data v0011Data)) (product q0408Data v0010Data)) (product q0409Data v0009Data)) (product q0410Data v0008Data)) (product q0411Data v0007Data)) (product q0412Data v0006Data)) (product q0413Data v0005Data)) (product q0414Data v0004Data)) (product q0415Data v0003Data)) (product q0416Data v0002Data)) (product q0417Data v0001Data)) (product q0418Data v0000Data)) = d18Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0013, q0015, q0016, q0017, q0018, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d18] using he


compact_certificate theorem row0_x19 (y z w : ℂ) :
    q0014 y z w*r0005 y z w +
    q0016 y z w*r0003 y z w +
    q0017 y z w*r0002 y z w +
    q0018 y z w*r0001 y z w +
    q0019 y z w*r0000 y z w +
    q0408 y z w*v0011 y z w +
    q0409 y z w*v0010 y z w +
    q0410 y z w*v0009 y z w +
    q0411 y z w*v0008 y z w +
    q0412 y z w*v0007 y z w +
    q0413 y z w*v0006 y z w +
    q0414 y z w*v0005 y z w +
    q0415 y z w*v0004 y z w +
    q0416 y z w*v0003 y z w +
    q0417 y z w*v0002 y z w +
    q0418 y z w*v0001 y z w +
    q0419 y z w*v0000 y z w=d19 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0014Data r0005Data) (product q0016Data r0003Data)) (product q0017Data r0002Data)) (product q0018Data r0001Data)) (product q0019Data r0000Data)) (product q0408Data v0011Data)) (product q0409Data v0010Data)) (product q0410Data v0009Data)) (product q0411Data v0008Data)) (product q0412Data v0007Data)) (product q0413Data v0006Data)) (product q0414Data v0005Data)) (product q0415Data v0004Data)) (product q0416Data v0003Data)) (product q0417Data v0002Data)) (product q0418Data v0001Data)) (product q0419Data v0000Data)) = d19Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0014, q0016, q0017, q0018, q0019, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d19] using he


compact_certificate theorem row0_x20 (y z w : ℂ) :
    q0015 y z w*r0005 y z w +
    q0017 y z w*r0003 y z w +
    q0018 y z w*r0002 y z w +
    q0019 y z w*r0001 y z w +
    q0020 y z w*r0000 y z w +
    q0409 y z w*v0011 y z w +
    q0410 y z w*v0010 y z w +
    q0411 y z w*v0009 y z w +
    q0412 y z w*v0008 y z w +
    q0413 y z w*v0007 y z w +
    q0414 y z w*v0006 y z w +
    q0415 y z w*v0005 y z w +
    q0416 y z w*v0004 y z w +
    q0417 y z w*v0003 y z w +
    q0418 y z w*v0002 y z w +
    q0419 y z w*v0001 y z w +
    q0420 y z w*v0000 y z w=d20 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0015Data r0005Data) (product q0017Data r0003Data)) (product q0018Data r0002Data)) (product q0019Data r0001Data)) (product q0020Data r0000Data)) (product q0409Data v0011Data)) (product q0410Data v0010Data)) (product q0411Data v0009Data)) (product q0412Data v0008Data)) (product q0413Data v0007Data)) (product q0414Data v0006Data)) (product q0415Data v0005Data)) (product q0416Data v0004Data)) (product q0417Data v0003Data)) (product q0418Data v0002Data)) (product q0419Data v0001Data)) (product q0420Data v0000Data)) = d20Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0015, q0017, q0018, q0019, q0020, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d20] using he


compact_certificate theorem row0_x21 (y z w : ℂ) :
    q0016 y z w*r0005 y z w +
    q0018 y z w*r0003 y z w +
    q0019 y z w*r0002 y z w +
    q0020 y z w*r0001 y z w +
    q0021 y z w*r0000 y z w +
    q0410 y z w*v0011 y z w +
    q0411 y z w*v0010 y z w +
    q0412 y z w*v0009 y z w +
    q0413 y z w*v0008 y z w +
    q0414 y z w*v0007 y z w +
    q0415 y z w*v0006 y z w +
    q0416 y z w*v0005 y z w +
    q0417 y z w*v0004 y z w +
    q0418 y z w*v0003 y z w +
    q0419 y z w*v0002 y z w +
    q0420 y z w*v0001 y z w +
    q0421 y z w*v0000 y z w=d21 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0016Data r0005Data) (product q0018Data r0003Data)) (product q0019Data r0002Data)) (product q0020Data r0001Data)) (product q0021Data r0000Data)) (product q0410Data v0011Data)) (product q0411Data v0010Data)) (product q0412Data v0009Data)) (product q0413Data v0008Data)) (product q0414Data v0007Data)) (product q0415Data v0006Data)) (product q0416Data v0005Data)) (product q0417Data v0004Data)) (product q0418Data v0003Data)) (product q0419Data v0002Data)) (product q0420Data v0001Data)) (product q0421Data v0000Data)) = d21Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0016, q0018, q0019, q0020, q0021, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d21] using he


compact_certificate theorem row0_x22 (y z w : ℂ) :
    q0017 y z w*r0005 y z w +
    q0019 y z w*r0003 y z w +
    q0020 y z w*r0002 y z w +
    q0021 y z w*r0001 y z w +
    q0022 y z w*r0000 y z w +
    q0411 y z w*v0011 y z w +
    q0412 y z w*v0010 y z w +
    q0413 y z w*v0009 y z w +
    q0414 y z w*v0008 y z w +
    q0415 y z w*v0007 y z w +
    q0416 y z w*v0006 y z w +
    q0417 y z w*v0005 y z w +
    q0418 y z w*v0004 y z w +
    q0419 y z w*v0003 y z w +
    q0420 y z w*v0002 y z w +
    q0421 y z w*v0001 y z w +
    q0422 y z w*v0000 y z w=d22 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0017Data r0005Data) (product q0019Data r0003Data)) (product q0020Data r0002Data)) (product q0021Data r0001Data)) (product q0022Data r0000Data)) (product q0411Data v0011Data)) (product q0412Data v0010Data)) (product q0413Data v0009Data)) (product q0414Data v0008Data)) (product q0415Data v0007Data)) (product q0416Data v0006Data)) (product q0417Data v0005Data)) (product q0418Data v0004Data)) (product q0419Data v0003Data)) (product q0420Data v0002Data)) (product q0421Data v0001Data)) (product q0422Data v0000Data)) = d22Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0017, q0019, q0020, q0021, q0022, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d22] using he


compact_certificate theorem row0_x23 (y z w : ℂ) :
    q0018 y z w*r0005 y z w +
    q0020 y z w*r0003 y z w +
    q0021 y z w*r0002 y z w +
    q0022 y z w*r0001 y z w +
    q0023 y z w*r0000 y z w +
    q0412 y z w*v0011 y z w +
    q0413 y z w*v0010 y z w +
    q0414 y z w*v0009 y z w +
    q0415 y z w*v0008 y z w +
    q0416 y z w*v0007 y z w +
    q0417 y z w*v0006 y z w +
    q0418 y z w*v0005 y z w +
    q0419 y z w*v0004 y z w +
    q0420 y z w*v0003 y z w +
    q0421 y z w*v0002 y z w +
    q0422 y z w*v0001 y z w +
    q0423 y z w*v0000 y z w=d23 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0018Data r0005Data) (product q0020Data r0003Data)) (product q0021Data r0002Data)) (product q0022Data r0001Data)) (product q0023Data r0000Data)) (product q0412Data v0011Data)) (product q0413Data v0010Data)) (product q0414Data v0009Data)) (product q0415Data v0008Data)) (product q0416Data v0007Data)) (product q0417Data v0006Data)) (product q0418Data v0005Data)) (product q0419Data v0004Data)) (product q0420Data v0003Data)) (product q0421Data v0002Data)) (product q0422Data v0001Data)) (product q0423Data v0000Data)) = d23Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0018, q0020, q0021, q0022, q0023, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d23] using he


compact_certificate theorem row0_x24 (y z w : ℂ) :
    q0019 y z w*r0005 y z w +
    q0021 y z w*r0003 y z w +
    q0022 y z w*r0002 y z w +
    q0023 y z w*r0001 y z w +
    q0024 y z w*r0000 y z w +
    q0413 y z w*v0011 y z w +
    q0414 y z w*v0010 y z w +
    q0415 y z w*v0009 y z w +
    q0416 y z w*v0008 y z w +
    q0417 y z w*v0007 y z w +
    q0418 y z w*v0006 y z w +
    q0419 y z w*v0005 y z w +
    q0420 y z w*v0004 y z w +
    q0421 y z w*v0003 y z w +
    q0422 y z w*v0002 y z w +
    q0423 y z w*v0001 y z w +
    q0424 y z w*v0000 y z w=d24 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0019Data r0005Data) (product q0021Data r0003Data)) (product q0022Data r0002Data)) (product q0023Data r0001Data)) (product q0024Data r0000Data)) (product q0413Data v0011Data)) (product q0414Data v0010Data)) (product q0415Data v0009Data)) (product q0416Data v0008Data)) (product q0417Data v0007Data)) (product q0418Data v0006Data)) (product q0419Data v0005Data)) (product q0420Data v0004Data)) (product q0421Data v0003Data)) (product q0422Data v0002Data)) (product q0423Data v0001Data)) (product q0424Data v0000Data)) = d24Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0019, q0021, q0022, q0023, q0024, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, r0000, r0001, r0002, r0003, r0005, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d24] using he


compact_certificate theorem row0_x25 (y z w : ℂ) :
    q0020 y z w*r0005 y z w +
    q0022 y z w*r0003 y z w +
    q0023 y z w*r0002 y z w +
    q0024 y z w*r0001 y z w +
    q0025 y z w*r0000 y z w +
    q0414 y z w*v0011 y z w +
    q0415 y z w*v0010 y z w +
    q0416 y z w*v0009 y z w +
    q0417 y z w*v0008 y z w +
    q0418 y z w*v0007 y z w +
    q0419 y z w*v0006 y z w +
    q0420 y z w*v0005 y z w +
    q0421 y z w*v0004 y z w +
    q0422 y z w*v0003 y z w +
    q0423 y z w*v0002 y z w +
    q0424 y z w*v0001 y z w=d25 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0020Data r0005Data) (product q0022Data r0003Data)) (product q0023Data r0002Data)) (product q0024Data r0001Data)) (product q0025Data r0000Data)) (product q0414Data v0011Data)) (product q0415Data v0010Data)) (product q0416Data v0009Data)) (product q0417Data v0008Data)) (product q0418Data v0007Data)) (product q0419Data v0006Data)) (product q0420Data v0005Data)) (product q0421Data v0004Data)) (product q0422Data v0003Data)) (product q0423Data v0002Data)) (product q0424Data v0001Data)) = d25Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0020, q0022, q0023, q0024, q0025, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, r0000, r0001, r0002, r0003, r0005, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d25] using he


compact_certificate theorem row0_x26 (y z w : ℂ) :
    q0021 y z w*r0005 y z w +
    q0023 y z w*r0003 y z w +
    q0024 y z w*r0002 y z w +
    q0025 y z w*r0001 y z w +
    q0026 y z w*r0000 y z w +
    q0415 y z w*v0011 y z w +
    q0416 y z w*v0010 y z w +
    q0417 y z w*v0009 y z w +
    q0418 y z w*v0008 y z w +
    q0419 y z w*v0007 y z w +
    q0420 y z w*v0006 y z w +
    q0421 y z w*v0005 y z w +
    q0422 y z w*v0004 y z w +
    q0423 y z w*v0003 y z w +
    q0424 y z w*v0002 y z w=d26 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0021Data r0005Data) (product q0023Data r0003Data)) (product q0024Data r0002Data)) (product q0025Data r0001Data)) (product q0026Data r0000Data)) (product q0415Data v0011Data)) (product q0416Data v0010Data)) (product q0417Data v0009Data)) (product q0418Data v0008Data)) (product q0419Data v0007Data)) (product q0420Data v0006Data)) (product q0421Data v0005Data)) (product q0422Data v0004Data)) (product q0423Data v0003Data)) (product q0424Data v0002Data)) = d26Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0021, q0023, q0024, q0025, q0026, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, r0000, r0001, r0002, r0003, r0005, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d26] using he


compact_certificate theorem row0_x27 (y z w : ℂ) :
    q0022 y z w*r0005 y z w +
    q0024 y z w*r0003 y z w +
    q0025 y z w*r0002 y z w +
    q0026 y z w*r0001 y z w +
    q0027 y z w*r0000 y z w +
    q0416 y z w*v0011 y z w +
    q0417 y z w*v0010 y z w +
    q0418 y z w*v0009 y z w +
    q0419 y z w*v0008 y z w +
    q0420 y z w*v0007 y z w +
    q0421 y z w*v0006 y z w +
    q0422 y z w*v0005 y z w +
    q0423 y z w*v0004 y z w +
    q0424 y z w*v0003 y z w=d27 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0022Data r0005Data) (product q0024Data r0003Data)) (product q0025Data r0002Data)) (product q0026Data r0001Data)) (product q0027Data r0000Data)) (product q0416Data v0011Data)) (product q0417Data v0010Data)) (product q0418Data v0009Data)) (product q0419Data v0008Data)) (product q0420Data v0007Data)) (product q0421Data v0006Data)) (product q0422Data v0005Data)) (product q0423Data v0004Data)) (product q0424Data v0003Data)) = d27Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0022, q0024, q0025, q0026, q0027, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, r0000, r0001, r0002, r0003, r0005, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d27] using he


compact_certificate theorem row0_x28 (y z w : ℂ) :
    q0023 y z w*r0005 y z w +
    q0025 y z w*r0003 y z w +
    q0026 y z w*r0002 y z w +
    q0027 y z w*r0001 y z w +
    q0028 y z w*r0000 y z w +
    q0417 y z w*v0011 y z w +
    q0418 y z w*v0010 y z w +
    q0419 y z w*v0009 y z w +
    q0420 y z w*v0008 y z w +
    q0421 y z w*v0007 y z w +
    q0422 y z w*v0006 y z w +
    q0423 y z w*v0005 y z w +
    q0424 y z w*v0004 y z w=d28 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0023Data r0005Data) (product q0025Data r0003Data)) (product q0026Data r0002Data)) (product q0027Data r0001Data)) (product q0028Data r0000Data)) (product q0417Data v0011Data)) (product q0418Data v0010Data)) (product q0419Data v0009Data)) (product q0420Data v0008Data)) (product q0421Data v0007Data)) (product q0422Data v0006Data)) (product q0423Data v0005Data)) (product q0424Data v0004Data)) = d28Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0023, q0025, q0026, q0027, q0028, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, r0000, r0001, r0002, r0003, r0005, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d28] using he


compact_certificate theorem row0_x29 (y z w : ℂ) :
    q0024 y z w*r0005 y z w +
    q0026 y z w*r0003 y z w +
    q0027 y z w*r0002 y z w +
    q0028 y z w*r0001 y z w +
    q0029 y z w*r0000 y z w +
    q0418 y z w*v0011 y z w +
    q0419 y z w*v0010 y z w +
    q0420 y z w*v0009 y z w +
    q0421 y z w*v0008 y z w +
    q0422 y z w*v0007 y z w +
    q0423 y z w*v0006 y z w +
    q0424 y z w*v0005 y z w=d29 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0024Data r0005Data) (product q0026Data r0003Data)) (product q0027Data r0002Data)) (product q0028Data r0001Data)) (product q0029Data r0000Data)) (product q0418Data v0011Data)) (product q0419Data v0010Data)) (product q0420Data v0009Data)) (product q0421Data v0008Data)) (product q0422Data v0007Data)) (product q0423Data v0006Data)) (product q0424Data v0005Data)) = d29Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0024, q0026, q0027, q0028, q0029, q0418, q0419, q0420, q0421, q0422, q0423, q0424, r0000, r0001, r0002, r0003, r0005, v0005, v0006, v0007, v0008, v0009, v0010, v0011, d29] using he


compact_certificate theorem row0_x30 (y z w : ℂ) :
    q0025 y z w*r0005 y z w +
    q0027 y z w*r0003 y z w +
    q0028 y z w*r0002 y z w +
    q0029 y z w*r0001 y z w +
    q0030 y z w*r0000 y z w +
    q0419 y z w*v0011 y z w +
    q0420 y z w*v0010 y z w +
    q0421 y z w*v0009 y z w +
    q0422 y z w*v0008 y z w +
    q0423 y z w*v0007 y z w +
    q0424 y z w*v0006 y z w=d30 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0025Data r0005Data) (product q0027Data r0003Data)) (product q0028Data r0002Data)) (product q0029Data r0001Data)) (product q0030Data r0000Data)) (product q0419Data v0011Data)) (product q0420Data v0010Data)) (product q0421Data v0009Data)) (product q0422Data v0008Data)) (product q0423Data v0007Data)) (product q0424Data v0006Data)) = d30Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0025, q0027, q0028, q0029, q0030, q0419, q0420, q0421, q0422, q0423, q0424, r0000, r0001, r0002, r0003, r0005, v0006, v0007, v0008, v0009, v0010, v0011, d30] using he


compact_certificate theorem row0_x31 (y z w : ℂ) :
    q0026 y z w*r0005 y z w +
    q0028 y z w*r0003 y z w +
    q0029 y z w*r0002 y z w +
    q0030 y z w*r0001 y z w +
    q0420 y z w*v0011 y z w +
    q0421 y z w*v0010 y z w +
    q0422 y z w*v0009 y z w +
    q0423 y z w*v0008 y z w +
    q0424 y z w*v0007 y z w=d31 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (product q0026Data r0005Data) (product q0028Data r0003Data)) (product q0029Data r0002Data)) (product q0030Data r0001Data)) (product q0420Data v0011Data)) (product q0421Data v0010Data)) (product q0422Data v0009Data)) (product q0423Data v0008Data)) (product q0424Data v0007Data)) = d31Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0026, q0028, q0029, q0030, q0420, q0421, q0422, q0423, q0424, r0001, r0002, r0003, r0005, v0007, v0008, v0009, v0010, v0011, d31] using he


compact_certificate theorem row0_x32 (y z w : ℂ) :
    q0027 y z w*r0005 y z w +
    q0029 y z w*r0003 y z w +
    q0030 y z w*r0002 y z w +
    q0421 y z w*v0011 y z w +
    q0422 y z w*v0010 y z w +
    q0423 y z w*v0009 y z w +
    q0424 y z w*v0008 y z w=d32 y z w := by
  have h : (merge (merge (merge (merge (merge (merge (product q0027Data r0005Data) (product q0029Data r0003Data)) (product q0030Data r0002Data)) (product q0421Data v0011Data)) (product q0422Data v0010Data)) (product q0423Data v0009Data)) (product q0424Data v0008Data)) = d32Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0027, q0029, q0030, q0421, q0422, q0423, q0424, r0002, r0003, r0005, v0008, v0009, v0010, v0011, d32] using he


compact_certificate theorem row0_x33 (y z w : ℂ) :
    q0028 y z w*r0005 y z w +
    q0030 y z w*r0003 y z w +
    q0422 y z w*v0011 y z w +
    q0423 y z w*v0010 y z w +
    q0424 y z w*v0009 y z w=d33 y z w := by
  have h : (merge (merge (merge (merge (product q0028Data r0005Data) (product q0030Data r0003Data)) (product q0422Data v0011Data)) (product q0423Data v0010Data)) (product q0424Data v0009Data)) = d33Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0028, q0030, q0422, q0423, q0424, r0003, r0005, v0009, v0010, v0011, d33] using he


compact_certificate theorem row0_x34 (y z w : ℂ) :
    q0029 y z w*r0005 y z w +
    q0423 y z w*v0011 y z w +
    q0424 y z w*v0010 y z w=d34 y z w := by
  have h : (merge (merge (product q0029Data r0005Data) (product q0423Data v0011Data)) (product q0424Data v0010Data)) = d34Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0029, q0423, q0424, r0005, v0010, v0011, d34] using he


compact_certificate theorem row0_x35 (y z w : ℂ) :
    q0030 y z w*r0005 y z w +
    q0424 y z w*v0011 y z w=d35 y z w := by
  have h : (merge (product q0030Data r0005Data) (product q0424Data v0011Data)) = d35Data := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0030, q0424, r0005, v0011, d35] using he



end SmallLevelTwentySixResultantCoefficientsMMM
end
end

}
