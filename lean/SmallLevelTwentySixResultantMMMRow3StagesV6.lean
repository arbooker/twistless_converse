module

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelCubicQuarticSylvesterV1
public import SmallLevelTwentySixResultantBatchedMMMZeroGroupedTheoryV4
public import SmallLevelTwentySixResultantCoefficientsMMMTheoryV4
public meta import QuantitativeArithmeticCompactCommandsV1

public meta import QuantitativeArithmeticSparseCertificateComputeV5
public meta import SmallLevelCertificateBatchCommandV1
/-! Consolidated chapter: SmallLevelTwentySixResultantBatchedMMM. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixResultantBatchedMMMRowIndexXBundleSeriesV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option Elab.async false
-- Compact certificates omit editor information used by these tactic linters.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantBatchedMMM
open SmallLevelTwentySixResultantCoefficientsMMM
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open Polynomial SmallLevelPolynomialCoefficientAssembly
open scoped Classical

/-! Whole coefficient identities are checked by sparse integer arithmetic.
The general evaluation lemma transports them to arbitrary complex arguments;
no stored intermediate polynomial or symbolic partial-product proof is needed. -/

certificate_batch {
compact_certificate theorem row3_x00 (y z w : ℂ) :
    q0000 y z w*r0300 y z w +
    q0100 y z w*r0200 y z w +
    q0500 y z w*v0200 y z w +
    q0600 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (product q0000Data r0300Data) (product q0100Data r0200Data)) (product q0500Data v0200Data)) (product q0600Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0100, q0500, q0600, r0200, r0300, v0100, v0200] using he

#print axioms row3_x00

compact_certificate theorem row3_x01 (y z w : ℂ) :
    q0000 y z w*r0301 y z w +
    q0001 y z w*r0300 y z w +
    q0100 y z w*r0201 y z w +
    q0101 y z w*r0200 y z w +
    q0201 y z w*r0100 y z w +
    q0301 y z w*r0000 y z w +
    q0400 y z w*v0301 y z w +
    q0500 y z w*v0201 y z w +
    q0501 y z w*v0200 y z w +
    q0600 y z w*v0101 y z w +
    q0601 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0301Data) (product q0001Data r0300Data)) (product q0100Data r0201Data)) (product q0101Data r0200Data)) (product q0201Data r0100Data)) (product q0301Data r0000Data)) (product q0400Data v0301Data)) (product q0500Data v0201Data)) (product q0501Data v0200Data)) (product q0600Data v0101Data)) (product q0601Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0100, q0101, q0201, q0301, q0400, q0500, q0501, q0600, q0601, r0000, r0100, r0200, r0201, r0300, r0301, v0100, v0101, v0200, v0201, v0301] using he

#print axioms row3_x01

compact_certificate theorem row3_x02 (y z w : ℂ) :
    q0001 y z w*r0301 y z w +
    q0002 y z w*r0300 y z w +
    q0100 y z w*r0202 y z w +
    q0101 y z w*r0201 y z w +
    q0102 y z w*r0200 y z w +
    q0201 y z w*r0101 y z w +
    q0202 y z w*r0100 y z w +
    q0301 y z w*r0001 y z w +
    q0302 y z w*r0000 y z w +
    q0400 y z w*v0302 y z w +
    q0401 y z w*v0301 y z w +
    q0500 y z w*v0202 y z w +
    q0501 y z w*v0201 y z w +
    q0502 y z w*v0200 y z w +
    q0600 y z w*v0102 y z w +
    q0601 y z w*v0101 y z w +
    q0602 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0001Data r0301Data) (product q0002Data r0300Data)) (product q0100Data r0202Data)) (product q0101Data r0201Data)) (product q0102Data r0200Data)) (product q0201Data r0101Data)) (product q0202Data r0100Data)) (product q0301Data r0001Data)) (product q0302Data r0000Data)) (product q0400Data v0302Data)) (product q0401Data v0301Data)) (product q0500Data v0202Data)) (product q0501Data v0201Data)) (product q0502Data v0200Data)) (product q0600Data v0102Data)) (product q0601Data v0101Data)) (product q0602Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0001, q0002, q0100, q0101, q0102, q0201, q0202, q0301, q0302, q0400, q0401, q0500, q0501, q0502, q0600, q0601, q0602, r0000, r0001, r0100, r0101, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0200, v0201, v0202, v0301, v0302] using he

#print axioms row3_x02

compact_certificate theorem row3_x03 (y z w : ℂ) :
    q0002 y z w*r0301 y z w +
    q0003 y z w*r0300 y z w +
    q0101 y z w*r0202 y z w +
    q0102 y z w*r0201 y z w +
    q0103 y z w*r0200 y z w +
    q0201 y z w*r0102 y z w +
    q0202 y z w*r0101 y z w +
    q0203 y z w*r0100 y z w +
    q0301 y z w*r0002 y z w +
    q0302 y z w*r0001 y z w +
    q0303 y z w*r0000 y z w +
    q0400 y z w*v0303 y z w +
    q0401 y z w*v0302 y z w +
    q0402 y z w*v0301 y z w +
    q0500 y z w*v0203 y z w +
    q0501 y z w*v0202 y z w +
    q0502 y z w*v0201 y z w +
    q0503 y z w*v0200 y z w +
    q0600 y z w*v0103 y z w +
    q0601 y z w*v0102 y z w +
    q0602 y z w*v0101 y z w +
    q0603 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0002Data r0301Data) (product q0003Data r0300Data)) (product q0101Data r0202Data)) (product q0102Data r0201Data)) (product q0103Data r0200Data)) (product q0201Data r0102Data)) (product q0202Data r0101Data)) (product q0203Data r0100Data)) (product q0301Data r0002Data)) (product q0302Data r0001Data)) (product q0303Data r0000Data)) (product q0400Data v0303Data)) (product q0401Data v0302Data)) (product q0402Data v0301Data)) (product q0500Data v0203Data)) (product q0501Data v0202Data)) (product q0502Data v0201Data)) (product q0503Data v0200Data)) (product q0600Data v0103Data)) (product q0601Data v0102Data)) (product q0602Data v0101Data)) (product q0603Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0002, q0003, q0101, q0102, q0103, q0201, q0202, q0203, q0301, q0302, q0303, q0400, q0401, q0402, q0500, q0501, q0502, q0503, q0600, q0601, q0602, q0603, r0000, r0001, r0002, r0100, r0101, r0102, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0200, v0201, v0202, v0203, v0301, v0302, v0303] using he

#print axioms row3_x03

compact_certificate theorem row3_x04 (y z w : ℂ) :
    q0003 y z w*r0301 y z w +
    q0004 y z w*r0300 y z w +
    q0102 y z w*r0202 y z w +
    q0103 y z w*r0201 y z w +
    q0104 y z w*r0200 y z w +
    q0201 y z w*r0103 y z w +
    q0202 y z w*r0102 y z w +
    q0203 y z w*r0101 y z w +
    q0204 y z w*r0100 y z w +
    q0301 y z w*r0003 y z w +
    q0302 y z w*r0002 y z w +
    q0303 y z w*r0001 y z w +
    q0304 y z w*r0000 y z w +
    q0400 y z w*v0304 y z w +
    q0401 y z w*v0303 y z w +
    q0402 y z w*v0302 y z w +
    q0403 y z w*v0301 y z w +
    q0500 y z w*v0204 y z w +
    q0501 y z w*v0203 y z w +
    q0502 y z w*v0202 y z w +
    q0503 y z w*v0201 y z w +
    q0504 y z w*v0200 y z w +
    q0600 y z w*v0104 y z w +
    q0601 y z w*v0103 y z w +
    q0602 y z w*v0102 y z w +
    q0603 y z w*v0101 y z w +
    q0604 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0003Data r0301Data) (product q0004Data r0300Data)) (product q0102Data r0202Data)) (product q0103Data r0201Data)) (product q0104Data r0200Data)) (product q0201Data r0103Data)) (product q0202Data r0102Data)) (product q0203Data r0101Data)) (product q0204Data r0100Data)) (product q0301Data r0003Data)) (product q0302Data r0002Data)) (product q0303Data r0001Data)) (product q0304Data r0000Data)) (product q0400Data v0304Data)) (product q0401Data v0303Data)) (product q0402Data v0302Data)) (product q0403Data v0301Data)) (product q0500Data v0204Data)) (product q0501Data v0203Data)) (product q0502Data v0202Data)) (product q0503Data v0201Data)) (product q0504Data v0200Data)) (product q0600Data v0104Data)) (product q0601Data v0103Data)) (product q0602Data v0102Data)) (product q0603Data v0101Data)) (product q0604Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0003, q0004, q0102, q0103, q0104, q0201, q0202, q0203, q0204, q0301, q0302, q0303, q0304, q0400, q0401, q0402, q0403, q0500, q0501, q0502, q0503, q0504, q0600, q0601, q0602, q0603, q0604, r0000, r0001, r0002, r0003, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0200, v0201, v0202, v0203, v0204, v0301, v0302, v0303, v0304] using he

#print axioms row3_x04

compact_certificate theorem row3_x05 (y z w : ℂ) :
    q0004 y z w*r0301 y z w +
    q0005 y z w*r0300 y z w +
    q0103 y z w*r0202 y z w +
    q0104 y z w*r0201 y z w +
    q0105 y z w*r0200 y z w +
    q0202 y z w*r0103 y z w +
    q0203 y z w*r0102 y z w +
    q0204 y z w*r0101 y z w +
    q0205 y z w*r0100 y z w +
    q0302 y z w*r0003 y z w +
    q0303 y z w*r0002 y z w +
    q0304 y z w*r0001 y z w +
    q0305 y z w*r0000 y z w +
    q0400 y z w*v0305 y z w +
    q0401 y z w*v0304 y z w +
    q0402 y z w*v0303 y z w +
    q0403 y z w*v0302 y z w +
    q0404 y z w*v0301 y z w +
    q0500 y z w*v0205 y z w +
    q0501 y z w*v0204 y z w +
    q0502 y z w*v0203 y z w +
    q0503 y z w*v0202 y z w +
    q0504 y z w*v0201 y z w +
    q0505 y z w*v0200 y z w +
    q0600 y z w*v0105 y z w +
    q0601 y z w*v0104 y z w +
    q0602 y z w*v0103 y z w +
    q0603 y z w*v0102 y z w +
    q0604 y z w*v0101 y z w +
    q0605 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0004Data r0301Data) (product q0005Data r0300Data)) (product q0103Data r0202Data)) (product q0104Data r0201Data)) (product q0105Data r0200Data)) (product q0202Data r0103Data)) (product q0203Data r0102Data)) (product q0204Data r0101Data)) (product q0205Data r0100Data)) (product q0302Data r0003Data)) (product q0303Data r0002Data)) (product q0304Data r0001Data)) (product q0305Data r0000Data)) (product q0400Data v0305Data)) (product q0401Data v0304Data)) (product q0402Data v0303Data)) (product q0403Data v0302Data)) (product q0404Data v0301Data)) (product q0500Data v0205Data)) (product q0501Data v0204Data)) (product q0502Data v0203Data)) (product q0503Data v0202Data)) (product q0504Data v0201Data)) (product q0505Data v0200Data)) (product q0600Data v0105Data)) (product q0601Data v0104Data)) (product q0602Data v0103Data)) (product q0603Data v0102Data)) (product q0604Data v0101Data)) (product q0605Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0004, q0005, q0103, q0104, q0105, q0202, q0203, q0204, q0205, q0302, q0303, q0304, q0305, q0400, q0401, q0402, q0403, q0404, q0500, q0501, q0502, q0503, q0504, q0505, q0600, q0601, q0602, q0603, q0604, q0605, r0000, r0001, r0002, r0003, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0200, v0201, v0202, v0203, v0204, v0205, v0301, v0302, v0303, v0304, v0305] using he

#print axioms row3_x05

compact_certificate theorem row3_x06 (y z w : ℂ) :
    q0005 y z w*r0301 y z w +
    q0006 y z w*r0300 y z w +
    q0104 y z w*r0202 y z w +
    q0105 y z w*r0201 y z w +
    q0106 y z w*r0200 y z w +
    q0203 y z w*r0103 y z w +
    q0204 y z w*r0102 y z w +
    q0205 y z w*r0101 y z w +
    q0206 y z w*r0100 y z w +
    q0301 y z w*r0005 y z w +
    q0303 y z w*r0003 y z w +
    q0304 y z w*r0002 y z w +
    q0305 y z w*r0001 y z w +
    q0306 y z w*r0000 y z w +
    q0400 y z w*v0306 y z w +
    q0401 y z w*v0305 y z w +
    q0402 y z w*v0304 y z w +
    q0403 y z w*v0303 y z w +
    q0404 y z w*v0302 y z w +
    q0405 y z w*v0301 y z w +
    q0500 y z w*v0206 y z w +
    q0501 y z w*v0205 y z w +
    q0502 y z w*v0204 y z w +
    q0503 y z w*v0203 y z w +
    q0504 y z w*v0202 y z w +
    q0505 y z w*v0201 y z w +
    q0506 y z w*v0200 y z w +
    q0600 y z w*v0106 y z w +
    q0601 y z w*v0105 y z w +
    q0602 y z w*v0104 y z w +
    q0603 y z w*v0103 y z w +
    q0604 y z w*v0102 y z w +
    q0605 y z w*v0101 y z w +
    q0606 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0005Data r0301Data) (product q0006Data r0300Data)) (product q0104Data r0202Data)) (product q0105Data r0201Data)) (product q0106Data r0200Data)) (product q0203Data r0103Data)) (product q0204Data r0102Data)) (product q0205Data r0101Data)) (product q0206Data r0100Data)) (product q0301Data r0005Data)) (product q0303Data r0003Data)) (product q0304Data r0002Data)) (product q0305Data r0001Data)) (product q0306Data r0000Data)) (product q0400Data v0306Data)) (product q0401Data v0305Data)) (product q0402Data v0304Data)) (product q0403Data v0303Data)) (product q0404Data v0302Data)) (product q0405Data v0301Data)) (product q0500Data v0206Data)) (product q0501Data v0205Data)) (product q0502Data v0204Data)) (product q0503Data v0203Data)) (product q0504Data v0202Data)) (product q0505Data v0201Data)) (product q0506Data v0200Data)) (product q0600Data v0106Data)) (product q0601Data v0105Data)) (product q0602Data v0104Data)) (product q0603Data v0103Data)) (product q0604Data v0102Data)) (product q0605Data v0101Data)) (product q0606Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0005, q0006, q0104, q0105, q0106, q0203, q0204, q0205, q0206, q0301, q0303, q0304, q0305, q0306, q0400, q0401, q0402, q0403, q0404, q0405, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0600, q0601, q0602, q0603, q0604, q0605, q0606, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0301, v0302, v0303, v0304, v0305, v0306] using he

#print axioms row3_x06

compact_certificate theorem row3_x07 (y z w : ℂ) :
    q0006 y z w*r0301 y z w +
    q0007 y z w*r0300 y z w +
    q0105 y z w*r0202 y z w +
    q0106 y z w*r0201 y z w +
    q0107 y z w*r0200 y z w +
    q0204 y z w*r0103 y z w +
    q0205 y z w*r0102 y z w +
    q0206 y z w*r0101 y z w +
    q0207 y z w*r0100 y z w +
    q0302 y z w*r0005 y z w +
    q0304 y z w*r0003 y z w +
    q0305 y z w*r0002 y z w +
    q0306 y z w*r0001 y z w +
    q0307 y z w*r0000 y z w +
    q0400 y z w*v0307 y z w +
    q0401 y z w*v0306 y z w +
    q0402 y z w*v0305 y z w +
    q0403 y z w*v0304 y z w +
    q0404 y z w*v0303 y z w +
    q0405 y z w*v0302 y z w +
    q0406 y z w*v0301 y z w +
    q0500 y z w*v0207 y z w +
    q0501 y z w*v0206 y z w +
    q0502 y z w*v0205 y z w +
    q0503 y z w*v0204 y z w +
    q0504 y z w*v0203 y z w +
    q0505 y z w*v0202 y z w +
    q0506 y z w*v0201 y z w +
    q0507 y z w*v0200 y z w +
    q0600 y z w*v0107 y z w +
    q0601 y z w*v0106 y z w +
    q0602 y z w*v0105 y z w +
    q0603 y z w*v0104 y z w +
    q0604 y z w*v0103 y z w +
    q0605 y z w*v0102 y z w +
    q0606 y z w*v0101 y z w +
    q0607 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0006Data r0301Data) (product q0007Data r0300Data)) (product q0105Data r0202Data)) (product q0106Data r0201Data)) (product q0107Data r0200Data)) (product q0204Data r0103Data)) (product q0205Data r0102Data)) (product q0206Data r0101Data)) (product q0207Data r0100Data)) (product q0302Data r0005Data)) (product q0304Data r0003Data)) (product q0305Data r0002Data)) (product q0306Data r0001Data)) (product q0307Data r0000Data)) (product q0400Data v0307Data)) (product q0401Data v0306Data)) (product q0402Data v0305Data)) (product q0403Data v0304Data)) (product q0404Data v0303Data)) (product q0405Data v0302Data)) (product q0406Data v0301Data)) (product q0500Data v0207Data)) (product q0501Data v0206Data)) (product q0502Data v0205Data)) (product q0503Data v0204Data)) (product q0504Data v0203Data)) (product q0505Data v0202Data)) (product q0506Data v0201Data)) (product q0507Data v0200Data)) (product q0600Data v0107Data)) (product q0601Data v0106Data)) (product q0602Data v0105Data)) (product q0603Data v0104Data)) (product q0604Data v0103Data)) (product q0605Data v0102Data)) (product q0606Data v0101Data)) (product q0607Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0006, q0007, q0105, q0106, q0107, q0204, q0205, q0206, q0207, q0302, q0304, q0305, q0306, q0307, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x07

compact_certificate theorem row3_x08 (y z w : ℂ) :
    q0007 y z w*r0301 y z w +
    q0008 y z w*r0300 y z w +
    q0106 y z w*r0202 y z w +
    q0107 y z w*r0201 y z w +
    q0108 y z w*r0200 y z w +
    q0205 y z w*r0103 y z w +
    q0206 y z w*r0102 y z w +
    q0207 y z w*r0101 y z w +
    q0208 y z w*r0100 y z w +
    q0303 y z w*r0005 y z w +
    q0305 y z w*r0003 y z w +
    q0306 y z w*r0002 y z w +
    q0307 y z w*r0001 y z w +
    q0308 y z w*r0000 y z w +
    q0401 y z w*v0307 y z w +
    q0402 y z w*v0306 y z w +
    q0403 y z w*v0305 y z w +
    q0404 y z w*v0304 y z w +
    q0405 y z w*v0303 y z w +
    q0406 y z w*v0302 y z w +
    q0407 y z w*v0301 y z w +
    q0500 y z w*v0208 y z w +
    q0501 y z w*v0207 y z w +
    q0502 y z w*v0206 y z w +
    q0503 y z w*v0205 y z w +
    q0504 y z w*v0204 y z w +
    q0505 y z w*v0203 y z w +
    q0506 y z w*v0202 y z w +
    q0507 y z w*v0201 y z w +
    q0508 y z w*v0200 y z w +
    q0600 y z w*v0108 y z w +
    q0601 y z w*v0107 y z w +
    q0602 y z w*v0106 y z w +
    q0603 y z w*v0105 y z w +
    q0604 y z w*v0104 y z w +
    q0605 y z w*v0103 y z w +
    q0606 y z w*v0102 y z w +
    q0607 y z w*v0101 y z w +
    q0608 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0007Data r0301Data) (product q0008Data r0300Data)) (product q0106Data r0202Data)) (product q0107Data r0201Data)) (product q0108Data r0200Data)) (product q0205Data r0103Data)) (product q0206Data r0102Data)) (product q0207Data r0101Data)) (product q0208Data r0100Data)) (product q0303Data r0005Data)) (product q0305Data r0003Data)) (product q0306Data r0002Data)) (product q0307Data r0001Data)) (product q0308Data r0000Data)) (product q0401Data v0307Data)) (product q0402Data v0306Data)) (product q0403Data v0305Data)) (product q0404Data v0304Data)) (product q0405Data v0303Data)) (product q0406Data v0302Data)) (product q0407Data v0301Data)) (product q0500Data v0208Data)) (product q0501Data v0207Data)) (product q0502Data v0206Data)) (product q0503Data v0205Data)) (product q0504Data v0204Data)) (product q0505Data v0203Data)) (product q0506Data v0202Data)) (product q0507Data v0201Data)) (product q0508Data v0200Data)) (product q0600Data v0108Data)) (product q0601Data v0107Data)) (product q0602Data v0106Data)) (product q0603Data v0105Data)) (product q0604Data v0104Data)) (product q0605Data v0103Data)) (product q0606Data v0102Data)) (product q0607Data v0101Data)) (product q0608Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0007, q0008, q0106, q0107, q0108, q0205, q0206, q0207, q0208, q0303, q0305, q0306, q0307, q0308, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x08

compact_certificate theorem row3_x09 (y z w : ℂ) :
    q0008 y z w*r0301 y z w +
    q0009 y z w*r0300 y z w +
    q0107 y z w*r0202 y z w +
    q0108 y z w*r0201 y z w +
    q0109 y z w*r0200 y z w +
    q0206 y z w*r0103 y z w +
    q0207 y z w*r0102 y z w +
    q0208 y z w*r0101 y z w +
    q0209 y z w*r0100 y z w +
    q0304 y z w*r0005 y z w +
    q0306 y z w*r0003 y z w +
    q0307 y z w*r0002 y z w +
    q0308 y z w*r0001 y z w +
    q0309 y z w*r0000 y z w +
    q0402 y z w*v0307 y z w +
    q0403 y z w*v0306 y z w +
    q0404 y z w*v0305 y z w +
    q0405 y z w*v0304 y z w +
    q0406 y z w*v0303 y z w +
    q0407 y z w*v0302 y z w +
    q0408 y z w*v0301 y z w +
    q0501 y z w*v0208 y z w +
    q0502 y z w*v0207 y z w +
    q0503 y z w*v0206 y z w +
    q0504 y z w*v0205 y z w +
    q0505 y z w*v0204 y z w +
    q0506 y z w*v0203 y z w +
    q0507 y z w*v0202 y z w +
    q0508 y z w*v0201 y z w +
    q0509 y z w*v0200 y z w +
    q0600 y z w*v0109 y z w +
    q0601 y z w*v0108 y z w +
    q0602 y z w*v0107 y z w +
    q0603 y z w*v0106 y z w +
    q0604 y z w*v0105 y z w +
    q0605 y z w*v0104 y z w +
    q0606 y z w*v0103 y z w +
    q0607 y z w*v0102 y z w +
    q0608 y z w*v0101 y z w +
    q0609 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0008Data r0301Data) (product q0009Data r0300Data)) (product q0107Data r0202Data)) (product q0108Data r0201Data)) (product q0109Data r0200Data)) (product q0206Data r0103Data)) (product q0207Data r0102Data)) (product q0208Data r0101Data)) (product q0209Data r0100Data)) (product q0304Data r0005Data)) (product q0306Data r0003Data)) (product q0307Data r0002Data)) (product q0308Data r0001Data)) (product q0309Data r0000Data)) (product q0402Data v0307Data)) (product q0403Data v0306Data)) (product q0404Data v0305Data)) (product q0405Data v0304Data)) (product q0406Data v0303Data)) (product q0407Data v0302Data)) (product q0408Data v0301Data)) (product q0501Data v0208Data)) (product q0502Data v0207Data)) (product q0503Data v0206Data)) (product q0504Data v0205Data)) (product q0505Data v0204Data)) (product q0506Data v0203Data)) (product q0507Data v0202Data)) (product q0508Data v0201Data)) (product q0509Data v0200Data)) (product q0600Data v0109Data)) (product q0601Data v0108Data)) (product q0602Data v0107Data)) (product q0603Data v0106Data)) (product q0604Data v0105Data)) (product q0605Data v0104Data)) (product q0606Data v0103Data)) (product q0607Data v0102Data)) (product q0608Data v0101Data)) (product q0609Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0008, q0009, q0107, q0108, q0109, q0206, q0207, q0208, q0209, q0304, q0306, q0307, q0308, q0309, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x09

compact_certificate theorem row3_x10 (y z w : ℂ) :
    q0009 y z w*r0301 y z w +
    q0010 y z w*r0300 y z w +
    q0108 y z w*r0202 y z w +
    q0109 y z w*r0201 y z w +
    q0110 y z w*r0200 y z w +
    q0207 y z w*r0103 y z w +
    q0208 y z w*r0102 y z w +
    q0209 y z w*r0101 y z w +
    q0210 y z w*r0100 y z w +
    q0305 y z w*r0005 y z w +
    q0307 y z w*r0003 y z w +
    q0308 y z w*r0002 y z w +
    q0309 y z w*r0001 y z w +
    q0310 y z w*r0000 y z w +
    q0403 y z w*v0307 y z w +
    q0404 y z w*v0306 y z w +
    q0405 y z w*v0305 y z w +
    q0406 y z w*v0304 y z w +
    q0407 y z w*v0303 y z w +
    q0408 y z w*v0302 y z w +
    q0409 y z w*v0301 y z w +
    q0502 y z w*v0208 y z w +
    q0503 y z w*v0207 y z w +
    q0504 y z w*v0206 y z w +
    q0505 y z w*v0205 y z w +
    q0506 y z w*v0204 y z w +
    q0507 y z w*v0203 y z w +
    q0508 y z w*v0202 y z w +
    q0509 y z w*v0201 y z w +
    q0510 y z w*v0200 y z w +
    q0600 y z w*v0110 y z w +
    q0601 y z w*v0109 y z w +
    q0602 y z w*v0108 y z w +
    q0603 y z w*v0107 y z w +
    q0604 y z w*v0106 y z w +
    q0605 y z w*v0105 y z w +
    q0606 y z w*v0104 y z w +
    q0607 y z w*v0103 y z w +
    q0608 y z w*v0102 y z w +
    q0609 y z w*v0101 y z w +
    q0610 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0009Data r0301Data) (product q0010Data r0300Data)) (product q0108Data r0202Data)) (product q0109Data r0201Data)) (product q0110Data r0200Data)) (product q0207Data r0103Data)) (product q0208Data r0102Data)) (product q0209Data r0101Data)) (product q0210Data r0100Data)) (product q0305Data r0005Data)) (product q0307Data r0003Data)) (product q0308Data r0002Data)) (product q0309Data r0001Data)) (product q0310Data r0000Data)) (product q0403Data v0307Data)) (product q0404Data v0306Data)) (product q0405Data v0305Data)) (product q0406Data v0304Data)) (product q0407Data v0303Data)) (product q0408Data v0302Data)) (product q0409Data v0301Data)) (product q0502Data v0208Data)) (product q0503Data v0207Data)) (product q0504Data v0206Data)) (product q0505Data v0205Data)) (product q0506Data v0204Data)) (product q0507Data v0203Data)) (product q0508Data v0202Data)) (product q0509Data v0201Data)) (product q0510Data v0200Data)) (product q0600Data v0110Data)) (product q0601Data v0109Data)) (product q0602Data v0108Data)) (product q0603Data v0107Data)) (product q0604Data v0106Data)) (product q0605Data v0105Data)) (product q0606Data v0104Data)) (product q0607Data v0103Data)) (product q0608Data v0102Data)) (product q0609Data v0101Data)) (product q0610Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0009, q0010, q0108, q0109, q0110, q0207, q0208, q0209, q0210, q0305, q0307, q0308, q0309, q0310, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x10

compact_certificate theorem row3_x11 (y z w : ℂ) :
    q0010 y z w*r0301 y z w +
    q0011 y z w*r0300 y z w +
    q0109 y z w*r0202 y z w +
    q0110 y z w*r0201 y z w +
    q0111 y z w*r0200 y z w +
    q0208 y z w*r0103 y z w +
    q0209 y z w*r0102 y z w +
    q0210 y z w*r0101 y z w +
    q0211 y z w*r0100 y z w +
    q0306 y z w*r0005 y z w +
    q0308 y z w*r0003 y z w +
    q0309 y z w*r0002 y z w +
    q0310 y z w*r0001 y z w +
    q0311 y z w*r0000 y z w +
    q0404 y z w*v0307 y z w +
    q0405 y z w*v0306 y z w +
    q0406 y z w*v0305 y z w +
    q0407 y z w*v0304 y z w +
    q0408 y z w*v0303 y z w +
    q0409 y z w*v0302 y z w +
    q0410 y z w*v0301 y z w +
    q0503 y z w*v0208 y z w +
    q0504 y z w*v0207 y z w +
    q0505 y z w*v0206 y z w +
    q0506 y z w*v0205 y z w +
    q0507 y z w*v0204 y z w +
    q0508 y z w*v0203 y z w +
    q0509 y z w*v0202 y z w +
    q0510 y z w*v0201 y z w +
    q0511 y z w*v0200 y z w +
    q0601 y z w*v0110 y z w +
    q0602 y z w*v0109 y z w +
    q0603 y z w*v0108 y z w +
    q0604 y z w*v0107 y z w +
    q0605 y z w*v0106 y z w +
    q0606 y z w*v0105 y z w +
    q0607 y z w*v0104 y z w +
    q0608 y z w*v0103 y z w +
    q0609 y z w*v0102 y z w +
    q0610 y z w*v0101 y z w +
    q0611 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0010Data r0301Data) (product q0011Data r0300Data)) (product q0109Data r0202Data)) (product q0110Data r0201Data)) (product q0111Data r0200Data)) (product q0208Data r0103Data)) (product q0209Data r0102Data)) (product q0210Data r0101Data)) (product q0211Data r0100Data)) (product q0306Data r0005Data)) (product q0308Data r0003Data)) (product q0309Data r0002Data)) (product q0310Data r0001Data)) (product q0311Data r0000Data)) (product q0404Data v0307Data)) (product q0405Data v0306Data)) (product q0406Data v0305Data)) (product q0407Data v0304Data)) (product q0408Data v0303Data)) (product q0409Data v0302Data)) (product q0410Data v0301Data)) (product q0503Data v0208Data)) (product q0504Data v0207Data)) (product q0505Data v0206Data)) (product q0506Data v0205Data)) (product q0507Data v0204Data)) (product q0508Data v0203Data)) (product q0509Data v0202Data)) (product q0510Data v0201Data)) (product q0511Data v0200Data)) (product q0601Data v0110Data)) (product q0602Data v0109Data)) (product q0603Data v0108Data)) (product q0604Data v0107Data)) (product q0605Data v0106Data)) (product q0606Data v0105Data)) (product q0607Data v0104Data)) (product q0608Data v0103Data)) (product q0609Data v0102Data)) (product q0610Data v0101Data)) (product q0611Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0010, q0011, q0109, q0110, q0111, q0208, q0209, q0210, q0211, q0306, q0308, q0309, q0310, q0311, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x11

compact_certificate theorem row3_x12 (y z w : ℂ) :
    q0011 y z w*r0301 y z w +
    q0012 y z w*r0300 y z w +
    q0110 y z w*r0202 y z w +
    q0111 y z w*r0201 y z w +
    q0112 y z w*r0200 y z w +
    q0209 y z w*r0103 y z w +
    q0210 y z w*r0102 y z w +
    q0211 y z w*r0101 y z w +
    q0212 y z w*r0100 y z w +
    q0307 y z w*r0005 y z w +
    q0309 y z w*r0003 y z w +
    q0310 y z w*r0002 y z w +
    q0311 y z w*r0001 y z w +
    q0312 y z w*r0000 y z w +
    q0405 y z w*v0307 y z w +
    q0406 y z w*v0306 y z w +
    q0407 y z w*v0305 y z w +
    q0408 y z w*v0304 y z w +
    q0409 y z w*v0303 y z w +
    q0410 y z w*v0302 y z w +
    q0411 y z w*v0301 y z w +
    q0504 y z w*v0208 y z w +
    q0505 y z w*v0207 y z w +
    q0506 y z w*v0206 y z w +
    q0507 y z w*v0205 y z w +
    q0508 y z w*v0204 y z w +
    q0509 y z w*v0203 y z w +
    q0510 y z w*v0202 y z w +
    q0511 y z w*v0201 y z w +
    q0512 y z w*v0200 y z w +
    q0602 y z w*v0110 y z w +
    q0603 y z w*v0109 y z w +
    q0604 y z w*v0108 y z w +
    q0605 y z w*v0107 y z w +
    q0606 y z w*v0106 y z w +
    q0607 y z w*v0105 y z w +
    q0608 y z w*v0104 y z w +
    q0609 y z w*v0103 y z w +
    q0610 y z w*v0102 y z w +
    q0611 y z w*v0101 y z w +
    q0612 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0011Data r0301Data) (product q0012Data r0300Data)) (product q0110Data r0202Data)) (product q0111Data r0201Data)) (product q0112Data r0200Data)) (product q0209Data r0103Data)) (product q0210Data r0102Data)) (product q0211Data r0101Data)) (product q0212Data r0100Data)) (product q0307Data r0005Data)) (product q0309Data r0003Data)) (product q0310Data r0002Data)) (product q0311Data r0001Data)) (product q0312Data r0000Data)) (product q0405Data v0307Data)) (product q0406Data v0306Data)) (product q0407Data v0305Data)) (product q0408Data v0304Data)) (product q0409Data v0303Data)) (product q0410Data v0302Data)) (product q0411Data v0301Data)) (product q0504Data v0208Data)) (product q0505Data v0207Data)) (product q0506Data v0206Data)) (product q0507Data v0205Data)) (product q0508Data v0204Data)) (product q0509Data v0203Data)) (product q0510Data v0202Data)) (product q0511Data v0201Data)) (product q0512Data v0200Data)) (product q0602Data v0110Data)) (product q0603Data v0109Data)) (product q0604Data v0108Data)) (product q0605Data v0107Data)) (product q0606Data v0106Data)) (product q0607Data v0105Data)) (product q0608Data v0104Data)) (product q0609Data v0103Data)) (product q0610Data v0102Data)) (product q0611Data v0101Data)) (product q0612Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0011, q0012, q0110, q0111, q0112, q0209, q0210, q0211, q0212, q0307, q0309, q0310, q0311, q0312, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x12

compact_certificate theorem row3_x13 (y z w : ℂ) :
    q0012 y z w*r0301 y z w +
    q0013 y z w*r0300 y z w +
    q0111 y z w*r0202 y z w +
    q0112 y z w*r0201 y z w +
    q0113 y z w*r0200 y z w +
    q0210 y z w*r0103 y z w +
    q0211 y z w*r0102 y z w +
    q0212 y z w*r0101 y z w +
    q0213 y z w*r0100 y z w +
    q0308 y z w*r0005 y z w +
    q0310 y z w*r0003 y z w +
    q0311 y z w*r0002 y z w +
    q0312 y z w*r0001 y z w +
    q0313 y z w*r0000 y z w +
    q0406 y z w*v0307 y z w +
    q0407 y z w*v0306 y z w +
    q0408 y z w*v0305 y z w +
    q0409 y z w*v0304 y z w +
    q0410 y z w*v0303 y z w +
    q0411 y z w*v0302 y z w +
    q0412 y z w*v0301 y z w +
    q0505 y z w*v0208 y z w +
    q0506 y z w*v0207 y z w +
    q0507 y z w*v0206 y z w +
    q0508 y z w*v0205 y z w +
    q0509 y z w*v0204 y z w +
    q0510 y z w*v0203 y z w +
    q0511 y z w*v0202 y z w +
    q0512 y z w*v0201 y z w +
    q0513 y z w*v0200 y z w +
    q0603 y z w*v0110 y z w +
    q0604 y z w*v0109 y z w +
    q0605 y z w*v0108 y z w +
    q0606 y z w*v0107 y z w +
    q0607 y z w*v0106 y z w +
    q0608 y z w*v0105 y z w +
    q0609 y z w*v0104 y z w +
    q0610 y z w*v0103 y z w +
    q0611 y z w*v0102 y z w +
    q0612 y z w*v0101 y z w +
    q0613 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0012Data r0301Data) (product q0013Data r0300Data)) (product q0111Data r0202Data)) (product q0112Data r0201Data)) (product q0113Data r0200Data)) (product q0210Data r0103Data)) (product q0211Data r0102Data)) (product q0212Data r0101Data)) (product q0213Data r0100Data)) (product q0308Data r0005Data)) (product q0310Data r0003Data)) (product q0311Data r0002Data)) (product q0312Data r0001Data)) (product q0313Data r0000Data)) (product q0406Data v0307Data)) (product q0407Data v0306Data)) (product q0408Data v0305Data)) (product q0409Data v0304Data)) (product q0410Data v0303Data)) (product q0411Data v0302Data)) (product q0412Data v0301Data)) (product q0505Data v0208Data)) (product q0506Data v0207Data)) (product q0507Data v0206Data)) (product q0508Data v0205Data)) (product q0509Data v0204Data)) (product q0510Data v0203Data)) (product q0511Data v0202Data)) (product q0512Data v0201Data)) (product q0513Data v0200Data)) (product q0603Data v0110Data)) (product q0604Data v0109Data)) (product q0605Data v0108Data)) (product q0606Data v0107Data)) (product q0607Data v0106Data)) (product q0608Data v0105Data)) (product q0609Data v0104Data)) (product q0610Data v0103Data)) (product q0611Data v0102Data)) (product q0612Data v0101Data)) (product q0613Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0012, q0013, q0111, q0112, q0113, q0210, q0211, q0212, q0213, q0308, q0310, q0311, q0312, q0313, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x13

compact_certificate theorem row3_x14 (y z w : ℂ) :
    q0013 y z w*r0301 y z w +
    q0014 y z w*r0300 y z w +
    q0112 y z w*r0202 y z w +
    q0113 y z w*r0201 y z w +
    q0114 y z w*r0200 y z w +
    q0211 y z w*r0103 y z w +
    q0212 y z w*r0102 y z w +
    q0213 y z w*r0101 y z w +
    q0214 y z w*r0100 y z w +
    q0309 y z w*r0005 y z w +
    q0311 y z w*r0003 y z w +
    q0312 y z w*r0002 y z w +
    q0313 y z w*r0001 y z w +
    q0314 y z w*r0000 y z w +
    q0407 y z w*v0307 y z w +
    q0408 y z w*v0306 y z w +
    q0409 y z w*v0305 y z w +
    q0410 y z w*v0304 y z w +
    q0411 y z w*v0303 y z w +
    q0412 y z w*v0302 y z w +
    q0413 y z w*v0301 y z w +
    q0506 y z w*v0208 y z w +
    q0507 y z w*v0207 y z w +
    q0508 y z w*v0206 y z w +
    q0509 y z w*v0205 y z w +
    q0510 y z w*v0204 y z w +
    q0511 y z w*v0203 y z w +
    q0512 y z w*v0202 y z w +
    q0513 y z w*v0201 y z w +
    q0514 y z w*v0200 y z w +
    q0604 y z w*v0110 y z w +
    q0605 y z w*v0109 y z w +
    q0606 y z w*v0108 y z w +
    q0607 y z w*v0107 y z w +
    q0608 y z w*v0106 y z w +
    q0609 y z w*v0105 y z w +
    q0610 y z w*v0104 y z w +
    q0611 y z w*v0103 y z w +
    q0612 y z w*v0102 y z w +
    q0613 y z w*v0101 y z w +
    q0614 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0013Data r0301Data) (product q0014Data r0300Data)) (product q0112Data r0202Data)) (product q0113Data r0201Data)) (product q0114Data r0200Data)) (product q0211Data r0103Data)) (product q0212Data r0102Data)) (product q0213Data r0101Data)) (product q0214Data r0100Data)) (product q0309Data r0005Data)) (product q0311Data r0003Data)) (product q0312Data r0002Data)) (product q0313Data r0001Data)) (product q0314Data r0000Data)) (product q0407Data v0307Data)) (product q0408Data v0306Data)) (product q0409Data v0305Data)) (product q0410Data v0304Data)) (product q0411Data v0303Data)) (product q0412Data v0302Data)) (product q0413Data v0301Data)) (product q0506Data v0208Data)) (product q0507Data v0207Data)) (product q0508Data v0206Data)) (product q0509Data v0205Data)) (product q0510Data v0204Data)) (product q0511Data v0203Data)) (product q0512Data v0202Data)) (product q0513Data v0201Data)) (product q0514Data v0200Data)) (product q0604Data v0110Data)) (product q0605Data v0109Data)) (product q0606Data v0108Data)) (product q0607Data v0107Data)) (product q0608Data v0106Data)) (product q0609Data v0105Data)) (product q0610Data v0104Data)) (product q0611Data v0103Data)) (product q0612Data v0102Data)) (product q0613Data v0101Data)) (product q0614Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0013, q0014, q0112, q0113, q0114, q0211, q0212, q0213, q0214, q0309, q0311, q0312, q0313, q0314, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x14

compact_certificate theorem row3_x15 (y z w : ℂ) :
    q0014 y z w*r0301 y z w +
    q0015 y z w*r0300 y z w +
    q0113 y z w*r0202 y z w +
    q0114 y z w*r0201 y z w +
    q0115 y z w*r0200 y z w +
    q0212 y z w*r0103 y z w +
    q0213 y z w*r0102 y z w +
    q0214 y z w*r0101 y z w +
    q0215 y z w*r0100 y z w +
    q0310 y z w*r0005 y z w +
    q0312 y z w*r0003 y z w +
    q0313 y z w*r0002 y z w +
    q0314 y z w*r0001 y z w +
    q0315 y z w*r0000 y z w +
    q0408 y z w*v0307 y z w +
    q0409 y z w*v0306 y z w +
    q0410 y z w*v0305 y z w +
    q0411 y z w*v0304 y z w +
    q0412 y z w*v0303 y z w +
    q0413 y z w*v0302 y z w +
    q0414 y z w*v0301 y z w +
    q0507 y z w*v0208 y z w +
    q0508 y z w*v0207 y z w +
    q0509 y z w*v0206 y z w +
    q0510 y z w*v0205 y z w +
    q0511 y z w*v0204 y z w +
    q0512 y z w*v0203 y z w +
    q0513 y z w*v0202 y z w +
    q0514 y z w*v0201 y z w +
    q0515 y z w*v0200 y z w +
    q0605 y z w*v0110 y z w +
    q0606 y z w*v0109 y z w +
    q0607 y z w*v0108 y z w +
    q0608 y z w*v0107 y z w +
    q0609 y z w*v0106 y z w +
    q0610 y z w*v0105 y z w +
    q0611 y z w*v0104 y z w +
    q0612 y z w*v0103 y z w +
    q0613 y z w*v0102 y z w +
    q0614 y z w*v0101 y z w +
    q0615 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0014Data r0301Data) (product q0015Data r0300Data)) (product q0113Data r0202Data)) (product q0114Data r0201Data)) (product q0115Data r0200Data)) (product q0212Data r0103Data)) (product q0213Data r0102Data)) (product q0214Data r0101Data)) (product q0215Data r0100Data)) (product q0310Data r0005Data)) (product q0312Data r0003Data)) (product q0313Data r0002Data)) (product q0314Data r0001Data)) (product q0315Data r0000Data)) (product q0408Data v0307Data)) (product q0409Data v0306Data)) (product q0410Data v0305Data)) (product q0411Data v0304Data)) (product q0412Data v0303Data)) (product q0413Data v0302Data)) (product q0414Data v0301Data)) (product q0507Data v0208Data)) (product q0508Data v0207Data)) (product q0509Data v0206Data)) (product q0510Data v0205Data)) (product q0511Data v0204Data)) (product q0512Data v0203Data)) (product q0513Data v0202Data)) (product q0514Data v0201Data)) (product q0515Data v0200Data)) (product q0605Data v0110Data)) (product q0606Data v0109Data)) (product q0607Data v0108Data)) (product q0608Data v0107Data)) (product q0609Data v0106Data)) (product q0610Data v0105Data)) (product q0611Data v0104Data)) (product q0612Data v0103Data)) (product q0613Data v0102Data)) (product q0614Data v0101Data)) (product q0615Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0014, q0015, q0113, q0114, q0115, q0212, q0213, q0214, q0215, q0310, q0312, q0313, q0314, q0315, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x15

compact_certificate theorem row3_x16 (y z w : ℂ) :
    q0015 y z w*r0301 y z w +
    q0016 y z w*r0300 y z w +
    q0114 y z w*r0202 y z w +
    q0115 y z w*r0201 y z w +
    q0116 y z w*r0200 y z w +
    q0213 y z w*r0103 y z w +
    q0214 y z w*r0102 y z w +
    q0215 y z w*r0101 y z w +
    q0216 y z w*r0100 y z w +
    q0311 y z w*r0005 y z w +
    q0313 y z w*r0003 y z w +
    q0314 y z w*r0002 y z w +
    q0315 y z w*r0001 y z w +
    q0316 y z w*r0000 y z w +
    q0409 y z w*v0307 y z w +
    q0410 y z w*v0306 y z w +
    q0411 y z w*v0305 y z w +
    q0412 y z w*v0304 y z w +
    q0413 y z w*v0303 y z w +
    q0414 y z w*v0302 y z w +
    q0415 y z w*v0301 y z w +
    q0508 y z w*v0208 y z w +
    q0509 y z w*v0207 y z w +
    q0510 y z w*v0206 y z w +
    q0511 y z w*v0205 y z w +
    q0512 y z w*v0204 y z w +
    q0513 y z w*v0203 y z w +
    q0514 y z w*v0202 y z w +
    q0515 y z w*v0201 y z w +
    q0516 y z w*v0200 y z w +
    q0606 y z w*v0110 y z w +
    q0607 y z w*v0109 y z w +
    q0608 y z w*v0108 y z w +
    q0609 y z w*v0107 y z w +
    q0610 y z w*v0106 y z w +
    q0611 y z w*v0105 y z w +
    q0612 y z w*v0104 y z w +
    q0613 y z w*v0103 y z w +
    q0614 y z w*v0102 y z w +
    q0615 y z w*v0101 y z w +
    q0616 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0015Data r0301Data) (product q0016Data r0300Data)) (product q0114Data r0202Data)) (product q0115Data r0201Data)) (product q0116Data r0200Data)) (product q0213Data r0103Data)) (product q0214Data r0102Data)) (product q0215Data r0101Data)) (product q0216Data r0100Data)) (product q0311Data r0005Data)) (product q0313Data r0003Data)) (product q0314Data r0002Data)) (product q0315Data r0001Data)) (product q0316Data r0000Data)) (product q0409Data v0307Data)) (product q0410Data v0306Data)) (product q0411Data v0305Data)) (product q0412Data v0304Data)) (product q0413Data v0303Data)) (product q0414Data v0302Data)) (product q0415Data v0301Data)) (product q0508Data v0208Data)) (product q0509Data v0207Data)) (product q0510Data v0206Data)) (product q0511Data v0205Data)) (product q0512Data v0204Data)) (product q0513Data v0203Data)) (product q0514Data v0202Data)) (product q0515Data v0201Data)) (product q0516Data v0200Data)) (product q0606Data v0110Data)) (product q0607Data v0109Data)) (product q0608Data v0108Data)) (product q0609Data v0107Data)) (product q0610Data v0106Data)) (product q0611Data v0105Data)) (product q0612Data v0104Data)) (product q0613Data v0103Data)) (product q0614Data v0102Data)) (product q0615Data v0101Data)) (product q0616Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0015, q0016, q0114, q0115, q0116, q0213, q0214, q0215, q0216, q0311, q0313, q0314, q0315, q0316, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x16

compact_certificate theorem row3_x17 (y z w : ℂ) :
    q0016 y z w*r0301 y z w +
    q0017 y z w*r0300 y z w +
    q0115 y z w*r0202 y z w +
    q0116 y z w*r0201 y z w +
    q0117 y z w*r0200 y z w +
    q0214 y z w*r0103 y z w +
    q0215 y z w*r0102 y z w +
    q0216 y z w*r0101 y z w +
    q0217 y z w*r0100 y z w +
    q0312 y z w*r0005 y z w +
    q0314 y z w*r0003 y z w +
    q0315 y z w*r0002 y z w +
    q0316 y z w*r0001 y z w +
    q0317 y z w*r0000 y z w +
    q0410 y z w*v0307 y z w +
    q0411 y z w*v0306 y z w +
    q0412 y z w*v0305 y z w +
    q0413 y z w*v0304 y z w +
    q0414 y z w*v0303 y z w +
    q0415 y z w*v0302 y z w +
    q0416 y z w*v0301 y z w +
    q0509 y z w*v0208 y z w +
    q0510 y z w*v0207 y z w +
    q0511 y z w*v0206 y z w +
    q0512 y z w*v0205 y z w +
    q0513 y z w*v0204 y z w +
    q0514 y z w*v0203 y z w +
    q0515 y z w*v0202 y z w +
    q0516 y z w*v0201 y z w +
    q0517 y z w*v0200 y z w +
    q0607 y z w*v0110 y z w +
    q0608 y z w*v0109 y z w +
    q0609 y z w*v0108 y z w +
    q0610 y z w*v0107 y z w +
    q0611 y z w*v0106 y z w +
    q0612 y z w*v0105 y z w +
    q0613 y z w*v0104 y z w +
    q0614 y z w*v0103 y z w +
    q0615 y z w*v0102 y z w +
    q0616 y z w*v0101 y z w +
    q0617 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0016Data r0301Data) (product q0017Data r0300Data)) (product q0115Data r0202Data)) (product q0116Data r0201Data)) (product q0117Data r0200Data)) (product q0214Data r0103Data)) (product q0215Data r0102Data)) (product q0216Data r0101Data)) (product q0217Data r0100Data)) (product q0312Data r0005Data)) (product q0314Data r0003Data)) (product q0315Data r0002Data)) (product q0316Data r0001Data)) (product q0317Data r0000Data)) (product q0410Data v0307Data)) (product q0411Data v0306Data)) (product q0412Data v0305Data)) (product q0413Data v0304Data)) (product q0414Data v0303Data)) (product q0415Data v0302Data)) (product q0416Data v0301Data)) (product q0509Data v0208Data)) (product q0510Data v0207Data)) (product q0511Data v0206Data)) (product q0512Data v0205Data)) (product q0513Data v0204Data)) (product q0514Data v0203Data)) (product q0515Data v0202Data)) (product q0516Data v0201Data)) (product q0517Data v0200Data)) (product q0607Data v0110Data)) (product q0608Data v0109Data)) (product q0609Data v0108Data)) (product q0610Data v0107Data)) (product q0611Data v0106Data)) (product q0612Data v0105Data)) (product q0613Data v0104Data)) (product q0614Data v0103Data)) (product q0615Data v0102Data)) (product q0616Data v0101Data)) (product q0617Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0016, q0017, q0115, q0116, q0117, q0214, q0215, q0216, q0217, q0312, q0314, q0315, q0316, q0317, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x17

compact_certificate theorem row3_x18 (y z w : ℂ) :
    q0017 y z w*r0301 y z w +
    q0018 y z w*r0300 y z w +
    q0116 y z w*r0202 y z w +
    q0117 y z w*r0201 y z w +
    q0118 y z w*r0200 y z w +
    q0215 y z w*r0103 y z w +
    q0216 y z w*r0102 y z w +
    q0217 y z w*r0101 y z w +
    q0218 y z w*r0100 y z w +
    q0313 y z w*r0005 y z w +
    q0315 y z w*r0003 y z w +
    q0316 y z w*r0002 y z w +
    q0317 y z w*r0001 y z w +
    q0318 y z w*r0000 y z w +
    q0411 y z w*v0307 y z w +
    q0412 y z w*v0306 y z w +
    q0413 y z w*v0305 y z w +
    q0414 y z w*v0304 y z w +
    q0415 y z w*v0303 y z w +
    q0416 y z w*v0302 y z w +
    q0417 y z w*v0301 y z w +
    q0510 y z w*v0208 y z w +
    q0511 y z w*v0207 y z w +
    q0512 y z w*v0206 y z w +
    q0513 y z w*v0205 y z w +
    q0514 y z w*v0204 y z w +
    q0515 y z w*v0203 y z w +
    q0516 y z w*v0202 y z w +
    q0517 y z w*v0201 y z w +
    q0518 y z w*v0200 y z w +
    q0608 y z w*v0110 y z w +
    q0609 y z w*v0109 y z w +
    q0610 y z w*v0108 y z w +
    q0611 y z w*v0107 y z w +
    q0612 y z w*v0106 y z w +
    q0613 y z w*v0105 y z w +
    q0614 y z w*v0104 y z w +
    q0615 y z w*v0103 y z w +
    q0616 y z w*v0102 y z w +
    q0617 y z w*v0101 y z w +
    q0618 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0017Data r0301Data) (product q0018Data r0300Data)) (product q0116Data r0202Data)) (product q0117Data r0201Data)) (product q0118Data r0200Data)) (product q0215Data r0103Data)) (product q0216Data r0102Data)) (product q0217Data r0101Data)) (product q0218Data r0100Data)) (product q0313Data r0005Data)) (product q0315Data r0003Data)) (product q0316Data r0002Data)) (product q0317Data r0001Data)) (product q0318Data r0000Data)) (product q0411Data v0307Data)) (product q0412Data v0306Data)) (product q0413Data v0305Data)) (product q0414Data v0304Data)) (product q0415Data v0303Data)) (product q0416Data v0302Data)) (product q0417Data v0301Data)) (product q0510Data v0208Data)) (product q0511Data v0207Data)) (product q0512Data v0206Data)) (product q0513Data v0205Data)) (product q0514Data v0204Data)) (product q0515Data v0203Data)) (product q0516Data v0202Data)) (product q0517Data v0201Data)) (product q0518Data v0200Data)) (product q0608Data v0110Data)) (product q0609Data v0109Data)) (product q0610Data v0108Data)) (product q0611Data v0107Data)) (product q0612Data v0106Data)) (product q0613Data v0105Data)) (product q0614Data v0104Data)) (product q0615Data v0103Data)) (product q0616Data v0102Data)) (product q0617Data v0101Data)) (product q0618Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0017, q0018, q0116, q0117, q0118, q0215, q0216, q0217, q0218, q0313, q0315, q0316, q0317, q0318, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x18

compact_certificate theorem row3_x19 (y z w : ℂ) :
    q0018 y z w*r0301 y z w +
    q0019 y z w*r0300 y z w +
    q0117 y z w*r0202 y z w +
    q0118 y z w*r0201 y z w +
    q0119 y z w*r0200 y z w +
    q0216 y z w*r0103 y z w +
    q0217 y z w*r0102 y z w +
    q0218 y z w*r0101 y z w +
    q0219 y z w*r0100 y z w +
    q0314 y z w*r0005 y z w +
    q0316 y z w*r0003 y z w +
    q0317 y z w*r0002 y z w +
    q0318 y z w*r0001 y z w +
    q0319 y z w*r0000 y z w +
    q0412 y z w*v0307 y z w +
    q0413 y z w*v0306 y z w +
    q0414 y z w*v0305 y z w +
    q0415 y z w*v0304 y z w +
    q0416 y z w*v0303 y z w +
    q0417 y z w*v0302 y z w +
    q0418 y z w*v0301 y z w +
    q0511 y z w*v0208 y z w +
    q0512 y z w*v0207 y z w +
    q0513 y z w*v0206 y z w +
    q0514 y z w*v0205 y z w +
    q0515 y z w*v0204 y z w +
    q0516 y z w*v0203 y z w +
    q0517 y z w*v0202 y z w +
    q0518 y z w*v0201 y z w +
    q0519 y z w*v0200 y z w +
    q0609 y z w*v0110 y z w +
    q0610 y z w*v0109 y z w +
    q0611 y z w*v0108 y z w +
    q0612 y z w*v0107 y z w +
    q0613 y z w*v0106 y z w +
    q0614 y z w*v0105 y z w +
    q0615 y z w*v0104 y z w +
    q0616 y z w*v0103 y z w +
    q0617 y z w*v0102 y z w +
    q0618 y z w*v0101 y z w +
    q0619 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0018Data r0301Data) (product q0019Data r0300Data)) (product q0117Data r0202Data)) (product q0118Data r0201Data)) (product q0119Data r0200Data)) (product q0216Data r0103Data)) (product q0217Data r0102Data)) (product q0218Data r0101Data)) (product q0219Data r0100Data)) (product q0314Data r0005Data)) (product q0316Data r0003Data)) (product q0317Data r0002Data)) (product q0318Data r0001Data)) (product q0319Data r0000Data)) (product q0412Data v0307Data)) (product q0413Data v0306Data)) (product q0414Data v0305Data)) (product q0415Data v0304Data)) (product q0416Data v0303Data)) (product q0417Data v0302Data)) (product q0418Data v0301Data)) (product q0511Data v0208Data)) (product q0512Data v0207Data)) (product q0513Data v0206Data)) (product q0514Data v0205Data)) (product q0515Data v0204Data)) (product q0516Data v0203Data)) (product q0517Data v0202Data)) (product q0518Data v0201Data)) (product q0519Data v0200Data)) (product q0609Data v0110Data)) (product q0610Data v0109Data)) (product q0611Data v0108Data)) (product q0612Data v0107Data)) (product q0613Data v0106Data)) (product q0614Data v0105Data)) (product q0615Data v0104Data)) (product q0616Data v0103Data)) (product q0617Data v0102Data)) (product q0618Data v0101Data)) (product q0619Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0018, q0019, q0117, q0118, q0119, q0216, q0217, q0218, q0219, q0314, q0316, q0317, q0318, q0319, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x19

compact_certificate theorem row3_x20 (y z w : ℂ) :
    q0019 y z w*r0301 y z w +
    q0020 y z w*r0300 y z w +
    q0118 y z w*r0202 y z w +
    q0119 y z w*r0201 y z w +
    q0120 y z w*r0200 y z w +
    q0217 y z w*r0103 y z w +
    q0218 y z w*r0102 y z w +
    q0219 y z w*r0101 y z w +
    q0220 y z w*r0100 y z w +
    q0315 y z w*r0005 y z w +
    q0317 y z w*r0003 y z w +
    q0318 y z w*r0002 y z w +
    q0319 y z w*r0001 y z w +
    q0320 y z w*r0000 y z w +
    q0413 y z w*v0307 y z w +
    q0414 y z w*v0306 y z w +
    q0415 y z w*v0305 y z w +
    q0416 y z w*v0304 y z w +
    q0417 y z w*v0303 y z w +
    q0418 y z w*v0302 y z w +
    q0419 y z w*v0301 y z w +
    q0512 y z w*v0208 y z w +
    q0513 y z w*v0207 y z w +
    q0514 y z w*v0206 y z w +
    q0515 y z w*v0205 y z w +
    q0516 y z w*v0204 y z w +
    q0517 y z w*v0203 y z w +
    q0518 y z w*v0202 y z w +
    q0519 y z w*v0201 y z w +
    q0520 y z w*v0200 y z w +
    q0610 y z w*v0110 y z w +
    q0611 y z w*v0109 y z w +
    q0612 y z w*v0108 y z w +
    q0613 y z w*v0107 y z w +
    q0614 y z w*v0106 y z w +
    q0615 y z w*v0105 y z w +
    q0616 y z w*v0104 y z w +
    q0617 y z w*v0103 y z w +
    q0618 y z w*v0102 y z w +
    q0619 y z w*v0101 y z w +
    q0620 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0019Data r0301Data) (product q0020Data r0300Data)) (product q0118Data r0202Data)) (product q0119Data r0201Data)) (product q0120Data r0200Data)) (product q0217Data r0103Data)) (product q0218Data r0102Data)) (product q0219Data r0101Data)) (product q0220Data r0100Data)) (product q0315Data r0005Data)) (product q0317Data r0003Data)) (product q0318Data r0002Data)) (product q0319Data r0001Data)) (product q0320Data r0000Data)) (product q0413Data v0307Data)) (product q0414Data v0306Data)) (product q0415Data v0305Data)) (product q0416Data v0304Data)) (product q0417Data v0303Data)) (product q0418Data v0302Data)) (product q0419Data v0301Data)) (product q0512Data v0208Data)) (product q0513Data v0207Data)) (product q0514Data v0206Data)) (product q0515Data v0205Data)) (product q0516Data v0204Data)) (product q0517Data v0203Data)) (product q0518Data v0202Data)) (product q0519Data v0201Data)) (product q0520Data v0200Data)) (product q0610Data v0110Data)) (product q0611Data v0109Data)) (product q0612Data v0108Data)) (product q0613Data v0107Data)) (product q0614Data v0106Data)) (product q0615Data v0105Data)) (product q0616Data v0104Data)) (product q0617Data v0103Data)) (product q0618Data v0102Data)) (product q0619Data v0101Data)) (product q0620Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0019, q0020, q0118, q0119, q0120, q0217, q0218, q0219, q0220, q0315, q0317, q0318, q0319, q0320, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x20

compact_certificate theorem row3_x21 (y z w : ℂ) :
    q0020 y z w*r0301 y z w +
    q0021 y z w*r0300 y z w +
    q0119 y z w*r0202 y z w +
    q0120 y z w*r0201 y z w +
    q0121 y z w*r0200 y z w +
    q0218 y z w*r0103 y z w +
    q0219 y z w*r0102 y z w +
    q0220 y z w*r0101 y z w +
    q0221 y z w*r0100 y z w +
    q0316 y z w*r0005 y z w +
    q0318 y z w*r0003 y z w +
    q0319 y z w*r0002 y z w +
    q0320 y z w*r0001 y z w +
    q0321 y z w*r0000 y z w +
    q0414 y z w*v0307 y z w +
    q0415 y z w*v0306 y z w +
    q0416 y z w*v0305 y z w +
    q0417 y z w*v0304 y z w +
    q0418 y z w*v0303 y z w +
    q0419 y z w*v0302 y z w +
    q0420 y z w*v0301 y z w +
    q0513 y z w*v0208 y z w +
    q0514 y z w*v0207 y z w +
    q0515 y z w*v0206 y z w +
    q0516 y z w*v0205 y z w +
    q0517 y z w*v0204 y z w +
    q0518 y z w*v0203 y z w +
    q0519 y z w*v0202 y z w +
    q0520 y z w*v0201 y z w +
    q0521 y z w*v0200 y z w +
    q0611 y z w*v0110 y z w +
    q0612 y z w*v0109 y z w +
    q0613 y z w*v0108 y z w +
    q0614 y z w*v0107 y z w +
    q0615 y z w*v0106 y z w +
    q0616 y z w*v0105 y z w +
    q0617 y z w*v0104 y z w +
    q0618 y z w*v0103 y z w +
    q0619 y z w*v0102 y z w +
    q0620 y z w*v0101 y z w +
    q0621 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0020Data r0301Data) (product q0021Data r0300Data)) (product q0119Data r0202Data)) (product q0120Data r0201Data)) (product q0121Data r0200Data)) (product q0218Data r0103Data)) (product q0219Data r0102Data)) (product q0220Data r0101Data)) (product q0221Data r0100Data)) (product q0316Data r0005Data)) (product q0318Data r0003Data)) (product q0319Data r0002Data)) (product q0320Data r0001Data)) (product q0321Data r0000Data)) (product q0414Data v0307Data)) (product q0415Data v0306Data)) (product q0416Data v0305Data)) (product q0417Data v0304Data)) (product q0418Data v0303Data)) (product q0419Data v0302Data)) (product q0420Data v0301Data)) (product q0513Data v0208Data)) (product q0514Data v0207Data)) (product q0515Data v0206Data)) (product q0516Data v0205Data)) (product q0517Data v0204Data)) (product q0518Data v0203Data)) (product q0519Data v0202Data)) (product q0520Data v0201Data)) (product q0521Data v0200Data)) (product q0611Data v0110Data)) (product q0612Data v0109Data)) (product q0613Data v0108Data)) (product q0614Data v0107Data)) (product q0615Data v0106Data)) (product q0616Data v0105Data)) (product q0617Data v0104Data)) (product q0618Data v0103Data)) (product q0619Data v0102Data)) (product q0620Data v0101Data)) (product q0621Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0020, q0021, q0119, q0120, q0121, q0218, q0219, q0220, q0221, q0316, q0318, q0319, q0320, q0321, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x21

compact_certificate theorem row3_x22 (y z w : ℂ) :
    q0021 y z w*r0301 y z w +
    q0022 y z w*r0300 y z w +
    q0120 y z w*r0202 y z w +
    q0121 y z w*r0201 y z w +
    q0122 y z w*r0200 y z w +
    q0219 y z w*r0103 y z w +
    q0220 y z w*r0102 y z w +
    q0221 y z w*r0101 y z w +
    q0222 y z w*r0100 y z w +
    q0317 y z w*r0005 y z w +
    q0319 y z w*r0003 y z w +
    q0320 y z w*r0002 y z w +
    q0321 y z w*r0001 y z w +
    q0322 y z w*r0000 y z w +
    q0415 y z w*v0307 y z w +
    q0416 y z w*v0306 y z w +
    q0417 y z w*v0305 y z w +
    q0418 y z w*v0304 y z w +
    q0419 y z w*v0303 y z w +
    q0420 y z w*v0302 y z w +
    q0421 y z w*v0301 y z w +
    q0514 y z w*v0208 y z w +
    q0515 y z w*v0207 y z w +
    q0516 y z w*v0206 y z w +
    q0517 y z w*v0205 y z w +
    q0518 y z w*v0204 y z w +
    q0519 y z w*v0203 y z w +
    q0520 y z w*v0202 y z w +
    q0521 y z w*v0201 y z w +
    q0522 y z w*v0200 y z w +
    q0612 y z w*v0110 y z w +
    q0613 y z w*v0109 y z w +
    q0614 y z w*v0108 y z w +
    q0615 y z w*v0107 y z w +
    q0616 y z w*v0106 y z w +
    q0617 y z w*v0105 y z w +
    q0618 y z w*v0104 y z w +
    q0619 y z w*v0103 y z w +
    q0620 y z w*v0102 y z w +
    q0621 y z w*v0101 y z w +
    q0622 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0021Data r0301Data) (product q0022Data r0300Data)) (product q0120Data r0202Data)) (product q0121Data r0201Data)) (product q0122Data r0200Data)) (product q0219Data r0103Data)) (product q0220Data r0102Data)) (product q0221Data r0101Data)) (product q0222Data r0100Data)) (product q0317Data r0005Data)) (product q0319Data r0003Data)) (product q0320Data r0002Data)) (product q0321Data r0001Data)) (product q0322Data r0000Data)) (product q0415Data v0307Data)) (product q0416Data v0306Data)) (product q0417Data v0305Data)) (product q0418Data v0304Data)) (product q0419Data v0303Data)) (product q0420Data v0302Data)) (product q0421Data v0301Data)) (product q0514Data v0208Data)) (product q0515Data v0207Data)) (product q0516Data v0206Data)) (product q0517Data v0205Data)) (product q0518Data v0204Data)) (product q0519Data v0203Data)) (product q0520Data v0202Data)) (product q0521Data v0201Data)) (product q0522Data v0200Data)) (product q0612Data v0110Data)) (product q0613Data v0109Data)) (product q0614Data v0108Data)) (product q0615Data v0107Data)) (product q0616Data v0106Data)) (product q0617Data v0105Data)) (product q0618Data v0104Data)) (product q0619Data v0103Data)) (product q0620Data v0102Data)) (product q0621Data v0101Data)) (product q0622Data v0100Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0021, q0022, q0120, q0121, q0122, q0219, q0220, q0221, q0222, q0317, q0319, q0320, q0321, q0322, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x22

compact_certificate theorem row3_x23 (y z w : ℂ) :
    q0022 y z w*r0301 y z w +
    q0023 y z w*r0300 y z w +
    q0121 y z w*r0202 y z w +
    q0122 y z w*r0201 y z w +
    q0123 y z w*r0200 y z w +
    q0220 y z w*r0103 y z w +
    q0221 y z w*r0102 y z w +
    q0222 y z w*r0101 y z w +
    q0223 y z w*r0100 y z w +
    q0318 y z w*r0005 y z w +
    q0320 y z w*r0003 y z w +
    q0321 y z w*r0002 y z w +
    q0322 y z w*r0001 y z w +
    q0323 y z w*r0000 y z w +
    q0416 y z w*v0307 y z w +
    q0417 y z w*v0306 y z w +
    q0418 y z w*v0305 y z w +
    q0419 y z w*v0304 y z w +
    q0420 y z w*v0303 y z w +
    q0421 y z w*v0302 y z w +
    q0422 y z w*v0301 y z w +
    q0515 y z w*v0208 y z w +
    q0516 y z w*v0207 y z w +
    q0517 y z w*v0206 y z w +
    q0518 y z w*v0205 y z w +
    q0519 y z w*v0204 y z w +
    q0520 y z w*v0203 y z w +
    q0521 y z w*v0202 y z w +
    q0522 y z w*v0201 y z w +
    q0523 y z w*v0200 y z w +
    q0613 y z w*v0110 y z w +
    q0614 y z w*v0109 y z w +
    q0615 y z w*v0108 y z w +
    q0616 y z w*v0107 y z w +
    q0617 y z w*v0106 y z w +
    q0618 y z w*v0105 y z w +
    q0619 y z w*v0104 y z w +
    q0620 y z w*v0103 y z w +
    q0621 y z w*v0102 y z w +
    q0622 y z w*v0101 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0022Data r0301Data) (product q0023Data r0300Data)) (product q0121Data r0202Data)) (product q0122Data r0201Data)) (product q0123Data r0200Data)) (product q0220Data r0103Data)) (product q0221Data r0102Data)) (product q0222Data r0101Data)) (product q0223Data r0100Data)) (product q0318Data r0005Data)) (product q0320Data r0003Data)) (product q0321Data r0002Data)) (product q0322Data r0001Data)) (product q0323Data r0000Data)) (product q0416Data v0307Data)) (product q0417Data v0306Data)) (product q0418Data v0305Data)) (product q0419Data v0304Data)) (product q0420Data v0303Data)) (product q0421Data v0302Data)) (product q0422Data v0301Data)) (product q0515Data v0208Data)) (product q0516Data v0207Data)) (product q0517Data v0206Data)) (product q0518Data v0205Data)) (product q0519Data v0204Data)) (product q0520Data v0203Data)) (product q0521Data v0202Data)) (product q0522Data v0201Data)) (product q0523Data v0200Data)) (product q0613Data v0110Data)) (product q0614Data v0109Data)) (product q0615Data v0108Data)) (product q0616Data v0107Data)) (product q0617Data v0106Data)) (product q0618Data v0105Data)) (product q0619Data v0104Data)) (product q0620Data v0103Data)) (product q0621Data v0102Data)) (product q0622Data v0101Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0022, q0023, q0121, q0122, q0123, q0220, q0221, q0222, q0223, q0318, q0320, q0321, q0322, q0323, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x23

compact_certificate theorem row3_x24 (y z w : ℂ) :
    q0023 y z w*r0301 y z w +
    q0024 y z w*r0300 y z w +
    q0122 y z w*r0202 y z w +
    q0123 y z w*r0201 y z w +
    q0124 y z w*r0200 y z w +
    q0221 y z w*r0103 y z w +
    q0222 y z w*r0102 y z w +
    q0223 y z w*r0101 y z w +
    q0224 y z w*r0100 y z w +
    q0319 y z w*r0005 y z w +
    q0321 y z w*r0003 y z w +
    q0322 y z w*r0002 y z w +
    q0323 y z w*r0001 y z w +
    q0324 y z w*r0000 y z w +
    q0417 y z w*v0307 y z w +
    q0418 y z w*v0306 y z w +
    q0419 y z w*v0305 y z w +
    q0420 y z w*v0304 y z w +
    q0421 y z w*v0303 y z w +
    q0422 y z w*v0302 y z w +
    q0423 y z w*v0301 y z w +
    q0516 y z w*v0208 y z w +
    q0517 y z w*v0207 y z w +
    q0518 y z w*v0206 y z w +
    q0519 y z w*v0205 y z w +
    q0520 y z w*v0204 y z w +
    q0521 y z w*v0203 y z w +
    q0522 y z w*v0202 y z w +
    q0523 y z w*v0201 y z w +
    q0614 y z w*v0110 y z w +
    q0615 y z w*v0109 y z w +
    q0616 y z w*v0108 y z w +
    q0617 y z w*v0107 y z w +
    q0618 y z w*v0106 y z w +
    q0619 y z w*v0105 y z w +
    q0620 y z w*v0104 y z w +
    q0621 y z w*v0103 y z w +
    q0622 y z w*v0102 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0023Data r0301Data) (product q0024Data r0300Data)) (product q0122Data r0202Data)) (product q0123Data r0201Data)) (product q0124Data r0200Data)) (product q0221Data r0103Data)) (product q0222Data r0102Data)) (product q0223Data r0101Data)) (product q0224Data r0100Data)) (product q0319Data r0005Data)) (product q0321Data r0003Data)) (product q0322Data r0002Data)) (product q0323Data r0001Data)) (product q0324Data r0000Data)) (product q0417Data v0307Data)) (product q0418Data v0306Data)) (product q0419Data v0305Data)) (product q0420Data v0304Data)) (product q0421Data v0303Data)) (product q0422Data v0302Data)) (product q0423Data v0301Data)) (product q0516Data v0208Data)) (product q0517Data v0207Data)) (product q0518Data v0206Data)) (product q0519Data v0205Data)) (product q0520Data v0204Data)) (product q0521Data v0203Data)) (product q0522Data v0202Data)) (product q0523Data v0201Data)) (product q0614Data v0110Data)) (product q0615Data v0109Data)) (product q0616Data v0108Data)) (product q0617Data v0107Data)) (product q0618Data v0106Data)) (product q0619Data v0105Data)) (product q0620Data v0104Data)) (product q0621Data v0103Data)) (product q0622Data v0102Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0023, q0024, q0122, q0123, q0124, q0221, q0222, q0223, q0224, q0319, q0321, q0322, q0323, q0324, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x24

compact_certificate theorem row3_x25 (y z w : ℂ) :
    q0024 y z w*r0301 y z w +
    q0025 y z w*r0300 y z w +
    q0123 y z w*r0202 y z w +
    q0124 y z w*r0201 y z w +
    q0125 y z w*r0200 y z w +
    q0222 y z w*r0103 y z w +
    q0223 y z w*r0102 y z w +
    q0224 y z w*r0101 y z w +
    q0225 y z w*r0100 y z w +
    q0320 y z w*r0005 y z w +
    q0322 y z w*r0003 y z w +
    q0323 y z w*r0002 y z w +
    q0324 y z w*r0001 y z w +
    q0325 y z w*r0000 y z w +
    q0418 y z w*v0307 y z w +
    q0419 y z w*v0306 y z w +
    q0420 y z w*v0305 y z w +
    q0421 y z w*v0304 y z w +
    q0422 y z w*v0303 y z w +
    q0423 y z w*v0302 y z w +
    q0424 y z w*v0301 y z w +
    q0517 y z w*v0208 y z w +
    q0518 y z w*v0207 y z w +
    q0519 y z w*v0206 y z w +
    q0520 y z w*v0205 y z w +
    q0521 y z w*v0204 y z w +
    q0522 y z w*v0203 y z w +
    q0523 y z w*v0202 y z w +
    q0615 y z w*v0110 y z w +
    q0616 y z w*v0109 y z w +
    q0617 y z w*v0108 y z w +
    q0618 y z w*v0107 y z w +
    q0619 y z w*v0106 y z w +
    q0620 y z w*v0105 y z w +
    q0621 y z w*v0104 y z w +
    q0622 y z w*v0103 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0024Data r0301Data) (product q0025Data r0300Data)) (product q0123Data r0202Data)) (product q0124Data r0201Data)) (product q0125Data r0200Data)) (product q0222Data r0103Data)) (product q0223Data r0102Data)) (product q0224Data r0101Data)) (product q0225Data r0100Data)) (product q0320Data r0005Data)) (product q0322Data r0003Data)) (product q0323Data r0002Data)) (product q0324Data r0001Data)) (product q0325Data r0000Data)) (product q0418Data v0307Data)) (product q0419Data v0306Data)) (product q0420Data v0305Data)) (product q0421Data v0304Data)) (product q0422Data v0303Data)) (product q0423Data v0302Data)) (product q0424Data v0301Data)) (product q0517Data v0208Data)) (product q0518Data v0207Data)) (product q0519Data v0206Data)) (product q0520Data v0205Data)) (product q0521Data v0204Data)) (product q0522Data v0203Data)) (product q0523Data v0202Data)) (product q0615Data v0110Data)) (product q0616Data v0109Data)) (product q0617Data v0108Data)) (product q0618Data v0107Data)) (product q0619Data v0106Data)) (product q0620Data v0105Data)) (product q0621Data v0104Data)) (product q0622Data v0103Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0024, q0025, q0123, q0124, q0125, q0222, q0223, q0224, q0225, q0320, q0322, q0323, q0324, q0325, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x25

compact_certificate theorem row3_x26 (y z w : ℂ) :
    q0025 y z w*r0301 y z w +
    q0026 y z w*r0300 y z w +
    q0124 y z w*r0202 y z w +
    q0125 y z w*r0201 y z w +
    q0126 y z w*r0200 y z w +
    q0223 y z w*r0103 y z w +
    q0224 y z w*r0102 y z w +
    q0225 y z w*r0101 y z w +
    q0226 y z w*r0100 y z w +
    q0321 y z w*r0005 y z w +
    q0323 y z w*r0003 y z w +
    q0324 y z w*r0002 y z w +
    q0325 y z w*r0001 y z w +
    q0326 y z w*r0000 y z w +
    q0419 y z w*v0307 y z w +
    q0420 y z w*v0306 y z w +
    q0421 y z w*v0305 y z w +
    q0422 y z w*v0304 y z w +
    q0423 y z w*v0303 y z w +
    q0424 y z w*v0302 y z w +
    q0518 y z w*v0208 y z w +
    q0519 y z w*v0207 y z w +
    q0520 y z w*v0206 y z w +
    q0521 y z w*v0205 y z w +
    q0522 y z w*v0204 y z w +
    q0523 y z w*v0203 y z w +
    q0616 y z w*v0110 y z w +
    q0617 y z w*v0109 y z w +
    q0618 y z w*v0108 y z w +
    q0619 y z w*v0107 y z w +
    q0620 y z w*v0106 y z w +
    q0621 y z w*v0105 y z w +
    q0622 y z w*v0104 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0025Data r0301Data) (product q0026Data r0300Data)) (product q0124Data r0202Data)) (product q0125Data r0201Data)) (product q0126Data r0200Data)) (product q0223Data r0103Data)) (product q0224Data r0102Data)) (product q0225Data r0101Data)) (product q0226Data r0100Data)) (product q0321Data r0005Data)) (product q0323Data r0003Data)) (product q0324Data r0002Data)) (product q0325Data r0001Data)) (product q0326Data r0000Data)) (product q0419Data v0307Data)) (product q0420Data v0306Data)) (product q0421Data v0305Data)) (product q0422Data v0304Data)) (product q0423Data v0303Data)) (product q0424Data v0302Data)) (product q0518Data v0208Data)) (product q0519Data v0207Data)) (product q0520Data v0206Data)) (product q0521Data v0205Data)) (product q0522Data v0204Data)) (product q0523Data v0203Data)) (product q0616Data v0110Data)) (product q0617Data v0109Data)) (product q0618Data v0108Data)) (product q0619Data v0107Data)) (product q0620Data v0106Data)) (product q0621Data v0105Data)) (product q0622Data v0104Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0025, q0026, q0124, q0125, q0126, q0223, q0224, q0225, q0226, q0321, q0323, q0324, q0325, q0326, q0419, q0420, q0421, q0422, q0423, q0424, q0518, q0519, q0520, q0521, q0522, q0523, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0203, v0204, v0205, v0206, v0207, v0208, v0302, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x26

compact_certificate theorem row3_x27 (y z w : ℂ) :
    q0026 y z w*r0301 y z w +
    q0027 y z w*r0300 y z w +
    q0125 y z w*r0202 y z w +
    q0126 y z w*r0201 y z w +
    q0127 y z w*r0200 y z w +
    q0224 y z w*r0103 y z w +
    q0225 y z w*r0102 y z w +
    q0226 y z w*r0101 y z w +
    q0227 y z w*r0100 y z w +
    q0322 y z w*r0005 y z w +
    q0324 y z w*r0003 y z w +
    q0325 y z w*r0002 y z w +
    q0326 y z w*r0001 y z w +
    q0327 y z w*r0000 y z w +
    q0420 y z w*v0307 y z w +
    q0421 y z w*v0306 y z w +
    q0422 y z w*v0305 y z w +
    q0423 y z w*v0304 y z w +
    q0424 y z w*v0303 y z w +
    q0519 y z w*v0208 y z w +
    q0520 y z w*v0207 y z w +
    q0521 y z w*v0206 y z w +
    q0522 y z w*v0205 y z w +
    q0523 y z w*v0204 y z w +
    q0617 y z w*v0110 y z w +
    q0618 y z w*v0109 y z w +
    q0619 y z w*v0108 y z w +
    q0620 y z w*v0107 y z w +
    q0621 y z w*v0106 y z w +
    q0622 y z w*v0105 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0026Data r0301Data) (product q0027Data r0300Data)) (product q0125Data r0202Data)) (product q0126Data r0201Data)) (product q0127Data r0200Data)) (product q0224Data r0103Data)) (product q0225Data r0102Data)) (product q0226Data r0101Data)) (product q0227Data r0100Data)) (product q0322Data r0005Data)) (product q0324Data r0003Data)) (product q0325Data r0002Data)) (product q0326Data r0001Data)) (product q0327Data r0000Data)) (product q0420Data v0307Data)) (product q0421Data v0306Data)) (product q0422Data v0305Data)) (product q0423Data v0304Data)) (product q0424Data v0303Data)) (product q0519Data v0208Data)) (product q0520Data v0207Data)) (product q0521Data v0206Data)) (product q0522Data v0205Data)) (product q0523Data v0204Data)) (product q0617Data v0110Data)) (product q0618Data v0109Data)) (product q0619Data v0108Data)) (product q0620Data v0107Data)) (product q0621Data v0106Data)) (product q0622Data v0105Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0026, q0027, q0125, q0126, q0127, q0224, q0225, q0226, q0227, q0322, q0324, q0325, q0326, q0327, q0420, q0421, q0422, q0423, q0424, q0519, q0520, q0521, q0522, q0523, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0105, v0106, v0107, v0108, v0109, v0110, v0204, v0205, v0206, v0207, v0208, v0303, v0304, v0305, v0306, v0307] using he

#print axioms row3_x27

compact_certificate theorem row3_x28 (y z w : ℂ) :
    q0027 y z w*r0301 y z w +
    q0028 y z w*r0300 y z w +
    q0126 y z w*r0202 y z w +
    q0127 y z w*r0201 y z w +
    q0128 y z w*r0200 y z w +
    q0225 y z w*r0103 y z w +
    q0226 y z w*r0102 y z w +
    q0227 y z w*r0101 y z w +
    q0228 y z w*r0100 y z w +
    q0323 y z w*r0005 y z w +
    q0325 y z w*r0003 y z w +
    q0326 y z w*r0002 y z w +
    q0327 y z w*r0001 y z w +
    q0421 y z w*v0307 y z w +
    q0422 y z w*v0306 y z w +
    q0423 y z w*v0305 y z w +
    q0424 y z w*v0304 y z w +
    q0520 y z w*v0208 y z w +
    q0521 y z w*v0207 y z w +
    q0522 y z w*v0206 y z w +
    q0523 y z w*v0205 y z w +
    q0618 y z w*v0110 y z w +
    q0619 y z w*v0109 y z w +
    q0620 y z w*v0108 y z w +
    q0621 y z w*v0107 y z w +
    q0622 y z w*v0106 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0027Data r0301Data) (product q0028Data r0300Data)) (product q0126Data r0202Data)) (product q0127Data r0201Data)) (product q0128Data r0200Data)) (product q0225Data r0103Data)) (product q0226Data r0102Data)) (product q0227Data r0101Data)) (product q0228Data r0100Data)) (product q0323Data r0005Data)) (product q0325Data r0003Data)) (product q0326Data r0002Data)) (product q0327Data r0001Data)) (product q0421Data v0307Data)) (product q0422Data v0306Data)) (product q0423Data v0305Data)) (product q0424Data v0304Data)) (product q0520Data v0208Data)) (product q0521Data v0207Data)) (product q0522Data v0206Data)) (product q0523Data v0205Data)) (product q0618Data v0110Data)) (product q0619Data v0109Data)) (product q0620Data v0108Data)) (product q0621Data v0107Data)) (product q0622Data v0106Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0027, q0028, q0126, q0127, q0128, q0225, q0226, q0227, q0228, q0323, q0325, q0326, q0327, q0421, q0422, q0423, q0424, q0520, q0521, q0522, q0523, q0618, q0619, q0620, q0621, q0622, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0106, v0107, v0108, v0109, v0110, v0205, v0206, v0207, v0208, v0304, v0305, v0306, v0307] using he

#print axioms row3_x28

compact_certificate theorem row3_x29 (y z w : ℂ) :
    q0028 y z w*r0301 y z w +
    q0029 y z w*r0300 y z w +
    q0127 y z w*r0202 y z w +
    q0128 y z w*r0201 y z w +
    q0129 y z w*r0200 y z w +
    q0226 y z w*r0103 y z w +
    q0227 y z w*r0102 y z w +
    q0228 y z w*r0101 y z w +
    q0324 y z w*r0005 y z w +
    q0326 y z w*r0003 y z w +
    q0327 y z w*r0002 y z w +
    q0422 y z w*v0307 y z w +
    q0423 y z w*v0306 y z w +
    q0424 y z w*v0305 y z w +
    q0521 y z w*v0208 y z w +
    q0522 y z w*v0207 y z w +
    q0523 y z w*v0206 y z w +
    q0619 y z w*v0110 y z w +
    q0620 y z w*v0109 y z w +
    q0621 y z w*v0108 y z w +
    q0622 y z w*v0107 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0028Data r0301Data) (product q0029Data r0300Data)) (product q0127Data r0202Data)) (product q0128Data r0201Data)) (product q0129Data r0200Data)) (product q0226Data r0103Data)) (product q0227Data r0102Data)) (product q0228Data r0101Data)) (product q0324Data r0005Data)) (product q0326Data r0003Data)) (product q0327Data r0002Data)) (product q0422Data v0307Data)) (product q0423Data v0306Data)) (product q0424Data v0305Data)) (product q0521Data v0208Data)) (product q0522Data v0207Data)) (product q0523Data v0206Data)) (product q0619Data v0110Data)) (product q0620Data v0109Data)) (product q0621Data v0108Data)) (product q0622Data v0107Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0028, q0029, q0127, q0128, q0129, q0226, q0227, q0228, q0324, q0326, q0327, q0422, q0423, q0424, q0521, q0522, q0523, q0619, q0620, q0621, q0622, r0002, r0003, r0005, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0107, v0108, v0109, v0110, v0206, v0207, v0208, v0305, v0306, v0307] using he

#print axioms row3_x29

compact_certificate theorem row3_x30 (y z w : ℂ) :
    q0029 y z w*r0301 y z w +
    q0030 y z w*r0300 y z w +
    q0128 y z w*r0202 y z w +
    q0129 y z w*r0201 y z w +
    q0227 y z w*r0103 y z w +
    q0228 y z w*r0102 y z w +
    q0325 y z w*r0005 y z w +
    q0327 y z w*r0003 y z w +
    q0423 y z w*v0307 y z w +
    q0424 y z w*v0306 y z w +
    q0522 y z w*v0208 y z w +
    q0523 y z w*v0207 y z w +
    q0620 y z w*v0110 y z w +
    q0621 y z w*v0109 y z w +
    q0622 y z w*v0108 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0029Data r0301Data) (product q0030Data r0300Data)) (product q0128Data r0202Data)) (product q0129Data r0201Data)) (product q0227Data r0103Data)) (product q0228Data r0102Data)) (product q0325Data r0005Data)) (product q0327Data r0003Data)) (product q0423Data v0307Data)) (product q0424Data v0306Data)) (product q0522Data v0208Data)) (product q0523Data v0207Data)) (product q0620Data v0110Data)) (product q0621Data v0109Data)) (product q0622Data v0108Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0029, q0030, q0128, q0129, q0227, q0228, q0325, q0327, q0423, q0424, q0522, q0523, q0620, q0621, q0622, r0003, r0005, r0102, r0103, r0201, r0202, r0300, r0301, v0108, v0109, v0110, v0207, v0208, v0306, v0307] using he

#print axioms row3_x30

compact_certificate theorem row3_x31 (y z w : ℂ) :
    q0030 y z w*r0301 y z w +
    q0129 y z w*r0202 y z w +
    q0228 y z w*r0103 y z w +
    q0326 y z w*r0005 y z w +
    q0424 y z w*v0307 y z w +
    q0523 y z w*v0208 y z w +
    q0621 y z w*v0110 y z w +
    q0622 y z w*v0109 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0030Data r0301Data) (product q0129Data r0202Data)) (product q0228Data r0103Data)) (product q0326Data r0005Data)) (product q0424Data v0307Data)) (product q0523Data v0208Data)) (product q0621Data v0110Data)) (product q0622Data v0109Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0030, q0129, q0228, q0326, q0424, q0523, q0621, q0622, r0005, r0103, r0202, r0301, v0109, v0110, v0208, v0307] using he

#print axioms row3_x31

compact_certificate theorem row3_x32 (y z w : ℂ) :
    q0327 y z w*r0005 y z w +
    q0622 y z w*v0110 y z w=0 := by
  have h : (merge (product q0327Data r0005Data) (product q0622Data v0110Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0327, q0622, r0005, v0110] using he

#print axioms row3_x32

compact_certificate theorem row3_coefficient00 (y z w : ℂ) : (rowPoly3 y z w).coeff 0=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x00 y z w

#print axioms row3_coefficient00

compact_certificate theorem row3_coefficient01 (y z w : ℂ) : (rowPoly3 y z w).coeff 1=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x01 y z w

#print axioms row3_coefficient01

compact_certificate theorem row3_coefficient02 (y z w : ℂ) : (rowPoly3 y z w).coeff 2=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x02 y z w

#print axioms row3_coefficient02

compact_certificate theorem row3_coefficient03 (y z w : ℂ) : (rowPoly3 y z w).coeff 3=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x03 y z w

#print axioms row3_coefficient03

compact_certificate theorem row3_coefficient04 (y z w : ℂ) : (rowPoly3 y z w).coeff 4=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x04 y z w

#print axioms row3_coefficient04

compact_certificate theorem row3_coefficient05 (y z w : ℂ) : (rowPoly3 y z w).coeff 5=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x05 y z w

#print axioms row3_coefficient05

compact_certificate theorem row3_coefficient06 (y z w : ℂ) : (rowPoly3 y z w).coeff 6=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x06 y z w

#print axioms row3_coefficient06

compact_certificate theorem row3_coefficient07 (y z w : ℂ) : (rowPoly3 y z w).coeff 7=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x07 y z w

#print axioms row3_coefficient07

compact_certificate theorem row3_coefficient08 (y z w : ℂ) : (rowPoly3 y z w).coeff 8=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x08 y z w

#print axioms row3_coefficient08

compact_certificate theorem row3_coefficient09 (y z w : ℂ) : (rowPoly3 y z w).coeff 9=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x09 y z w

#print axioms row3_coefficient09

compact_certificate theorem row3_coefficient10 (y z w : ℂ) : (rowPoly3 y z w).coeff 10=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x10 y z w

#print axioms row3_coefficient10

compact_certificate theorem row3_coefficient11 (y z w : ℂ) : (rowPoly3 y z w).coeff 11=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x11 y z w

#print axioms row3_coefficient11

compact_certificate theorem row3_coefficient12 (y z w : ℂ) : (rowPoly3 y z w).coeff 12=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x12 y z w

#print axioms row3_coefficient12

compact_certificate theorem row3_coefficient13 (y z w : ℂ) : (rowPoly3 y z w).coeff 13=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x13 y z w

#print axioms row3_coefficient13

compact_certificate theorem row3_coefficient14 (y z w : ℂ) : (rowPoly3 y z w).coeff 14=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x14 y z w

#print axioms row3_coefficient14

compact_certificate theorem row3_coefficient15 (y z w : ℂ) : (rowPoly3 y z w).coeff 15=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x15 y z w

#print axioms row3_coefficient15

compact_certificate theorem row3_coefficient16 (y z w : ℂ) : (rowPoly3 y z w).coeff 16=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x16 y z w

#print axioms row3_coefficient16

compact_certificate theorem row3_coefficient17 (y z w : ℂ) : (rowPoly3 y z w).coeff 17=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x17 y z w

#print axioms row3_coefficient17

compact_certificate theorem row3_coefficient18 (y z w : ℂ) : (rowPoly3 y z w).coeff 18=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x18 y z w

#print axioms row3_coefficient18

compact_certificate theorem row3_coefficient19 (y z w : ℂ) : (rowPoly3 y z w).coeff 19=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x19 y z w

#print axioms row3_coefficient19

compact_certificate theorem row3_coefficient20 (y z w : ℂ) : (rowPoly3 y z w).coeff 20=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x20 y z w

#print axioms row3_coefficient20

compact_certificate theorem row3_coefficient21 (y z w : ℂ) : (rowPoly3 y z w).coeff 21=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x21 y z w

#print axioms row3_coefficient21

compact_certificate theorem row3_coefficient22 (y z w : ℂ) : (rowPoly3 y z w).coeff 22=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x22 y z w

#print axioms row3_coefficient22

compact_certificate theorem row3_coefficient23 (y z w : ℂ) : (rowPoly3 y z w).coeff 23=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x23 y z w

#print axioms row3_coefficient23

compact_certificate theorem row3_coefficient24 (y z w : ℂ) : (rowPoly3 y z w).coeff 24=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x24 y z w

#print axioms row3_coefficient24

compact_certificate theorem row3_coefficient25 (y z w : ℂ) : (rowPoly3 y z w).coeff 25=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x25 y z w

#print axioms row3_coefficient25

compact_certificate theorem row3_coefficient26 (y z w : ℂ) : (rowPoly3 y z w).coeff 26=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x26 y z w

#print axioms row3_coefficient26

compact_certificate theorem row3_coefficient27 (y z w : ℂ) : (rowPoly3 y z w).coeff 27=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x27 y z w

#print axioms row3_coefficient27

compact_certificate theorem row3_coefficient28 (y z w : ℂ) : (rowPoly3 y z w).coeff 28=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x28 y z w

#print axioms row3_coefficient28

compact_certificate theorem row3_coefficient29 (y z w : ℂ) : (rowPoly3 y z w).coeff 29=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x29 y z w

#print axioms row3_coefficient29

compact_certificate theorem row3_coefficient30 (y z w : ℂ) : (rowPoly3 y z w).coeff 30=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x30 y z w

#print axioms row3_coefficient30

compact_certificate theorem row3_coefficient31 (y z w : ℂ) : (rowPoly3 y z w).coeff 31=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x31 y z w

#print axioms row3_coefficient31

compact_certificate theorem row3_coefficient32 (y z w : ℂ) : (rowPoly3 y z w).coeff 32=0 := by
  simpa [rowPoly3,qPoly0,rPoly3,qPoly1,rPoly2,qPoly2,rPoly1,qPoly3,rPoly0,qPoly4,vPoly3,qPoly5,vPoly2,qPoly6,vPoly1,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row3_x32 y z w

#print axioms row3_coefficient32


}
end SmallLevelTwentySixResultantBatchedMMM
end
end
