module

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelCubicQuarticSylvesterV1
public import SmallLevelTwentySixResultantBatchedMMPZeroGroupedTheoryV4
public import SmallLevelTwentySixResultantCoefficientsMMPTheoryV4
public meta import QuantitativeArithmeticCompactCommandsV1

public meta import QuantitativeArithmeticSparseCertificateComputeV5
public meta import SmallLevelCertificateBatchCommandV1
/-! Consolidated chapter: SmallLevelTwentySixResultantBatchedMMP. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixResultantBatchedMMPRowIndexXBundleSeriesV4 -/
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
namespace SmallLevelTwentySixResultantBatchedMMP
open SmallLevelTwentySixResultantCoefficientsMMP
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open Polynomial SmallLevelPolynomialCoefficientAssembly
open scoped Classical

/-! Whole coefficient identities are checked by sparse integer arithmetic.
The general evaluation lemma transports them to arbitrary complex arguments;
no stored intermediate polynomial or symbolic partial-product proof is needed. -/

certificate_batch {
compact_certificate theorem row4_x00 (y z w : ℂ) :
    q0100 y z w*r0300 y z w +
    q0600 y z w*v0200 y z w=0 := by
  have h : (merge (product q0100Data r0300Data) (product q0600Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0100, q0600, r0300, v0200] using he

#print axioms row4_x00

compact_certificate theorem row4_x01 (y z w : ℂ) :
    q0100 y z w*r0301 y z w +
    q0101 y z w*r0300 y z w +
    q0201 y z w*r0200 y z w +
    q0301 y z w*r0100 y z w +
    q0400 y z w*v0401 y z w +
    q0500 y z w*v0301 y z w +
    q0600 y z w*v0201 y z w +
    q0601 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0100Data r0301Data) (product q0101Data r0300Data)) (product q0201Data r0200Data)) (product q0301Data r0100Data)) (product q0400Data v0401Data)) (product q0500Data v0301Data)) (product q0600Data v0201Data)) (product q0601Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0100, q0101, q0201, q0301, q0400, q0500, q0600, q0601, r0100, r0200, r0300, r0301, v0200, v0201, v0301, v0401] using he

#print axioms row4_x01

compact_certificate theorem row4_x02 (y z w : ℂ) :
    q0101 y z w*r0301 y z w +
    q0102 y z w*r0300 y z w +
    q0201 y z w*r0201 y z w +
    q0202 y z w*r0200 y z w +
    q0301 y z w*r0101 y z w +
    q0302 y z w*r0100 y z w +
    q0400 y z w*v0402 y z w +
    q0401 y z w*v0401 y z w +
    q0500 y z w*v0302 y z w +
    q0501 y z w*v0301 y z w +
    q0600 y z w*v0202 y z w +
    q0601 y z w*v0201 y z w +
    q0602 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0101Data r0301Data) (product q0102Data r0300Data)) (product q0201Data r0201Data)) (product q0202Data r0200Data)) (product q0301Data r0101Data)) (product q0302Data r0100Data)) (product q0400Data v0402Data)) (product q0401Data v0401Data)) (product q0500Data v0302Data)) (product q0501Data v0301Data)) (product q0600Data v0202Data)) (product q0601Data v0201Data)) (product q0602Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0101, q0102, q0201, q0202, q0301, q0302, q0400, q0401, q0500, q0501, q0600, q0601, q0602, r0100, r0101, r0200, r0201, r0300, r0301, v0200, v0201, v0202, v0301, v0302, v0401, v0402] using he

#print axioms row4_x02

compact_certificate theorem row4_x03 (y z w : ℂ) :
    q0102 y z w*r0301 y z w +
    q0103 y z w*r0300 y z w +
    q0201 y z w*r0202 y z w +
    q0202 y z w*r0201 y z w +
    q0203 y z w*r0200 y z w +
    q0301 y z w*r0102 y z w +
    q0302 y z w*r0101 y z w +
    q0303 y z w*r0100 y z w +
    q0400 y z w*v0403 y z w +
    q0401 y z w*v0402 y z w +
    q0402 y z w*v0401 y z w +
    q0500 y z w*v0303 y z w +
    q0501 y z w*v0302 y z w +
    q0502 y z w*v0301 y z w +
    q0600 y z w*v0203 y z w +
    q0601 y z w*v0202 y z w +
    q0602 y z w*v0201 y z w +
    q0603 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0102Data r0301Data) (product q0103Data r0300Data)) (product q0201Data r0202Data)) (product q0202Data r0201Data)) (product q0203Data r0200Data)) (product q0301Data r0102Data)) (product q0302Data r0101Data)) (product q0303Data r0100Data)) (product q0400Data v0403Data)) (product q0401Data v0402Data)) (product q0402Data v0401Data)) (product q0500Data v0303Data)) (product q0501Data v0302Data)) (product q0502Data v0301Data)) (product q0600Data v0203Data)) (product q0601Data v0202Data)) (product q0602Data v0201Data)) (product q0603Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0102, q0103, q0201, q0202, q0203, q0301, q0302, q0303, q0400, q0401, q0402, q0500, q0501, q0502, q0600, q0601, q0602, q0603, r0100, r0101, r0102, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0301, v0302, v0303, v0401, v0402, v0403] using he

#print axioms row4_x03

compact_certificate theorem row4_x04 (y z w : ℂ) :
    q0103 y z w*r0301 y z w +
    q0104 y z w*r0300 y z w +
    q0202 y z w*r0202 y z w +
    q0203 y z w*r0201 y z w +
    q0204 y z w*r0200 y z w +
    q0301 y z w*r0103 y z w +
    q0302 y z w*r0102 y z w +
    q0303 y z w*r0101 y z w +
    q0304 y z w*r0100 y z w +
    q0400 y z w*v0404 y z w +
    q0401 y z w*v0403 y z w +
    q0402 y z w*v0402 y z w +
    q0403 y z w*v0401 y z w +
    q0500 y z w*v0304 y z w +
    q0501 y z w*v0303 y z w +
    q0502 y z w*v0302 y z w +
    q0503 y z w*v0301 y z w +
    q0600 y z w*v0204 y z w +
    q0601 y z w*v0203 y z w +
    q0602 y z w*v0202 y z w +
    q0603 y z w*v0201 y z w +
    q0604 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0103Data r0301Data) (product q0104Data r0300Data)) (product q0202Data r0202Data)) (product q0203Data r0201Data)) (product q0204Data r0200Data)) (product q0301Data r0103Data)) (product q0302Data r0102Data)) (product q0303Data r0101Data)) (product q0304Data r0100Data)) (product q0400Data v0404Data)) (product q0401Data v0403Data)) (product q0402Data v0402Data)) (product q0403Data v0401Data)) (product q0500Data v0304Data)) (product q0501Data v0303Data)) (product q0502Data v0302Data)) (product q0503Data v0301Data)) (product q0600Data v0204Data)) (product q0601Data v0203Data)) (product q0602Data v0202Data)) (product q0603Data v0201Data)) (product q0604Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0103, q0104, q0202, q0203, q0204, q0301, q0302, q0303, q0304, q0400, q0401, q0402, q0403, q0500, q0501, q0502, q0503, q0600, q0601, q0602, q0603, q0604, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0301, v0302, v0303, v0304, v0401, v0402, v0403, v0404] using he

#print axioms row4_x04

compact_certificate theorem row4_x05 (y z w : ℂ) :
    q0104 y z w*r0301 y z w +
    q0105 y z w*r0300 y z w +
    q0203 y z w*r0202 y z w +
    q0204 y z w*r0201 y z w +
    q0205 y z w*r0200 y z w +
    q0302 y z w*r0103 y z w +
    q0303 y z w*r0102 y z w +
    q0304 y z w*r0101 y z w +
    q0305 y z w*r0100 y z w +
    q0400 y z w*v0405 y z w +
    q0401 y z w*v0404 y z w +
    q0402 y z w*v0403 y z w +
    q0403 y z w*v0402 y z w +
    q0404 y z w*v0401 y z w +
    q0500 y z w*v0305 y z w +
    q0501 y z w*v0304 y z w +
    q0502 y z w*v0303 y z w +
    q0503 y z w*v0302 y z w +
    q0504 y z w*v0301 y z w +
    q0600 y z w*v0205 y z w +
    q0601 y z w*v0204 y z w +
    q0602 y z w*v0203 y z w +
    q0603 y z w*v0202 y z w +
    q0604 y z w*v0201 y z w +
    q0605 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0104Data r0301Data) (product q0105Data r0300Data)) (product q0203Data r0202Data)) (product q0204Data r0201Data)) (product q0205Data r0200Data)) (product q0302Data r0103Data)) (product q0303Data r0102Data)) (product q0304Data r0101Data)) (product q0305Data r0100Data)) (product q0400Data v0405Data)) (product q0401Data v0404Data)) (product q0402Data v0403Data)) (product q0403Data v0402Data)) (product q0404Data v0401Data)) (product q0500Data v0305Data)) (product q0501Data v0304Data)) (product q0502Data v0303Data)) (product q0503Data v0302Data)) (product q0504Data v0301Data)) (product q0600Data v0205Data)) (product q0601Data v0204Data)) (product q0602Data v0203Data)) (product q0603Data v0202Data)) (product q0604Data v0201Data)) (product q0605Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0104, q0105, q0203, q0204, q0205, q0302, q0303, q0304, q0305, q0400, q0401, q0402, q0403, q0404, q0500, q0501, q0502, q0503, q0504, q0600, q0601, q0602, q0603, q0604, q0605, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0301, v0302, v0303, v0304, v0305, v0401, v0402, v0403, v0404, v0405] using he

#print axioms row4_x05

compact_certificate theorem row4_x06 (y z w : ℂ) :
    q0105 y z w*r0301 y z w +
    q0106 y z w*r0300 y z w +
    q0204 y z w*r0202 y z w +
    q0205 y z w*r0201 y z w +
    q0206 y z w*r0200 y z w +
    q0303 y z w*r0103 y z w +
    q0304 y z w*r0102 y z w +
    q0305 y z w*r0101 y z w +
    q0306 y z w*r0100 y z w +
    q0400 y z w*v0406 y z w +
    q0401 y z w*v0405 y z w +
    q0402 y z w*v0404 y z w +
    q0403 y z w*v0403 y z w +
    q0404 y z w*v0402 y z w +
    q0405 y z w*v0401 y z w +
    q0500 y z w*v0306 y z w +
    q0501 y z w*v0305 y z w +
    q0502 y z w*v0304 y z w +
    q0503 y z w*v0303 y z w +
    q0504 y z w*v0302 y z w +
    q0505 y z w*v0301 y z w +
    q0600 y z w*v0206 y z w +
    q0601 y z w*v0205 y z w +
    q0602 y z w*v0204 y z w +
    q0603 y z w*v0203 y z w +
    q0604 y z w*v0202 y z w +
    q0605 y z w*v0201 y z w +
    q0606 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0105Data r0301Data) (product q0106Data r0300Data)) (product q0204Data r0202Data)) (product q0205Data r0201Data)) (product q0206Data r0200Data)) (product q0303Data r0103Data)) (product q0304Data r0102Data)) (product q0305Data r0101Data)) (product q0306Data r0100Data)) (product q0400Data v0406Data)) (product q0401Data v0405Data)) (product q0402Data v0404Data)) (product q0403Data v0403Data)) (product q0404Data v0402Data)) (product q0405Data v0401Data)) (product q0500Data v0306Data)) (product q0501Data v0305Data)) (product q0502Data v0304Data)) (product q0503Data v0303Data)) (product q0504Data v0302Data)) (product q0505Data v0301Data)) (product q0600Data v0206Data)) (product q0601Data v0205Data)) (product q0602Data v0204Data)) (product q0603Data v0203Data)) (product q0604Data v0202Data)) (product q0605Data v0201Data)) (product q0606Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0105, q0106, q0204, q0205, q0206, q0303, q0304, q0305, q0306, q0400, q0401, q0402, q0403, q0404, q0405, q0500, q0501, q0502, q0503, q0504, q0505, q0600, q0601, q0602, q0603, q0604, q0605, q0606, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0301, v0302, v0303, v0304, v0305, v0306, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x06

compact_certificate theorem row4_x07 (y z w : ℂ) :
    q0106 y z w*r0301 y z w +
    q0107 y z w*r0300 y z w +
    q0205 y z w*r0202 y z w +
    q0206 y z w*r0201 y z w +
    q0207 y z w*r0200 y z w +
    q0304 y z w*r0103 y z w +
    q0305 y z w*r0102 y z w +
    q0306 y z w*r0101 y z w +
    q0307 y z w*r0100 y z w +
    q0401 y z w*v0406 y z w +
    q0402 y z w*v0405 y z w +
    q0403 y z w*v0404 y z w +
    q0404 y z w*v0403 y z w +
    q0405 y z w*v0402 y z w +
    q0406 y z w*v0401 y z w +
    q0500 y z w*v0307 y z w +
    q0501 y z w*v0306 y z w +
    q0502 y z w*v0305 y z w +
    q0503 y z w*v0304 y z w +
    q0504 y z w*v0303 y z w +
    q0505 y z w*v0302 y z w +
    q0506 y z w*v0301 y z w +
    q0600 y z w*v0207 y z w +
    q0601 y z w*v0206 y z w +
    q0602 y z w*v0205 y z w +
    q0603 y z w*v0204 y z w +
    q0604 y z w*v0203 y z w +
    q0605 y z w*v0202 y z w +
    q0606 y z w*v0201 y z w +
    q0607 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0106Data r0301Data) (product q0107Data r0300Data)) (product q0205Data r0202Data)) (product q0206Data r0201Data)) (product q0207Data r0200Data)) (product q0304Data r0103Data)) (product q0305Data r0102Data)) (product q0306Data r0101Data)) (product q0307Data r0100Data)) (product q0401Data v0406Data)) (product q0402Data v0405Data)) (product q0403Data v0404Data)) (product q0404Data v0403Data)) (product q0405Data v0402Data)) (product q0406Data v0401Data)) (product q0500Data v0307Data)) (product q0501Data v0306Data)) (product q0502Data v0305Data)) (product q0503Data v0304Data)) (product q0504Data v0303Data)) (product q0505Data v0302Data)) (product q0506Data v0301Data)) (product q0600Data v0207Data)) (product q0601Data v0206Data)) (product q0602Data v0205Data)) (product q0603Data v0204Data)) (product q0604Data v0203Data)) (product q0605Data v0202Data)) (product q0606Data v0201Data)) (product q0607Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0106, q0107, q0205, q0206, q0207, q0304, q0305, q0306, q0307, q0401, q0402, q0403, q0404, q0405, q0406, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x07

compact_certificate theorem row4_x08 (y z w : ℂ) :
    q0107 y z w*r0301 y z w +
    q0108 y z w*r0300 y z w +
    q0206 y z w*r0202 y z w +
    q0207 y z w*r0201 y z w +
    q0208 y z w*r0200 y z w +
    q0305 y z w*r0103 y z w +
    q0306 y z w*r0102 y z w +
    q0307 y z w*r0101 y z w +
    q0308 y z w*r0100 y z w +
    q0402 y z w*v0406 y z w +
    q0403 y z w*v0405 y z w +
    q0404 y z w*v0404 y z w +
    q0405 y z w*v0403 y z w +
    q0406 y z w*v0402 y z w +
    q0407 y z w*v0401 y z w +
    q0501 y z w*v0307 y z w +
    q0502 y z w*v0306 y z w +
    q0503 y z w*v0305 y z w +
    q0504 y z w*v0304 y z w +
    q0505 y z w*v0303 y z w +
    q0506 y z w*v0302 y z w +
    q0507 y z w*v0301 y z w +
    q0600 y z w*v0208 y z w +
    q0601 y z w*v0207 y z w +
    q0602 y z w*v0206 y z w +
    q0603 y z w*v0205 y z w +
    q0604 y z w*v0204 y z w +
    q0605 y z w*v0203 y z w +
    q0606 y z w*v0202 y z w +
    q0607 y z w*v0201 y z w +
    q0608 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0107Data r0301Data) (product q0108Data r0300Data)) (product q0206Data r0202Data)) (product q0207Data r0201Data)) (product q0208Data r0200Data)) (product q0305Data r0103Data)) (product q0306Data r0102Data)) (product q0307Data r0101Data)) (product q0308Data r0100Data)) (product q0402Data v0406Data)) (product q0403Data v0405Data)) (product q0404Data v0404Data)) (product q0405Data v0403Data)) (product q0406Data v0402Data)) (product q0407Data v0401Data)) (product q0501Data v0307Data)) (product q0502Data v0306Data)) (product q0503Data v0305Data)) (product q0504Data v0304Data)) (product q0505Data v0303Data)) (product q0506Data v0302Data)) (product q0507Data v0301Data)) (product q0600Data v0208Data)) (product q0601Data v0207Data)) (product q0602Data v0206Data)) (product q0603Data v0205Data)) (product q0604Data v0204Data)) (product q0605Data v0203Data)) (product q0606Data v0202Data)) (product q0607Data v0201Data)) (product q0608Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0107, q0108, q0206, q0207, q0208, q0305, q0306, q0307, q0308, q0402, q0403, q0404, q0405, q0406, q0407, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x08

compact_certificate theorem row4_x09 (y z w : ℂ) :
    q0108 y z w*r0301 y z w +
    q0109 y z w*r0300 y z w +
    q0207 y z w*r0202 y z w +
    q0208 y z w*r0201 y z w +
    q0209 y z w*r0200 y z w +
    q0306 y z w*r0103 y z w +
    q0307 y z w*r0102 y z w +
    q0308 y z w*r0101 y z w +
    q0309 y z w*r0100 y z w +
    q0403 y z w*v0406 y z w +
    q0404 y z w*v0405 y z w +
    q0405 y z w*v0404 y z w +
    q0406 y z w*v0403 y z w +
    q0407 y z w*v0402 y z w +
    q0408 y z w*v0401 y z w +
    q0502 y z w*v0307 y z w +
    q0503 y z w*v0306 y z w +
    q0504 y z w*v0305 y z w +
    q0505 y z w*v0304 y z w +
    q0506 y z w*v0303 y z w +
    q0507 y z w*v0302 y z w +
    q0508 y z w*v0301 y z w +
    q0601 y z w*v0208 y z w +
    q0602 y z w*v0207 y z w +
    q0603 y z w*v0206 y z w +
    q0604 y z w*v0205 y z w +
    q0605 y z w*v0204 y z w +
    q0606 y z w*v0203 y z w +
    q0607 y z w*v0202 y z w +
    q0608 y z w*v0201 y z w +
    q0609 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0108Data r0301Data) (product q0109Data r0300Data)) (product q0207Data r0202Data)) (product q0208Data r0201Data)) (product q0209Data r0200Data)) (product q0306Data r0103Data)) (product q0307Data r0102Data)) (product q0308Data r0101Data)) (product q0309Data r0100Data)) (product q0403Data v0406Data)) (product q0404Data v0405Data)) (product q0405Data v0404Data)) (product q0406Data v0403Data)) (product q0407Data v0402Data)) (product q0408Data v0401Data)) (product q0502Data v0307Data)) (product q0503Data v0306Data)) (product q0504Data v0305Data)) (product q0505Data v0304Data)) (product q0506Data v0303Data)) (product q0507Data v0302Data)) (product q0508Data v0301Data)) (product q0601Data v0208Data)) (product q0602Data v0207Data)) (product q0603Data v0206Data)) (product q0604Data v0205Data)) (product q0605Data v0204Data)) (product q0606Data v0203Data)) (product q0607Data v0202Data)) (product q0608Data v0201Data)) (product q0609Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0108, q0109, q0207, q0208, q0209, q0306, q0307, q0308, q0309, q0403, q0404, q0405, q0406, q0407, q0408, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x09

compact_certificate theorem row4_x10 (y z w : ℂ) :
    q0109 y z w*r0301 y z w +
    q0110 y z w*r0300 y z w +
    q0208 y z w*r0202 y z w +
    q0209 y z w*r0201 y z w +
    q0210 y z w*r0200 y z w +
    q0307 y z w*r0103 y z w +
    q0308 y z w*r0102 y z w +
    q0309 y z w*r0101 y z w +
    q0310 y z w*r0100 y z w +
    q0404 y z w*v0406 y z w +
    q0405 y z w*v0405 y z w +
    q0406 y z w*v0404 y z w +
    q0407 y z w*v0403 y z w +
    q0408 y z w*v0402 y z w +
    q0409 y z w*v0401 y z w +
    q0503 y z w*v0307 y z w +
    q0504 y z w*v0306 y z w +
    q0505 y z w*v0305 y z w +
    q0506 y z w*v0304 y z w +
    q0507 y z w*v0303 y z w +
    q0508 y z w*v0302 y z w +
    q0509 y z w*v0301 y z w +
    q0602 y z w*v0208 y z w +
    q0603 y z w*v0207 y z w +
    q0604 y z w*v0206 y z w +
    q0605 y z w*v0205 y z w +
    q0606 y z w*v0204 y z w +
    q0607 y z w*v0203 y z w +
    q0608 y z w*v0202 y z w +
    q0609 y z w*v0201 y z w +
    q0610 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0109Data r0301Data) (product q0110Data r0300Data)) (product q0208Data r0202Data)) (product q0209Data r0201Data)) (product q0210Data r0200Data)) (product q0307Data r0103Data)) (product q0308Data r0102Data)) (product q0309Data r0101Data)) (product q0310Data r0100Data)) (product q0404Data v0406Data)) (product q0405Data v0405Data)) (product q0406Data v0404Data)) (product q0407Data v0403Data)) (product q0408Data v0402Data)) (product q0409Data v0401Data)) (product q0503Data v0307Data)) (product q0504Data v0306Data)) (product q0505Data v0305Data)) (product q0506Data v0304Data)) (product q0507Data v0303Data)) (product q0508Data v0302Data)) (product q0509Data v0301Data)) (product q0602Data v0208Data)) (product q0603Data v0207Data)) (product q0604Data v0206Data)) (product q0605Data v0205Data)) (product q0606Data v0204Data)) (product q0607Data v0203Data)) (product q0608Data v0202Data)) (product q0609Data v0201Data)) (product q0610Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0109, q0110, q0208, q0209, q0210, q0307, q0308, q0309, q0310, q0404, q0405, q0406, q0407, q0408, q0409, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x10

compact_certificate theorem row4_x11 (y z w : ℂ) :
    q0110 y z w*r0301 y z w +
    q0111 y z w*r0300 y z w +
    q0209 y z w*r0202 y z w +
    q0210 y z w*r0201 y z w +
    q0211 y z w*r0200 y z w +
    q0308 y z w*r0103 y z w +
    q0309 y z w*r0102 y z w +
    q0310 y z w*r0101 y z w +
    q0311 y z w*r0100 y z w +
    q0405 y z w*v0406 y z w +
    q0406 y z w*v0405 y z w +
    q0407 y z w*v0404 y z w +
    q0408 y z w*v0403 y z w +
    q0409 y z w*v0402 y z w +
    q0410 y z w*v0401 y z w +
    q0504 y z w*v0307 y z w +
    q0505 y z w*v0306 y z w +
    q0506 y z w*v0305 y z w +
    q0507 y z w*v0304 y z w +
    q0508 y z w*v0303 y z w +
    q0509 y z w*v0302 y z w +
    q0510 y z w*v0301 y z w +
    q0603 y z w*v0208 y z w +
    q0604 y z w*v0207 y z w +
    q0605 y z w*v0206 y z w +
    q0606 y z w*v0205 y z w +
    q0607 y z w*v0204 y z w +
    q0608 y z w*v0203 y z w +
    q0609 y z w*v0202 y z w +
    q0610 y z w*v0201 y z w +
    q0611 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0110Data r0301Data) (product q0111Data r0300Data)) (product q0209Data r0202Data)) (product q0210Data r0201Data)) (product q0211Data r0200Data)) (product q0308Data r0103Data)) (product q0309Data r0102Data)) (product q0310Data r0101Data)) (product q0311Data r0100Data)) (product q0405Data v0406Data)) (product q0406Data v0405Data)) (product q0407Data v0404Data)) (product q0408Data v0403Data)) (product q0409Data v0402Data)) (product q0410Data v0401Data)) (product q0504Data v0307Data)) (product q0505Data v0306Data)) (product q0506Data v0305Data)) (product q0507Data v0304Data)) (product q0508Data v0303Data)) (product q0509Data v0302Data)) (product q0510Data v0301Data)) (product q0603Data v0208Data)) (product q0604Data v0207Data)) (product q0605Data v0206Data)) (product q0606Data v0205Data)) (product q0607Data v0204Data)) (product q0608Data v0203Data)) (product q0609Data v0202Data)) (product q0610Data v0201Data)) (product q0611Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0110, q0111, q0209, q0210, q0211, q0308, q0309, q0310, q0311, q0405, q0406, q0407, q0408, q0409, q0410, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x11

compact_certificate theorem row4_x12 (y z w : ℂ) :
    q0111 y z w*r0301 y z w +
    q0112 y z w*r0300 y z w +
    q0210 y z w*r0202 y z w +
    q0211 y z w*r0201 y z w +
    q0212 y z w*r0200 y z w +
    q0309 y z w*r0103 y z w +
    q0310 y z w*r0102 y z w +
    q0311 y z w*r0101 y z w +
    q0312 y z w*r0100 y z w +
    q0406 y z w*v0406 y z w +
    q0407 y z w*v0405 y z w +
    q0408 y z w*v0404 y z w +
    q0409 y z w*v0403 y z w +
    q0410 y z w*v0402 y z w +
    q0411 y z w*v0401 y z w +
    q0505 y z w*v0307 y z w +
    q0506 y z w*v0306 y z w +
    q0507 y z w*v0305 y z w +
    q0508 y z w*v0304 y z w +
    q0509 y z w*v0303 y z w +
    q0510 y z w*v0302 y z w +
    q0511 y z w*v0301 y z w +
    q0604 y z w*v0208 y z w +
    q0605 y z w*v0207 y z w +
    q0606 y z w*v0206 y z w +
    q0607 y z w*v0205 y z w +
    q0608 y z w*v0204 y z w +
    q0609 y z w*v0203 y z w +
    q0610 y z w*v0202 y z w +
    q0611 y z w*v0201 y z w +
    q0612 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0111Data r0301Data) (product q0112Data r0300Data)) (product q0210Data r0202Data)) (product q0211Data r0201Data)) (product q0212Data r0200Data)) (product q0309Data r0103Data)) (product q0310Data r0102Data)) (product q0311Data r0101Data)) (product q0312Data r0100Data)) (product q0406Data v0406Data)) (product q0407Data v0405Data)) (product q0408Data v0404Data)) (product q0409Data v0403Data)) (product q0410Data v0402Data)) (product q0411Data v0401Data)) (product q0505Data v0307Data)) (product q0506Data v0306Data)) (product q0507Data v0305Data)) (product q0508Data v0304Data)) (product q0509Data v0303Data)) (product q0510Data v0302Data)) (product q0511Data v0301Data)) (product q0604Data v0208Data)) (product q0605Data v0207Data)) (product q0606Data v0206Data)) (product q0607Data v0205Data)) (product q0608Data v0204Data)) (product q0609Data v0203Data)) (product q0610Data v0202Data)) (product q0611Data v0201Data)) (product q0612Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0111, q0112, q0210, q0211, q0212, q0309, q0310, q0311, q0312, q0406, q0407, q0408, q0409, q0410, q0411, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x12

compact_certificate theorem row4_x13 (y z w : ℂ) :
    q0112 y z w*r0301 y z w +
    q0113 y z w*r0300 y z w +
    q0211 y z w*r0202 y z w +
    q0212 y z w*r0201 y z w +
    q0213 y z w*r0200 y z w +
    q0310 y z w*r0103 y z w +
    q0311 y z w*r0102 y z w +
    q0312 y z w*r0101 y z w +
    q0313 y z w*r0100 y z w +
    q0407 y z w*v0406 y z w +
    q0408 y z w*v0405 y z w +
    q0409 y z w*v0404 y z w +
    q0410 y z w*v0403 y z w +
    q0411 y z w*v0402 y z w +
    q0412 y z w*v0401 y z w +
    q0506 y z w*v0307 y z w +
    q0507 y z w*v0306 y z w +
    q0508 y z w*v0305 y z w +
    q0509 y z w*v0304 y z w +
    q0510 y z w*v0303 y z w +
    q0511 y z w*v0302 y z w +
    q0512 y z w*v0301 y z w +
    q0605 y z w*v0208 y z w +
    q0606 y z w*v0207 y z w +
    q0607 y z w*v0206 y z w +
    q0608 y z w*v0205 y z w +
    q0609 y z w*v0204 y z w +
    q0610 y z w*v0203 y z w +
    q0611 y z w*v0202 y z w +
    q0612 y z w*v0201 y z w +
    q0613 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0112Data r0301Data) (product q0113Data r0300Data)) (product q0211Data r0202Data)) (product q0212Data r0201Data)) (product q0213Data r0200Data)) (product q0310Data r0103Data)) (product q0311Data r0102Data)) (product q0312Data r0101Data)) (product q0313Data r0100Data)) (product q0407Data v0406Data)) (product q0408Data v0405Data)) (product q0409Data v0404Data)) (product q0410Data v0403Data)) (product q0411Data v0402Data)) (product q0412Data v0401Data)) (product q0506Data v0307Data)) (product q0507Data v0306Data)) (product q0508Data v0305Data)) (product q0509Data v0304Data)) (product q0510Data v0303Data)) (product q0511Data v0302Data)) (product q0512Data v0301Data)) (product q0605Data v0208Data)) (product q0606Data v0207Data)) (product q0607Data v0206Data)) (product q0608Data v0205Data)) (product q0609Data v0204Data)) (product q0610Data v0203Data)) (product q0611Data v0202Data)) (product q0612Data v0201Data)) (product q0613Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0112, q0113, q0211, q0212, q0213, q0310, q0311, q0312, q0313, q0407, q0408, q0409, q0410, q0411, q0412, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x13

compact_certificate theorem row4_x14 (y z w : ℂ) :
    q0113 y z w*r0301 y z w +
    q0114 y z w*r0300 y z w +
    q0212 y z w*r0202 y z w +
    q0213 y z w*r0201 y z w +
    q0214 y z w*r0200 y z w +
    q0311 y z w*r0103 y z w +
    q0312 y z w*r0102 y z w +
    q0313 y z w*r0101 y z w +
    q0314 y z w*r0100 y z w +
    q0408 y z w*v0406 y z w +
    q0409 y z w*v0405 y z w +
    q0410 y z w*v0404 y z w +
    q0411 y z w*v0403 y z w +
    q0412 y z w*v0402 y z w +
    q0413 y z w*v0401 y z w +
    q0507 y z w*v0307 y z w +
    q0508 y z w*v0306 y z w +
    q0509 y z w*v0305 y z w +
    q0510 y z w*v0304 y z w +
    q0511 y z w*v0303 y z w +
    q0512 y z w*v0302 y z w +
    q0513 y z w*v0301 y z w +
    q0606 y z w*v0208 y z w +
    q0607 y z w*v0207 y z w +
    q0608 y z w*v0206 y z w +
    q0609 y z w*v0205 y z w +
    q0610 y z w*v0204 y z w +
    q0611 y z w*v0203 y z w +
    q0612 y z w*v0202 y z w +
    q0613 y z w*v0201 y z w +
    q0614 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0113Data r0301Data) (product q0114Data r0300Data)) (product q0212Data r0202Data)) (product q0213Data r0201Data)) (product q0214Data r0200Data)) (product q0311Data r0103Data)) (product q0312Data r0102Data)) (product q0313Data r0101Data)) (product q0314Data r0100Data)) (product q0408Data v0406Data)) (product q0409Data v0405Data)) (product q0410Data v0404Data)) (product q0411Data v0403Data)) (product q0412Data v0402Data)) (product q0413Data v0401Data)) (product q0507Data v0307Data)) (product q0508Data v0306Data)) (product q0509Data v0305Data)) (product q0510Data v0304Data)) (product q0511Data v0303Data)) (product q0512Data v0302Data)) (product q0513Data v0301Data)) (product q0606Data v0208Data)) (product q0607Data v0207Data)) (product q0608Data v0206Data)) (product q0609Data v0205Data)) (product q0610Data v0204Data)) (product q0611Data v0203Data)) (product q0612Data v0202Data)) (product q0613Data v0201Data)) (product q0614Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0113, q0114, q0212, q0213, q0214, q0311, q0312, q0313, q0314, q0408, q0409, q0410, q0411, q0412, q0413, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x14

compact_certificate theorem row4_x15 (y z w : ℂ) :
    q0114 y z w*r0301 y z w +
    q0115 y z w*r0300 y z w +
    q0213 y z w*r0202 y z w +
    q0214 y z w*r0201 y z w +
    q0215 y z w*r0200 y z w +
    q0312 y z w*r0103 y z w +
    q0313 y z w*r0102 y z w +
    q0314 y z w*r0101 y z w +
    q0315 y z w*r0100 y z w +
    q0409 y z w*v0406 y z w +
    q0410 y z w*v0405 y z w +
    q0411 y z w*v0404 y z w +
    q0412 y z w*v0403 y z w +
    q0413 y z w*v0402 y z w +
    q0414 y z w*v0401 y z w +
    q0508 y z w*v0307 y z w +
    q0509 y z w*v0306 y z w +
    q0510 y z w*v0305 y z w +
    q0511 y z w*v0304 y z w +
    q0512 y z w*v0303 y z w +
    q0513 y z w*v0302 y z w +
    q0514 y z w*v0301 y z w +
    q0607 y z w*v0208 y z w +
    q0608 y z w*v0207 y z w +
    q0609 y z w*v0206 y z w +
    q0610 y z w*v0205 y z w +
    q0611 y z w*v0204 y z w +
    q0612 y z w*v0203 y z w +
    q0613 y z w*v0202 y z w +
    q0614 y z w*v0201 y z w +
    q0615 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0114Data r0301Data) (product q0115Data r0300Data)) (product q0213Data r0202Data)) (product q0214Data r0201Data)) (product q0215Data r0200Data)) (product q0312Data r0103Data)) (product q0313Data r0102Data)) (product q0314Data r0101Data)) (product q0315Data r0100Data)) (product q0409Data v0406Data)) (product q0410Data v0405Data)) (product q0411Data v0404Data)) (product q0412Data v0403Data)) (product q0413Data v0402Data)) (product q0414Data v0401Data)) (product q0508Data v0307Data)) (product q0509Data v0306Data)) (product q0510Data v0305Data)) (product q0511Data v0304Data)) (product q0512Data v0303Data)) (product q0513Data v0302Data)) (product q0514Data v0301Data)) (product q0607Data v0208Data)) (product q0608Data v0207Data)) (product q0609Data v0206Data)) (product q0610Data v0205Data)) (product q0611Data v0204Data)) (product q0612Data v0203Data)) (product q0613Data v0202Data)) (product q0614Data v0201Data)) (product q0615Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0114, q0115, q0213, q0214, q0215, q0312, q0313, q0314, q0315, q0409, q0410, q0411, q0412, q0413, q0414, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x15

compact_certificate theorem row4_x16 (y z w : ℂ) :
    q0115 y z w*r0301 y z w +
    q0116 y z w*r0300 y z w +
    q0214 y z w*r0202 y z w +
    q0215 y z w*r0201 y z w +
    q0216 y z w*r0200 y z w +
    q0313 y z w*r0103 y z w +
    q0314 y z w*r0102 y z w +
    q0315 y z w*r0101 y z w +
    q0316 y z w*r0100 y z w +
    q0410 y z w*v0406 y z w +
    q0411 y z w*v0405 y z w +
    q0412 y z w*v0404 y z w +
    q0413 y z w*v0403 y z w +
    q0414 y z w*v0402 y z w +
    q0415 y z w*v0401 y z w +
    q0509 y z w*v0307 y z w +
    q0510 y z w*v0306 y z w +
    q0511 y z w*v0305 y z w +
    q0512 y z w*v0304 y z w +
    q0513 y z w*v0303 y z w +
    q0514 y z w*v0302 y z w +
    q0515 y z w*v0301 y z w +
    q0608 y z w*v0208 y z w +
    q0609 y z w*v0207 y z w +
    q0610 y z w*v0206 y z w +
    q0611 y z w*v0205 y z w +
    q0612 y z w*v0204 y z w +
    q0613 y z w*v0203 y z w +
    q0614 y z w*v0202 y z w +
    q0615 y z w*v0201 y z w +
    q0616 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0115Data r0301Data) (product q0116Data r0300Data)) (product q0214Data r0202Data)) (product q0215Data r0201Data)) (product q0216Data r0200Data)) (product q0313Data r0103Data)) (product q0314Data r0102Data)) (product q0315Data r0101Data)) (product q0316Data r0100Data)) (product q0410Data v0406Data)) (product q0411Data v0405Data)) (product q0412Data v0404Data)) (product q0413Data v0403Data)) (product q0414Data v0402Data)) (product q0415Data v0401Data)) (product q0509Data v0307Data)) (product q0510Data v0306Data)) (product q0511Data v0305Data)) (product q0512Data v0304Data)) (product q0513Data v0303Data)) (product q0514Data v0302Data)) (product q0515Data v0301Data)) (product q0608Data v0208Data)) (product q0609Data v0207Data)) (product q0610Data v0206Data)) (product q0611Data v0205Data)) (product q0612Data v0204Data)) (product q0613Data v0203Data)) (product q0614Data v0202Data)) (product q0615Data v0201Data)) (product q0616Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0115, q0116, q0214, q0215, q0216, q0313, q0314, q0315, q0316, q0410, q0411, q0412, q0413, q0414, q0415, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x16

compact_certificate theorem row4_x17 (y z w : ℂ) :
    q0116 y z w*r0301 y z w +
    q0117 y z w*r0300 y z w +
    q0215 y z w*r0202 y z w +
    q0216 y z w*r0201 y z w +
    q0217 y z w*r0200 y z w +
    q0314 y z w*r0103 y z w +
    q0315 y z w*r0102 y z w +
    q0316 y z w*r0101 y z w +
    q0317 y z w*r0100 y z w +
    q0411 y z w*v0406 y z w +
    q0412 y z w*v0405 y z w +
    q0413 y z w*v0404 y z w +
    q0414 y z w*v0403 y z w +
    q0415 y z w*v0402 y z w +
    q0416 y z w*v0401 y z w +
    q0510 y z w*v0307 y z w +
    q0511 y z w*v0306 y z w +
    q0512 y z w*v0305 y z w +
    q0513 y z w*v0304 y z w +
    q0514 y z w*v0303 y z w +
    q0515 y z w*v0302 y z w +
    q0516 y z w*v0301 y z w +
    q0609 y z w*v0208 y z w +
    q0610 y z w*v0207 y z w +
    q0611 y z w*v0206 y z w +
    q0612 y z w*v0205 y z w +
    q0613 y z w*v0204 y z w +
    q0614 y z w*v0203 y z w +
    q0615 y z w*v0202 y z w +
    q0616 y z w*v0201 y z w +
    q0617 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0116Data r0301Data) (product q0117Data r0300Data)) (product q0215Data r0202Data)) (product q0216Data r0201Data)) (product q0217Data r0200Data)) (product q0314Data r0103Data)) (product q0315Data r0102Data)) (product q0316Data r0101Data)) (product q0317Data r0100Data)) (product q0411Data v0406Data)) (product q0412Data v0405Data)) (product q0413Data v0404Data)) (product q0414Data v0403Data)) (product q0415Data v0402Data)) (product q0416Data v0401Data)) (product q0510Data v0307Data)) (product q0511Data v0306Data)) (product q0512Data v0305Data)) (product q0513Data v0304Data)) (product q0514Data v0303Data)) (product q0515Data v0302Data)) (product q0516Data v0301Data)) (product q0609Data v0208Data)) (product q0610Data v0207Data)) (product q0611Data v0206Data)) (product q0612Data v0205Data)) (product q0613Data v0204Data)) (product q0614Data v0203Data)) (product q0615Data v0202Data)) (product q0616Data v0201Data)) (product q0617Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0116, q0117, q0215, q0216, q0217, q0314, q0315, q0316, q0317, q0411, q0412, q0413, q0414, q0415, q0416, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x17

compact_certificate theorem row4_x18 (y z w : ℂ) :
    q0117 y z w*r0301 y z w +
    q0118 y z w*r0300 y z w +
    q0216 y z w*r0202 y z w +
    q0217 y z w*r0201 y z w +
    q0218 y z w*r0200 y z w +
    q0315 y z w*r0103 y z w +
    q0316 y z w*r0102 y z w +
    q0317 y z w*r0101 y z w +
    q0318 y z w*r0100 y z w +
    q0412 y z w*v0406 y z w +
    q0413 y z w*v0405 y z w +
    q0414 y z w*v0404 y z w +
    q0415 y z w*v0403 y z w +
    q0416 y z w*v0402 y z w +
    q0417 y z w*v0401 y z w +
    q0511 y z w*v0307 y z w +
    q0512 y z w*v0306 y z w +
    q0513 y z w*v0305 y z w +
    q0514 y z w*v0304 y z w +
    q0515 y z w*v0303 y z w +
    q0516 y z w*v0302 y z w +
    q0517 y z w*v0301 y z w +
    q0610 y z w*v0208 y z w +
    q0611 y z w*v0207 y z w +
    q0612 y z w*v0206 y z w +
    q0613 y z w*v0205 y z w +
    q0614 y z w*v0204 y z w +
    q0615 y z w*v0203 y z w +
    q0616 y z w*v0202 y z w +
    q0617 y z w*v0201 y z w +
    q0618 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0117Data r0301Data) (product q0118Data r0300Data)) (product q0216Data r0202Data)) (product q0217Data r0201Data)) (product q0218Data r0200Data)) (product q0315Data r0103Data)) (product q0316Data r0102Data)) (product q0317Data r0101Data)) (product q0318Data r0100Data)) (product q0412Data v0406Data)) (product q0413Data v0405Data)) (product q0414Data v0404Data)) (product q0415Data v0403Data)) (product q0416Data v0402Data)) (product q0417Data v0401Data)) (product q0511Data v0307Data)) (product q0512Data v0306Data)) (product q0513Data v0305Data)) (product q0514Data v0304Data)) (product q0515Data v0303Data)) (product q0516Data v0302Data)) (product q0517Data v0301Data)) (product q0610Data v0208Data)) (product q0611Data v0207Data)) (product q0612Data v0206Data)) (product q0613Data v0205Data)) (product q0614Data v0204Data)) (product q0615Data v0203Data)) (product q0616Data v0202Data)) (product q0617Data v0201Data)) (product q0618Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0117, q0118, q0216, q0217, q0218, q0315, q0316, q0317, q0318, q0412, q0413, q0414, q0415, q0416, q0417, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x18

compact_certificate theorem row4_x19 (y z w : ℂ) :
    q0118 y z w*r0301 y z w +
    q0119 y z w*r0300 y z w +
    q0217 y z w*r0202 y z w +
    q0218 y z w*r0201 y z w +
    q0219 y z w*r0200 y z w +
    q0316 y z w*r0103 y z w +
    q0317 y z w*r0102 y z w +
    q0318 y z w*r0101 y z w +
    q0319 y z w*r0100 y z w +
    q0413 y z w*v0406 y z w +
    q0414 y z w*v0405 y z w +
    q0415 y z w*v0404 y z w +
    q0416 y z w*v0403 y z w +
    q0417 y z w*v0402 y z w +
    q0418 y z w*v0401 y z w +
    q0512 y z w*v0307 y z w +
    q0513 y z w*v0306 y z w +
    q0514 y z w*v0305 y z w +
    q0515 y z w*v0304 y z w +
    q0516 y z w*v0303 y z w +
    q0517 y z w*v0302 y z w +
    q0518 y z w*v0301 y z w +
    q0611 y z w*v0208 y z w +
    q0612 y z w*v0207 y z w +
    q0613 y z w*v0206 y z w +
    q0614 y z w*v0205 y z w +
    q0615 y z w*v0204 y z w +
    q0616 y z w*v0203 y z w +
    q0617 y z w*v0202 y z w +
    q0618 y z w*v0201 y z w +
    q0619 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0118Data r0301Data) (product q0119Data r0300Data)) (product q0217Data r0202Data)) (product q0218Data r0201Data)) (product q0219Data r0200Data)) (product q0316Data r0103Data)) (product q0317Data r0102Data)) (product q0318Data r0101Data)) (product q0319Data r0100Data)) (product q0413Data v0406Data)) (product q0414Data v0405Data)) (product q0415Data v0404Data)) (product q0416Data v0403Data)) (product q0417Data v0402Data)) (product q0418Data v0401Data)) (product q0512Data v0307Data)) (product q0513Data v0306Data)) (product q0514Data v0305Data)) (product q0515Data v0304Data)) (product q0516Data v0303Data)) (product q0517Data v0302Data)) (product q0518Data v0301Data)) (product q0611Data v0208Data)) (product q0612Data v0207Data)) (product q0613Data v0206Data)) (product q0614Data v0205Data)) (product q0615Data v0204Data)) (product q0616Data v0203Data)) (product q0617Data v0202Data)) (product q0618Data v0201Data)) (product q0619Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0118, q0119, q0217, q0218, q0219, q0316, q0317, q0318, q0319, q0413, q0414, q0415, q0416, q0417, q0418, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x19

compact_certificate theorem row4_x20 (y z w : ℂ) :
    q0119 y z w*r0301 y z w +
    q0120 y z w*r0300 y z w +
    q0218 y z w*r0202 y z w +
    q0219 y z w*r0201 y z w +
    q0220 y z w*r0200 y z w +
    q0317 y z w*r0103 y z w +
    q0318 y z w*r0102 y z w +
    q0319 y z w*r0101 y z w +
    q0320 y z w*r0100 y z w +
    q0414 y z w*v0406 y z w +
    q0415 y z w*v0405 y z w +
    q0416 y z w*v0404 y z w +
    q0417 y z w*v0403 y z w +
    q0418 y z w*v0402 y z w +
    q0419 y z w*v0401 y z w +
    q0513 y z w*v0307 y z w +
    q0514 y z w*v0306 y z w +
    q0515 y z w*v0305 y z w +
    q0516 y z w*v0304 y z w +
    q0517 y z w*v0303 y z w +
    q0518 y z w*v0302 y z w +
    q0519 y z w*v0301 y z w +
    q0612 y z w*v0208 y z w +
    q0613 y z w*v0207 y z w +
    q0614 y z w*v0206 y z w +
    q0615 y z w*v0205 y z w +
    q0616 y z w*v0204 y z w +
    q0617 y z w*v0203 y z w +
    q0618 y z w*v0202 y z w +
    q0619 y z w*v0201 y z w +
    q0620 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0119Data r0301Data) (product q0120Data r0300Data)) (product q0218Data r0202Data)) (product q0219Data r0201Data)) (product q0220Data r0200Data)) (product q0317Data r0103Data)) (product q0318Data r0102Data)) (product q0319Data r0101Data)) (product q0320Data r0100Data)) (product q0414Data v0406Data)) (product q0415Data v0405Data)) (product q0416Data v0404Data)) (product q0417Data v0403Data)) (product q0418Data v0402Data)) (product q0419Data v0401Data)) (product q0513Data v0307Data)) (product q0514Data v0306Data)) (product q0515Data v0305Data)) (product q0516Data v0304Data)) (product q0517Data v0303Data)) (product q0518Data v0302Data)) (product q0519Data v0301Data)) (product q0612Data v0208Data)) (product q0613Data v0207Data)) (product q0614Data v0206Data)) (product q0615Data v0205Data)) (product q0616Data v0204Data)) (product q0617Data v0203Data)) (product q0618Data v0202Data)) (product q0619Data v0201Data)) (product q0620Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0119, q0120, q0218, q0219, q0220, q0317, q0318, q0319, q0320, q0414, q0415, q0416, q0417, q0418, q0419, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x20

compact_certificate theorem row4_x21 (y z w : ℂ) :
    q0120 y z w*r0301 y z w +
    q0121 y z w*r0300 y z w +
    q0219 y z w*r0202 y z w +
    q0220 y z w*r0201 y z w +
    q0221 y z w*r0200 y z w +
    q0318 y z w*r0103 y z w +
    q0319 y z w*r0102 y z w +
    q0320 y z w*r0101 y z w +
    q0321 y z w*r0100 y z w +
    q0415 y z w*v0406 y z w +
    q0416 y z w*v0405 y z w +
    q0417 y z w*v0404 y z w +
    q0418 y z w*v0403 y z w +
    q0419 y z w*v0402 y z w +
    q0420 y z w*v0401 y z w +
    q0514 y z w*v0307 y z w +
    q0515 y z w*v0306 y z w +
    q0516 y z w*v0305 y z w +
    q0517 y z w*v0304 y z w +
    q0518 y z w*v0303 y z w +
    q0519 y z w*v0302 y z w +
    q0520 y z w*v0301 y z w +
    q0613 y z w*v0208 y z w +
    q0614 y z w*v0207 y z w +
    q0615 y z w*v0206 y z w +
    q0616 y z w*v0205 y z w +
    q0617 y z w*v0204 y z w +
    q0618 y z w*v0203 y z w +
    q0619 y z w*v0202 y z w +
    q0620 y z w*v0201 y z w +
    q0621 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0120Data r0301Data) (product q0121Data r0300Data)) (product q0219Data r0202Data)) (product q0220Data r0201Data)) (product q0221Data r0200Data)) (product q0318Data r0103Data)) (product q0319Data r0102Data)) (product q0320Data r0101Data)) (product q0321Data r0100Data)) (product q0415Data v0406Data)) (product q0416Data v0405Data)) (product q0417Data v0404Data)) (product q0418Data v0403Data)) (product q0419Data v0402Data)) (product q0420Data v0401Data)) (product q0514Data v0307Data)) (product q0515Data v0306Data)) (product q0516Data v0305Data)) (product q0517Data v0304Data)) (product q0518Data v0303Data)) (product q0519Data v0302Data)) (product q0520Data v0301Data)) (product q0613Data v0208Data)) (product q0614Data v0207Data)) (product q0615Data v0206Data)) (product q0616Data v0205Data)) (product q0617Data v0204Data)) (product q0618Data v0203Data)) (product q0619Data v0202Data)) (product q0620Data v0201Data)) (product q0621Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0120, q0121, q0219, q0220, q0221, q0318, q0319, q0320, q0321, q0415, q0416, q0417, q0418, q0419, q0420, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x21

compact_certificate theorem row4_x22 (y z w : ℂ) :
    q0121 y z w*r0301 y z w +
    q0122 y z w*r0300 y z w +
    q0220 y z w*r0202 y z w +
    q0221 y z w*r0201 y z w +
    q0222 y z w*r0200 y z w +
    q0319 y z w*r0103 y z w +
    q0320 y z w*r0102 y z w +
    q0321 y z w*r0101 y z w +
    q0322 y z w*r0100 y z w +
    q0416 y z w*v0406 y z w +
    q0417 y z w*v0405 y z w +
    q0418 y z w*v0404 y z w +
    q0419 y z w*v0403 y z w +
    q0420 y z w*v0402 y z w +
    q0421 y z w*v0401 y z w +
    q0515 y z w*v0307 y z w +
    q0516 y z w*v0306 y z w +
    q0517 y z w*v0305 y z w +
    q0518 y z w*v0304 y z w +
    q0519 y z w*v0303 y z w +
    q0520 y z w*v0302 y z w +
    q0521 y z w*v0301 y z w +
    q0614 y z w*v0208 y z w +
    q0615 y z w*v0207 y z w +
    q0616 y z w*v0206 y z w +
    q0617 y z w*v0205 y z w +
    q0618 y z w*v0204 y z w +
    q0619 y z w*v0203 y z w +
    q0620 y z w*v0202 y z w +
    q0621 y z w*v0201 y z w +
    q0622 y z w*v0200 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0121Data r0301Data) (product q0122Data r0300Data)) (product q0220Data r0202Data)) (product q0221Data r0201Data)) (product q0222Data r0200Data)) (product q0319Data r0103Data)) (product q0320Data r0102Data)) (product q0321Data r0101Data)) (product q0322Data r0100Data)) (product q0416Data v0406Data)) (product q0417Data v0405Data)) (product q0418Data v0404Data)) (product q0419Data v0403Data)) (product q0420Data v0402Data)) (product q0421Data v0401Data)) (product q0515Data v0307Data)) (product q0516Data v0306Data)) (product q0517Data v0305Data)) (product q0518Data v0304Data)) (product q0519Data v0303Data)) (product q0520Data v0302Data)) (product q0521Data v0301Data)) (product q0614Data v0208Data)) (product q0615Data v0207Data)) (product q0616Data v0206Data)) (product q0617Data v0205Data)) (product q0618Data v0204Data)) (product q0619Data v0203Data)) (product q0620Data v0202Data)) (product q0621Data v0201Data)) (product q0622Data v0200Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0121, q0122, q0220, q0221, q0222, q0319, q0320, q0321, q0322, q0416, q0417, q0418, q0419, q0420, q0421, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x22

compact_certificate theorem row4_x23 (y z w : ℂ) :
    q0122 y z w*r0301 y z w +
    q0123 y z w*r0300 y z w +
    q0221 y z w*r0202 y z w +
    q0222 y z w*r0201 y z w +
    q0223 y z w*r0200 y z w +
    q0320 y z w*r0103 y z w +
    q0321 y z w*r0102 y z w +
    q0322 y z w*r0101 y z w +
    q0323 y z w*r0100 y z w +
    q0417 y z w*v0406 y z w +
    q0418 y z w*v0405 y z w +
    q0419 y z w*v0404 y z w +
    q0420 y z w*v0403 y z w +
    q0421 y z w*v0402 y z w +
    q0422 y z w*v0401 y z w +
    q0516 y z w*v0307 y z w +
    q0517 y z w*v0306 y z w +
    q0518 y z w*v0305 y z w +
    q0519 y z w*v0304 y z w +
    q0520 y z w*v0303 y z w +
    q0521 y z w*v0302 y z w +
    q0522 y z w*v0301 y z w +
    q0615 y z w*v0208 y z w +
    q0616 y z w*v0207 y z w +
    q0617 y z w*v0206 y z w +
    q0618 y z w*v0205 y z w +
    q0619 y z w*v0204 y z w +
    q0620 y z w*v0203 y z w +
    q0621 y z w*v0202 y z w +
    q0622 y z w*v0201 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0122Data r0301Data) (product q0123Data r0300Data)) (product q0221Data r0202Data)) (product q0222Data r0201Data)) (product q0223Data r0200Data)) (product q0320Data r0103Data)) (product q0321Data r0102Data)) (product q0322Data r0101Data)) (product q0323Data r0100Data)) (product q0417Data v0406Data)) (product q0418Data v0405Data)) (product q0419Data v0404Data)) (product q0420Data v0403Data)) (product q0421Data v0402Data)) (product q0422Data v0401Data)) (product q0516Data v0307Data)) (product q0517Data v0306Data)) (product q0518Data v0305Data)) (product q0519Data v0304Data)) (product q0520Data v0303Data)) (product q0521Data v0302Data)) (product q0522Data v0301Data)) (product q0615Data v0208Data)) (product q0616Data v0207Data)) (product q0617Data v0206Data)) (product q0618Data v0205Data)) (product q0619Data v0204Data)) (product q0620Data v0203Data)) (product q0621Data v0202Data)) (product q0622Data v0201Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0122, q0123, q0221, q0222, q0223, q0320, q0321, q0322, q0323, q0417, q0418, q0419, q0420, q0421, q0422, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x23

compact_certificate theorem row4_x24 (y z w : ℂ) :
    q0123 y z w*r0301 y z w +
    q0124 y z w*r0300 y z w +
    q0222 y z w*r0202 y z w +
    q0223 y z w*r0201 y z w +
    q0224 y z w*r0200 y z w +
    q0321 y z w*r0103 y z w +
    q0322 y z w*r0102 y z w +
    q0323 y z w*r0101 y z w +
    q0324 y z w*r0100 y z w +
    q0418 y z w*v0406 y z w +
    q0419 y z w*v0405 y z w +
    q0420 y z w*v0404 y z w +
    q0421 y z w*v0403 y z w +
    q0422 y z w*v0402 y z w +
    q0423 y z w*v0401 y z w +
    q0517 y z w*v0307 y z w +
    q0518 y z w*v0306 y z w +
    q0519 y z w*v0305 y z w +
    q0520 y z w*v0304 y z w +
    q0521 y z w*v0303 y z w +
    q0522 y z w*v0302 y z w +
    q0523 y z w*v0301 y z w +
    q0616 y z w*v0208 y z w +
    q0617 y z w*v0207 y z w +
    q0618 y z w*v0206 y z w +
    q0619 y z w*v0205 y z w +
    q0620 y z w*v0204 y z w +
    q0621 y z w*v0203 y z w +
    q0622 y z w*v0202 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0123Data r0301Data) (product q0124Data r0300Data)) (product q0222Data r0202Data)) (product q0223Data r0201Data)) (product q0224Data r0200Data)) (product q0321Data r0103Data)) (product q0322Data r0102Data)) (product q0323Data r0101Data)) (product q0324Data r0100Data)) (product q0418Data v0406Data)) (product q0419Data v0405Data)) (product q0420Data v0404Data)) (product q0421Data v0403Data)) (product q0422Data v0402Data)) (product q0423Data v0401Data)) (product q0517Data v0307Data)) (product q0518Data v0306Data)) (product q0519Data v0305Data)) (product q0520Data v0304Data)) (product q0521Data v0303Data)) (product q0522Data v0302Data)) (product q0523Data v0301Data)) (product q0616Data v0208Data)) (product q0617Data v0207Data)) (product q0618Data v0206Data)) (product q0619Data v0205Data)) (product q0620Data v0204Data)) (product q0621Data v0203Data)) (product q0622Data v0202Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0123, q0124, q0222, q0223, q0224, q0321, q0322, q0323, q0324, q0418, q0419, q0420, q0421, q0422, q0423, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0202, v0203, v0204, v0205, v0206, v0207, v0208, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x24

compact_certificate theorem row4_x25 (y z w : ℂ) :
    q0124 y z w*r0301 y z w +
    q0125 y z w*r0300 y z w +
    q0223 y z w*r0202 y z w +
    q0224 y z w*r0201 y z w +
    q0225 y z w*r0200 y z w +
    q0322 y z w*r0103 y z w +
    q0323 y z w*r0102 y z w +
    q0324 y z w*r0101 y z w +
    q0325 y z w*r0100 y z w +
    q0419 y z w*v0406 y z w +
    q0420 y z w*v0405 y z w +
    q0421 y z w*v0404 y z w +
    q0422 y z w*v0403 y z w +
    q0423 y z w*v0402 y z w +
    q0424 y z w*v0401 y z w +
    q0518 y z w*v0307 y z w +
    q0519 y z w*v0306 y z w +
    q0520 y z w*v0305 y z w +
    q0521 y z w*v0304 y z w +
    q0522 y z w*v0303 y z w +
    q0523 y z w*v0302 y z w +
    q0617 y z w*v0208 y z w +
    q0618 y z w*v0207 y z w +
    q0619 y z w*v0206 y z w +
    q0620 y z w*v0205 y z w +
    q0621 y z w*v0204 y z w +
    q0622 y z w*v0203 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0124Data r0301Data) (product q0125Data r0300Data)) (product q0223Data r0202Data)) (product q0224Data r0201Data)) (product q0225Data r0200Data)) (product q0322Data r0103Data)) (product q0323Data r0102Data)) (product q0324Data r0101Data)) (product q0325Data r0100Data)) (product q0419Data v0406Data)) (product q0420Data v0405Data)) (product q0421Data v0404Data)) (product q0422Data v0403Data)) (product q0423Data v0402Data)) (product q0424Data v0401Data)) (product q0518Data v0307Data)) (product q0519Data v0306Data)) (product q0520Data v0305Data)) (product q0521Data v0304Data)) (product q0522Data v0303Data)) (product q0523Data v0302Data)) (product q0617Data v0208Data)) (product q0618Data v0207Data)) (product q0619Data v0206Data)) (product q0620Data v0205Data)) (product q0621Data v0204Data)) (product q0622Data v0203Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0124, q0125, q0223, q0224, q0225, q0322, q0323, q0324, q0325, q0419, q0420, q0421, q0422, q0423, q0424, q0518, q0519, q0520, q0521, q0522, q0523, q0617, q0618, q0619, q0620, q0621, q0622, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0203, v0204, v0205, v0206, v0207, v0208, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x25

compact_certificate theorem row4_x26 (y z w : ℂ) :
    q0125 y z w*r0301 y z w +
    q0126 y z w*r0300 y z w +
    q0224 y z w*r0202 y z w +
    q0225 y z w*r0201 y z w +
    q0226 y z w*r0200 y z w +
    q0323 y z w*r0103 y z w +
    q0324 y z w*r0102 y z w +
    q0325 y z w*r0101 y z w +
    q0326 y z w*r0100 y z w +
    q0420 y z w*v0406 y z w +
    q0421 y z w*v0405 y z w +
    q0422 y z w*v0404 y z w +
    q0423 y z w*v0403 y z w +
    q0424 y z w*v0402 y z w +
    q0519 y z w*v0307 y z w +
    q0520 y z w*v0306 y z w +
    q0521 y z w*v0305 y z w +
    q0522 y z w*v0304 y z w +
    q0523 y z w*v0303 y z w +
    q0618 y z w*v0208 y z w +
    q0619 y z w*v0207 y z w +
    q0620 y z w*v0206 y z w +
    q0621 y z w*v0205 y z w +
    q0622 y z w*v0204 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0125Data r0301Data) (product q0126Data r0300Data)) (product q0224Data r0202Data)) (product q0225Data r0201Data)) (product q0226Data r0200Data)) (product q0323Data r0103Data)) (product q0324Data r0102Data)) (product q0325Data r0101Data)) (product q0326Data r0100Data)) (product q0420Data v0406Data)) (product q0421Data v0405Data)) (product q0422Data v0404Data)) (product q0423Data v0403Data)) (product q0424Data v0402Data)) (product q0519Data v0307Data)) (product q0520Data v0306Data)) (product q0521Data v0305Data)) (product q0522Data v0304Data)) (product q0523Data v0303Data)) (product q0618Data v0208Data)) (product q0619Data v0207Data)) (product q0620Data v0206Data)) (product q0621Data v0205Data)) (product q0622Data v0204Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0125, q0126, q0224, q0225, q0226, q0323, q0324, q0325, q0326, q0420, q0421, q0422, q0423, q0424, q0519, q0520, q0521, q0522, q0523, q0618, q0619, q0620, q0621, q0622, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0204, v0205, v0206, v0207, v0208, v0303, v0304, v0305, v0306, v0307, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row4_x26

compact_certificate theorem row4_x27 (y z w : ℂ) :
    q0126 y z w*r0301 y z w +
    q0127 y z w*r0300 y z w +
    q0225 y z w*r0202 y z w +
    q0226 y z w*r0201 y z w +
    q0227 y z w*r0200 y z w +
    q0324 y z w*r0103 y z w +
    q0325 y z w*r0102 y z w +
    q0326 y z w*r0101 y z w +
    q0327 y z w*r0100 y z w +
    q0421 y z w*v0406 y z w +
    q0422 y z w*v0405 y z w +
    q0423 y z w*v0404 y z w +
    q0424 y z w*v0403 y z w +
    q0520 y z w*v0307 y z w +
    q0521 y z w*v0306 y z w +
    q0522 y z w*v0305 y z w +
    q0523 y z w*v0304 y z w +
    q0619 y z w*v0208 y z w +
    q0620 y z w*v0207 y z w +
    q0621 y z w*v0206 y z w +
    q0622 y z w*v0205 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0126Data r0301Data) (product q0127Data r0300Data)) (product q0225Data r0202Data)) (product q0226Data r0201Data)) (product q0227Data r0200Data)) (product q0324Data r0103Data)) (product q0325Data r0102Data)) (product q0326Data r0101Data)) (product q0327Data r0100Data)) (product q0421Data v0406Data)) (product q0422Data v0405Data)) (product q0423Data v0404Data)) (product q0424Data v0403Data)) (product q0520Data v0307Data)) (product q0521Data v0306Data)) (product q0522Data v0305Data)) (product q0523Data v0304Data)) (product q0619Data v0208Data)) (product q0620Data v0207Data)) (product q0621Data v0206Data)) (product q0622Data v0205Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0126, q0127, q0225, q0226, q0227, q0324, q0325, q0326, q0327, q0421, q0422, q0423, q0424, q0520, q0521, q0522, q0523, q0619, q0620, q0621, q0622, r0100, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0205, v0206, v0207, v0208, v0304, v0305, v0306, v0307, v0403, v0404, v0405, v0406] using he

#print axioms row4_x27

compact_certificate theorem row4_x28 (y z w : ℂ) :
    q0127 y z w*r0301 y z w +
    q0128 y z w*r0300 y z w +
    q0226 y z w*r0202 y z w +
    q0227 y z w*r0201 y z w +
    q0228 y z w*r0200 y z w +
    q0325 y z w*r0103 y z w +
    q0326 y z w*r0102 y z w +
    q0327 y z w*r0101 y z w +
    q0422 y z w*v0406 y z w +
    q0423 y z w*v0405 y z w +
    q0424 y z w*v0404 y z w +
    q0521 y z w*v0307 y z w +
    q0522 y z w*v0306 y z w +
    q0523 y z w*v0305 y z w +
    q0620 y z w*v0208 y z w +
    q0621 y z w*v0207 y z w +
    q0622 y z w*v0206 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0127Data r0301Data) (product q0128Data r0300Data)) (product q0226Data r0202Data)) (product q0227Data r0201Data)) (product q0228Data r0200Data)) (product q0325Data r0103Data)) (product q0326Data r0102Data)) (product q0327Data r0101Data)) (product q0422Data v0406Data)) (product q0423Data v0405Data)) (product q0424Data v0404Data)) (product q0521Data v0307Data)) (product q0522Data v0306Data)) (product q0523Data v0305Data)) (product q0620Data v0208Data)) (product q0621Data v0207Data)) (product q0622Data v0206Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0127, q0128, q0226, q0227, q0228, q0325, q0326, q0327, q0422, q0423, q0424, q0521, q0522, q0523, q0620, q0621, q0622, r0101, r0102, r0103, r0200, r0201, r0202, r0300, r0301, v0206, v0207, v0208, v0305, v0306, v0307, v0404, v0405, v0406] using he

#print axioms row4_x28

compact_certificate theorem row4_x29 (y z w : ℂ) :
    q0128 y z w*r0301 y z w +
    q0129 y z w*r0300 y z w +
    q0227 y z w*r0202 y z w +
    q0228 y z w*r0201 y z w +
    q0326 y z w*r0103 y z w +
    q0327 y z w*r0102 y z w +
    q0423 y z w*v0406 y z w +
    q0424 y z w*v0405 y z w +
    q0522 y z w*v0307 y z w +
    q0523 y z w*v0306 y z w +
    q0621 y z w*v0208 y z w +
    q0622 y z w*v0207 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0128Data r0301Data) (product q0129Data r0300Data)) (product q0227Data r0202Data)) (product q0228Data r0201Data)) (product q0326Data r0103Data)) (product q0327Data r0102Data)) (product q0423Data v0406Data)) (product q0424Data v0405Data)) (product q0522Data v0307Data)) (product q0523Data v0306Data)) (product q0621Data v0208Data)) (product q0622Data v0207Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0128, q0129, q0227, q0228, q0326, q0327, q0423, q0424, q0522, q0523, q0621, q0622, r0102, r0103, r0201, r0202, r0300, r0301, v0207, v0208, v0306, v0307, v0405, v0406] using he

#print axioms row4_x29

compact_certificate theorem row4_x30 (y z w : ℂ) :
    q0129 y z w*r0301 y z w +
    q0228 y z w*r0202 y z w +
    q0327 y z w*r0103 y z w +
    q0424 y z w*v0406 y z w +
    q0523 y z w*v0307 y z w +
    q0622 y z w*v0208 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (product q0129Data r0301Data) (product q0228Data r0202Data)) (product q0327Data r0103Data)) (product q0424Data v0406Data)) (product q0523Data v0307Data)) (product q0622Data v0208Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0129, q0228, q0327, q0424, q0523, q0622, r0103, r0202, r0301, v0208, v0307, v0406] using he

#print axioms row4_x30

compact_certificate theorem row4_x35 (_y _z _w : ℂ) : (0:ℂ)=0 := rfl
#print axioms row4_x35

compact_certificate theorem row4_coefficient00 (y z w : ℂ) : (rowPoly4 y z w).coeff 0=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x00 y z w

#print axioms row4_coefficient00

compact_certificate theorem row4_coefficient01 (y z w : ℂ) : (rowPoly4 y z w).coeff 1=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x01 y z w

#print axioms row4_coefficient01

compact_certificate theorem row4_coefficient02 (y z w : ℂ) : (rowPoly4 y z w).coeff 2=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x02 y z w

#print axioms row4_coefficient02

compact_certificate theorem row4_coefficient03 (y z w : ℂ) : (rowPoly4 y z w).coeff 3=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x03 y z w

#print axioms row4_coefficient03

compact_certificate theorem row4_coefficient04 (y z w : ℂ) : (rowPoly4 y z w).coeff 4=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x04 y z w

#print axioms row4_coefficient04

compact_certificate theorem row4_coefficient05 (y z w : ℂ) : (rowPoly4 y z w).coeff 5=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x05 y z w

#print axioms row4_coefficient05

compact_certificate theorem row4_coefficient06 (y z w : ℂ) : (rowPoly4 y z w).coeff 6=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x06 y z w

#print axioms row4_coefficient06

compact_certificate theorem row4_coefficient07 (y z w : ℂ) : (rowPoly4 y z w).coeff 7=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x07 y z w

#print axioms row4_coefficient07

compact_certificate theorem row4_coefficient08 (y z w : ℂ) : (rowPoly4 y z w).coeff 8=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x08 y z w

#print axioms row4_coefficient08

compact_certificate theorem row4_coefficient09 (y z w : ℂ) : (rowPoly4 y z w).coeff 9=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x09 y z w

#print axioms row4_coefficient09

compact_certificate theorem row4_coefficient10 (y z w : ℂ) : (rowPoly4 y z w).coeff 10=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x10 y z w

#print axioms row4_coefficient10

compact_certificate theorem row4_coefficient11 (y z w : ℂ) : (rowPoly4 y z w).coeff 11=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x11 y z w

#print axioms row4_coefficient11

compact_certificate theorem row4_coefficient12 (y z w : ℂ) : (rowPoly4 y z w).coeff 12=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x12 y z w

#print axioms row4_coefficient12

compact_certificate theorem row4_coefficient13 (y z w : ℂ) : (rowPoly4 y z w).coeff 13=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x13 y z w

#print axioms row4_coefficient13

compact_certificate theorem row4_coefficient14 (y z w : ℂ) : (rowPoly4 y z w).coeff 14=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x14 y z w

#print axioms row4_coefficient14

compact_certificate theorem row4_coefficient15 (y z w : ℂ) : (rowPoly4 y z w).coeff 15=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x15 y z w

#print axioms row4_coefficient15

compact_certificate theorem row4_coefficient16 (y z w : ℂ) : (rowPoly4 y z w).coeff 16=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x16 y z w

#print axioms row4_coefficient16

compact_certificate theorem row4_coefficient17 (y z w : ℂ) : (rowPoly4 y z w).coeff 17=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x17 y z w

#print axioms row4_coefficient17

compact_certificate theorem row4_coefficient18 (y z w : ℂ) : (rowPoly4 y z w).coeff 18=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x18 y z w

#print axioms row4_coefficient18

compact_certificate theorem row4_coefficient19 (y z w : ℂ) : (rowPoly4 y z w).coeff 19=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x19 y z w

#print axioms row4_coefficient19

compact_certificate theorem row4_coefficient20 (y z w : ℂ) : (rowPoly4 y z w).coeff 20=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x20 y z w

#print axioms row4_coefficient20

compact_certificate theorem row4_coefficient21 (y z w : ℂ) : (rowPoly4 y z w).coeff 21=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x21 y z w

#print axioms row4_coefficient21

compact_certificate theorem row4_coefficient22 (y z w : ℂ) : (rowPoly4 y z w).coeff 22=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x22 y z w

#print axioms row4_coefficient22

compact_certificate theorem row4_coefficient23 (y z w : ℂ) : (rowPoly4 y z w).coeff 23=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x23 y z w

#print axioms row4_coefficient23

compact_certificate theorem row4_coefficient24 (y z w : ℂ) : (rowPoly4 y z w).coeff 24=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x24 y z w

#print axioms row4_coefficient24

compact_certificate theorem row4_coefficient25 (y z w : ℂ) : (rowPoly4 y z w).coeff 25=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x25 y z w

#print axioms row4_coefficient25

compact_certificate theorem row4_coefficient26 (y z w : ℂ) : (rowPoly4 y z w).coeff 26=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x26 y z w

#print axioms row4_coefficient26

compact_certificate theorem row4_coefficient27 (y z w : ℂ) : (rowPoly4 y z w).coeff 27=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x27 y z w

#print axioms row4_coefficient27

compact_certificate theorem row4_coefficient28 (y z w : ℂ) : (rowPoly4 y z w).coeff 28=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x28 y z w

#print axioms row4_coefficient28

compact_certificate theorem row4_coefficient29 (y z w : ℂ) : (rowPoly4 y z w).coeff 29=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x29 y z w

#print axioms row4_coefficient29

compact_certificate theorem row4_coefficient30 (y z w : ℂ) : (rowPoly4 y z w).coeff 30=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x30 y z w

#print axioms row4_coefficient30

compact_certificate theorem row4_coefficient35 (y z w : ℂ) : (rowPoly4 y z w).coeff 35=0 := by
  simpa [rowPoly4,qPoly1,rPoly3,qPoly2,rPoly2,qPoly3,rPoly1,qPoly4,vPoly4,qPoly5,vPoly3,qPoly6,vPoly2,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row4_x35 y z w

#print axioms row4_coefficient35


}
end SmallLevelTwentySixResultantBatchedMMP
end
end
