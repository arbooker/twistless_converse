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
compact_certificate theorem row2_x00 (y z w : ℂ) :
    q0000 y z w*r0200 y z w +
    q0100 y z w*r0100 y z w +
    q0400 y z w*v0200 y z w +
    q0500 y z w*v0100 y z w +
    q0600 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (product q0000Data r0200Data) (product q0100Data r0100Data)) (product q0400Data v0200Data)) (product q0500Data v0100Data)) (product q0600Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0100, q0400, q0500, q0600, r0100, r0200, v0000, v0100, v0200] using he

#print axioms row2_x00

compact_certificate theorem row2_x01 (y z w : ℂ) :
    q0000 y z w*r0201 y z w +
    q0001 y z w*r0200 y z w +
    q0100 y z w*r0101 y z w +
    q0101 y z w*r0100 y z w +
    q0201 y z w*r0000 y z w +
    q0400 y z w*v0201 y z w +
    q0401 y z w*v0200 y z w +
    q0500 y z w*v0101 y z w +
    q0501 y z w*v0100 y z w +
    q0600 y z w*v0001 y z w +
    q0601 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0201Data) (product q0001Data r0200Data)) (product q0100Data r0101Data)) (product q0101Data r0100Data)) (product q0201Data r0000Data)) (product q0400Data v0201Data)) (product q0401Data v0200Data)) (product q0500Data v0101Data)) (product q0501Data v0100Data)) (product q0600Data v0001Data)) (product q0601Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0100, q0101, q0201, q0400, q0401, q0500, q0501, q0600, q0601, r0000, r0100, r0101, r0200, r0201, v0000, v0001, v0100, v0101, v0200, v0201] using he

#print axioms row2_x01

compact_certificate theorem row2_x02 (y z w : ℂ) :
    q0000 y z w*r0202 y z w +
    q0001 y z w*r0201 y z w +
    q0002 y z w*r0200 y z w +
    q0100 y z w*r0102 y z w +
    q0101 y z w*r0101 y z w +
    q0102 y z w*r0100 y z w +
    q0201 y z w*r0001 y z w +
    q0202 y z w*r0000 y z w +
    q0400 y z w*v0202 y z w +
    q0401 y z w*v0201 y z w +
    q0402 y z w*v0200 y z w +
    q0500 y z w*v0102 y z w +
    q0501 y z w*v0101 y z w +
    q0502 y z w*v0100 y z w +
    q0600 y z w*v0002 y z w +
    q0601 y z w*v0001 y z w +
    q0602 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0202Data) (product q0001Data r0201Data)) (product q0002Data r0200Data)) (product q0100Data r0102Data)) (product q0101Data r0101Data)) (product q0102Data r0100Data)) (product q0201Data r0001Data)) (product q0202Data r0000Data)) (product q0400Data v0202Data)) (product q0401Data v0201Data)) (product q0402Data v0200Data)) (product q0500Data v0102Data)) (product q0501Data v0101Data)) (product q0502Data v0100Data)) (product q0600Data v0002Data)) (product q0601Data v0001Data)) (product q0602Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0000, q0001, q0002, q0100, q0101, q0102, q0201, q0202, q0400, q0401, q0402, q0500, q0501, q0502, q0600, q0601, q0602, r0000, r0001, r0100, r0101, r0102, r0200, r0201, r0202, v0000, v0001, v0002, v0100, v0101, v0102, v0200, v0201, v0202] using he

#print axioms row2_x02

compact_certificate theorem row2_x03 (y z w : ℂ) :
    q0001 y z w*r0202 y z w +
    q0002 y z w*r0201 y z w +
    q0003 y z w*r0200 y z w +
    q0100 y z w*r0103 y z w +
    q0101 y z w*r0102 y z w +
    q0102 y z w*r0101 y z w +
    q0103 y z w*r0100 y z w +
    q0201 y z w*r0002 y z w +
    q0202 y z w*r0001 y z w +
    q0203 y z w*r0000 y z w +
    q0400 y z w*v0203 y z w +
    q0401 y z w*v0202 y z w +
    q0402 y z w*v0201 y z w +
    q0403 y z w*v0200 y z w +
    q0500 y z w*v0103 y z w +
    q0501 y z w*v0102 y z w +
    q0502 y z w*v0101 y z w +
    q0503 y z w*v0100 y z w +
    q0600 y z w*v0003 y z w +
    q0601 y z w*v0002 y z w +
    q0602 y z w*v0001 y z w +
    q0603 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0001Data r0202Data) (product q0002Data r0201Data)) (product q0003Data r0200Data)) (product q0100Data r0103Data)) (product q0101Data r0102Data)) (product q0102Data r0101Data)) (product q0103Data r0100Data)) (product q0201Data r0002Data)) (product q0202Data r0001Data)) (product q0203Data r0000Data)) (product q0400Data v0203Data)) (product q0401Data v0202Data)) (product q0402Data v0201Data)) (product q0403Data v0200Data)) (product q0500Data v0103Data)) (product q0501Data v0102Data)) (product q0502Data v0101Data)) (product q0503Data v0100Data)) (product q0600Data v0003Data)) (product q0601Data v0002Data)) (product q0602Data v0001Data)) (product q0603Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0001, q0002, q0003, q0100, q0101, q0102, q0103, q0201, q0202, q0203, q0400, q0401, q0402, q0403, q0500, q0501, q0502, q0503, q0600, q0601, q0602, q0603, r0000, r0001, r0002, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0100, v0101, v0102, v0103, v0200, v0201, v0202, v0203] using he

#print axioms row2_x03

compact_certificate theorem row2_x04 (y z w : ℂ) :
    q0002 y z w*r0202 y z w +
    q0003 y z w*r0201 y z w +
    q0004 y z w*r0200 y z w +
    q0101 y z w*r0103 y z w +
    q0102 y z w*r0102 y z w +
    q0103 y z w*r0101 y z w +
    q0104 y z w*r0100 y z w +
    q0201 y z w*r0003 y z w +
    q0202 y z w*r0002 y z w +
    q0203 y z w*r0001 y z w +
    q0204 y z w*r0000 y z w +
    q0400 y z w*v0204 y z w +
    q0401 y z w*v0203 y z w +
    q0402 y z w*v0202 y z w +
    q0403 y z w*v0201 y z w +
    q0404 y z w*v0200 y z w +
    q0500 y z w*v0104 y z w +
    q0501 y z w*v0103 y z w +
    q0502 y z w*v0102 y z w +
    q0503 y z w*v0101 y z w +
    q0504 y z w*v0100 y z w +
    q0600 y z w*v0004 y z w +
    q0601 y z w*v0003 y z w +
    q0602 y z w*v0002 y z w +
    q0603 y z w*v0001 y z w +
    q0604 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0002Data r0202Data) (product q0003Data r0201Data)) (product q0004Data r0200Data)) (product q0101Data r0103Data)) (product q0102Data r0102Data)) (product q0103Data r0101Data)) (product q0104Data r0100Data)) (product q0201Data r0003Data)) (product q0202Data r0002Data)) (product q0203Data r0001Data)) (product q0204Data r0000Data)) (product q0400Data v0204Data)) (product q0401Data v0203Data)) (product q0402Data v0202Data)) (product q0403Data v0201Data)) (product q0404Data v0200Data)) (product q0500Data v0104Data)) (product q0501Data v0103Data)) (product q0502Data v0102Data)) (product q0503Data v0101Data)) (product q0504Data v0100Data)) (product q0600Data v0004Data)) (product q0601Data v0003Data)) (product q0602Data v0002Data)) (product q0603Data v0001Data)) (product q0604Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0002, q0003, q0004, q0101, q0102, q0103, q0104, q0201, q0202, q0203, q0204, q0400, q0401, q0402, q0403, q0404, q0500, q0501, q0502, q0503, q0504, q0600, q0601, q0602, q0603, q0604, r0000, r0001, r0002, r0003, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0100, v0101, v0102, v0103, v0104, v0200, v0201, v0202, v0203, v0204] using he

#print axioms row2_x04

compact_certificate theorem row2_x05 (y z w : ℂ) :
    q0003 y z w*r0202 y z w +
    q0004 y z w*r0201 y z w +
    q0005 y z w*r0200 y z w +
    q0102 y z w*r0103 y z w +
    q0103 y z w*r0102 y z w +
    q0104 y z w*r0101 y z w +
    q0105 y z w*r0100 y z w +
    q0202 y z w*r0003 y z w +
    q0203 y z w*r0002 y z w +
    q0204 y z w*r0001 y z w +
    q0205 y z w*r0000 y z w +
    q0400 y z w*v0205 y z w +
    q0401 y z w*v0204 y z w +
    q0402 y z w*v0203 y z w +
    q0403 y z w*v0202 y z w +
    q0404 y z w*v0201 y z w +
    q0405 y z w*v0200 y z w +
    q0500 y z w*v0105 y z w +
    q0501 y z w*v0104 y z w +
    q0502 y z w*v0103 y z w +
    q0503 y z w*v0102 y z w +
    q0504 y z w*v0101 y z w +
    q0505 y z w*v0100 y z w +
    q0600 y z w*v0005 y z w +
    q0601 y z w*v0004 y z w +
    q0602 y z w*v0003 y z w +
    q0603 y z w*v0002 y z w +
    q0604 y z w*v0001 y z w +
    q0605 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0003Data r0202Data) (product q0004Data r0201Data)) (product q0005Data r0200Data)) (product q0102Data r0103Data)) (product q0103Data r0102Data)) (product q0104Data r0101Data)) (product q0105Data r0100Data)) (product q0202Data r0003Data)) (product q0203Data r0002Data)) (product q0204Data r0001Data)) (product q0205Data r0000Data)) (product q0400Data v0205Data)) (product q0401Data v0204Data)) (product q0402Data v0203Data)) (product q0403Data v0202Data)) (product q0404Data v0201Data)) (product q0405Data v0200Data)) (product q0500Data v0105Data)) (product q0501Data v0104Data)) (product q0502Data v0103Data)) (product q0503Data v0102Data)) (product q0504Data v0101Data)) (product q0505Data v0100Data)) (product q0600Data v0005Data)) (product q0601Data v0004Data)) (product q0602Data v0003Data)) (product q0603Data v0002Data)) (product q0604Data v0001Data)) (product q0605Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0003, q0004, q0005, q0102, q0103, q0104, q0105, q0202, q0203, q0204, q0205, q0400, q0401, q0402, q0403, q0404, q0405, q0500, q0501, q0502, q0503, q0504, q0505, q0600, q0601, q0602, q0603, q0604, q0605, r0000, r0001, r0002, r0003, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0100, v0101, v0102, v0103, v0104, v0105, v0200, v0201, v0202, v0203, v0204, v0205] using he

#print axioms row2_x05

compact_certificate theorem row2_x06 (y z w : ℂ) :
    q0004 y z w*r0202 y z w +
    q0005 y z w*r0201 y z w +
    q0006 y z w*r0200 y z w +
    q0103 y z w*r0103 y z w +
    q0104 y z w*r0102 y z w +
    q0105 y z w*r0101 y z w +
    q0106 y z w*r0100 y z w +
    q0201 y z w*r0005 y z w +
    q0203 y z w*r0003 y z w +
    q0204 y z w*r0002 y z w +
    q0205 y z w*r0001 y z w +
    q0206 y z w*r0000 y z w +
    q0400 y z w*v0206 y z w +
    q0401 y z w*v0205 y z w +
    q0402 y z w*v0204 y z w +
    q0403 y z w*v0203 y z w +
    q0404 y z w*v0202 y z w +
    q0405 y z w*v0201 y z w +
    q0406 y z w*v0200 y z w +
    q0500 y z w*v0106 y z w +
    q0501 y z w*v0105 y z w +
    q0502 y z w*v0104 y z w +
    q0503 y z w*v0103 y z w +
    q0504 y z w*v0102 y z w +
    q0505 y z w*v0101 y z w +
    q0506 y z w*v0100 y z w +
    q0600 y z w*v0006 y z w +
    q0601 y z w*v0005 y z w +
    q0602 y z w*v0004 y z w +
    q0603 y z w*v0003 y z w +
    q0604 y z w*v0002 y z w +
    q0605 y z w*v0001 y z w +
    q0606 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0004Data r0202Data) (product q0005Data r0201Data)) (product q0006Data r0200Data)) (product q0103Data r0103Data)) (product q0104Data r0102Data)) (product q0105Data r0101Data)) (product q0106Data r0100Data)) (product q0201Data r0005Data)) (product q0203Data r0003Data)) (product q0204Data r0002Data)) (product q0205Data r0001Data)) (product q0206Data r0000Data)) (product q0400Data v0206Data)) (product q0401Data v0205Data)) (product q0402Data v0204Data)) (product q0403Data v0203Data)) (product q0404Data v0202Data)) (product q0405Data v0201Data)) (product q0406Data v0200Data)) (product q0500Data v0106Data)) (product q0501Data v0105Data)) (product q0502Data v0104Data)) (product q0503Data v0103Data)) (product q0504Data v0102Data)) (product q0505Data v0101Data)) (product q0506Data v0100Data)) (product q0600Data v0006Data)) (product q0601Data v0005Data)) (product q0602Data v0004Data)) (product q0603Data v0003Data)) (product q0604Data v0002Data)) (product q0605Data v0001Data)) (product q0606Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0004, q0005, q0006, q0103, q0104, q0105, q0106, q0201, q0203, q0204, q0205, q0206, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0600, q0601, q0602, q0603, q0604, q0605, q0606, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0200, v0201, v0202, v0203, v0204, v0205, v0206] using he

#print axioms row2_x06

compact_certificate theorem row2_x07 (y z w : ℂ) :
    q0005 y z w*r0202 y z w +
    q0006 y z w*r0201 y z w +
    q0007 y z w*r0200 y z w +
    q0104 y z w*r0103 y z w +
    q0105 y z w*r0102 y z w +
    q0106 y z w*r0101 y z w +
    q0107 y z w*r0100 y z w +
    q0202 y z w*r0005 y z w +
    q0204 y z w*r0003 y z w +
    q0205 y z w*r0002 y z w +
    q0206 y z w*r0001 y z w +
    q0207 y z w*r0000 y z w +
    q0400 y z w*v0207 y z w +
    q0401 y z w*v0206 y z w +
    q0402 y z w*v0205 y z w +
    q0403 y z w*v0204 y z w +
    q0404 y z w*v0203 y z w +
    q0405 y z w*v0202 y z w +
    q0406 y z w*v0201 y z w +
    q0407 y z w*v0200 y z w +
    q0500 y z w*v0107 y z w +
    q0501 y z w*v0106 y z w +
    q0502 y z w*v0105 y z w +
    q0503 y z w*v0104 y z w +
    q0504 y z w*v0103 y z w +
    q0505 y z w*v0102 y z w +
    q0506 y z w*v0101 y z w +
    q0507 y z w*v0100 y z w +
    q0600 y z w*v0007 y z w +
    q0601 y z w*v0006 y z w +
    q0602 y z w*v0005 y z w +
    q0603 y z w*v0004 y z w +
    q0604 y z w*v0003 y z w +
    q0605 y z w*v0002 y z w +
    q0606 y z w*v0001 y z w +
    q0607 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0005Data r0202Data) (product q0006Data r0201Data)) (product q0007Data r0200Data)) (product q0104Data r0103Data)) (product q0105Data r0102Data)) (product q0106Data r0101Data)) (product q0107Data r0100Data)) (product q0202Data r0005Data)) (product q0204Data r0003Data)) (product q0205Data r0002Data)) (product q0206Data r0001Data)) (product q0207Data r0000Data)) (product q0400Data v0207Data)) (product q0401Data v0206Data)) (product q0402Data v0205Data)) (product q0403Data v0204Data)) (product q0404Data v0203Data)) (product q0405Data v0202Data)) (product q0406Data v0201Data)) (product q0407Data v0200Data)) (product q0500Data v0107Data)) (product q0501Data v0106Data)) (product q0502Data v0105Data)) (product q0503Data v0104Data)) (product q0504Data v0103Data)) (product q0505Data v0102Data)) (product q0506Data v0101Data)) (product q0507Data v0100Data)) (product q0600Data v0007Data)) (product q0601Data v0006Data)) (product q0602Data v0005Data)) (product q0603Data v0004Data)) (product q0604Data v0003Data)) (product q0605Data v0002Data)) (product q0606Data v0001Data)) (product q0607Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0005, q0006, q0007, q0104, q0105, q0106, q0107, q0202, q0204, q0205, q0206, q0207, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207] using he

#print axioms row2_x07

compact_certificate theorem row2_x08 (y z w : ℂ) :
    q0006 y z w*r0202 y z w +
    q0007 y z w*r0201 y z w +
    q0008 y z w*r0200 y z w +
    q0105 y z w*r0103 y z w +
    q0106 y z w*r0102 y z w +
    q0107 y z w*r0101 y z w +
    q0108 y z w*r0100 y z w +
    q0203 y z w*r0005 y z w +
    q0205 y z w*r0003 y z w +
    q0206 y z w*r0002 y z w +
    q0207 y z w*r0001 y z w +
    q0208 y z w*r0000 y z w +
    q0400 y z w*v0208 y z w +
    q0401 y z w*v0207 y z w +
    q0402 y z w*v0206 y z w +
    q0403 y z w*v0205 y z w +
    q0404 y z w*v0204 y z w +
    q0405 y z w*v0203 y z w +
    q0406 y z w*v0202 y z w +
    q0407 y z w*v0201 y z w +
    q0408 y z w*v0200 y z w +
    q0500 y z w*v0108 y z w +
    q0501 y z w*v0107 y z w +
    q0502 y z w*v0106 y z w +
    q0503 y z w*v0105 y z w +
    q0504 y z w*v0104 y z w +
    q0505 y z w*v0103 y z w +
    q0506 y z w*v0102 y z w +
    q0507 y z w*v0101 y z w +
    q0508 y z w*v0100 y z w +
    q0600 y z w*v0008 y z w +
    q0601 y z w*v0007 y z w +
    q0602 y z w*v0006 y z w +
    q0603 y z w*v0005 y z w +
    q0604 y z w*v0004 y z w +
    q0605 y z w*v0003 y z w +
    q0606 y z w*v0002 y z w +
    q0607 y z w*v0001 y z w +
    q0608 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0006Data r0202Data) (product q0007Data r0201Data)) (product q0008Data r0200Data)) (product q0105Data r0103Data)) (product q0106Data r0102Data)) (product q0107Data r0101Data)) (product q0108Data r0100Data)) (product q0203Data r0005Data)) (product q0205Data r0003Data)) (product q0206Data r0002Data)) (product q0207Data r0001Data)) (product q0208Data r0000Data)) (product q0400Data v0208Data)) (product q0401Data v0207Data)) (product q0402Data v0206Data)) (product q0403Data v0205Data)) (product q0404Data v0204Data)) (product q0405Data v0203Data)) (product q0406Data v0202Data)) (product q0407Data v0201Data)) (product q0408Data v0200Data)) (product q0500Data v0108Data)) (product q0501Data v0107Data)) (product q0502Data v0106Data)) (product q0503Data v0105Data)) (product q0504Data v0104Data)) (product q0505Data v0103Data)) (product q0506Data v0102Data)) (product q0507Data v0101Data)) (product q0508Data v0100Data)) (product q0600Data v0008Data)) (product q0601Data v0007Data)) (product q0602Data v0006Data)) (product q0603Data v0005Data)) (product q0604Data v0004Data)) (product q0605Data v0003Data)) (product q0606Data v0002Data)) (product q0607Data v0001Data)) (product q0608Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0006, q0007, q0008, q0105, q0106, q0107, q0108, q0203, q0205, q0206, q0207, q0208, q0400, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x08

compact_certificate theorem row2_x09 (y z w : ℂ) :
    q0007 y z w*r0202 y z w +
    q0008 y z w*r0201 y z w +
    q0009 y z w*r0200 y z w +
    q0106 y z w*r0103 y z w +
    q0107 y z w*r0102 y z w +
    q0108 y z w*r0101 y z w +
    q0109 y z w*r0100 y z w +
    q0204 y z w*r0005 y z w +
    q0206 y z w*r0003 y z w +
    q0207 y z w*r0002 y z w +
    q0208 y z w*r0001 y z w +
    q0209 y z w*r0000 y z w +
    q0401 y z w*v0208 y z w +
    q0402 y z w*v0207 y z w +
    q0403 y z w*v0206 y z w +
    q0404 y z w*v0205 y z w +
    q0405 y z w*v0204 y z w +
    q0406 y z w*v0203 y z w +
    q0407 y z w*v0202 y z w +
    q0408 y z w*v0201 y z w +
    q0409 y z w*v0200 y z w +
    q0500 y z w*v0109 y z w +
    q0501 y z w*v0108 y z w +
    q0502 y z w*v0107 y z w +
    q0503 y z w*v0106 y z w +
    q0504 y z w*v0105 y z w +
    q0505 y z w*v0104 y z w +
    q0506 y z w*v0103 y z w +
    q0507 y z w*v0102 y z w +
    q0508 y z w*v0101 y z w +
    q0509 y z w*v0100 y z w +
    q0600 y z w*v0009 y z w +
    q0601 y z w*v0008 y z w +
    q0602 y z w*v0007 y z w +
    q0603 y z w*v0006 y z w +
    q0604 y z w*v0005 y z w +
    q0605 y z w*v0004 y z w +
    q0606 y z w*v0003 y z w +
    q0607 y z w*v0002 y z w +
    q0608 y z w*v0001 y z w +
    q0609 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0007Data r0202Data) (product q0008Data r0201Data)) (product q0009Data r0200Data)) (product q0106Data r0103Data)) (product q0107Data r0102Data)) (product q0108Data r0101Data)) (product q0109Data r0100Data)) (product q0204Data r0005Data)) (product q0206Data r0003Data)) (product q0207Data r0002Data)) (product q0208Data r0001Data)) (product q0209Data r0000Data)) (product q0401Data v0208Data)) (product q0402Data v0207Data)) (product q0403Data v0206Data)) (product q0404Data v0205Data)) (product q0405Data v0204Data)) (product q0406Data v0203Data)) (product q0407Data v0202Data)) (product q0408Data v0201Data)) (product q0409Data v0200Data)) (product q0500Data v0109Data)) (product q0501Data v0108Data)) (product q0502Data v0107Data)) (product q0503Data v0106Data)) (product q0504Data v0105Data)) (product q0505Data v0104Data)) (product q0506Data v0103Data)) (product q0507Data v0102Data)) (product q0508Data v0101Data)) (product q0509Data v0100Data)) (product q0600Data v0009Data)) (product q0601Data v0008Data)) (product q0602Data v0007Data)) (product q0603Data v0006Data)) (product q0604Data v0005Data)) (product q0605Data v0004Data)) (product q0606Data v0003Data)) (product q0607Data v0002Data)) (product q0608Data v0001Data)) (product q0609Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0007, q0008, q0009, q0106, q0107, q0108, q0109, q0204, q0206, q0207, q0208, q0209, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x09

compact_certificate theorem row2_x10 (y z w : ℂ) :
    q0008 y z w*r0202 y z w +
    q0009 y z w*r0201 y z w +
    q0010 y z w*r0200 y z w +
    q0107 y z w*r0103 y z w +
    q0108 y z w*r0102 y z w +
    q0109 y z w*r0101 y z w +
    q0110 y z w*r0100 y z w +
    q0205 y z w*r0005 y z w +
    q0207 y z w*r0003 y z w +
    q0208 y z w*r0002 y z w +
    q0209 y z w*r0001 y z w +
    q0210 y z w*r0000 y z w +
    q0402 y z w*v0208 y z w +
    q0403 y z w*v0207 y z w +
    q0404 y z w*v0206 y z w +
    q0405 y z w*v0205 y z w +
    q0406 y z w*v0204 y z w +
    q0407 y z w*v0203 y z w +
    q0408 y z w*v0202 y z w +
    q0409 y z w*v0201 y z w +
    q0410 y z w*v0200 y z w +
    q0500 y z w*v0110 y z w +
    q0501 y z w*v0109 y z w +
    q0502 y z w*v0108 y z w +
    q0503 y z w*v0107 y z w +
    q0504 y z w*v0106 y z w +
    q0505 y z w*v0105 y z w +
    q0506 y z w*v0104 y z w +
    q0507 y z w*v0103 y z w +
    q0508 y z w*v0102 y z w +
    q0509 y z w*v0101 y z w +
    q0510 y z w*v0100 y z w +
    q0600 y z w*v0010 y z w +
    q0601 y z w*v0009 y z w +
    q0602 y z w*v0008 y z w +
    q0603 y z w*v0007 y z w +
    q0604 y z w*v0006 y z w +
    q0605 y z w*v0005 y z w +
    q0606 y z w*v0004 y z w +
    q0607 y z w*v0003 y z w +
    q0608 y z w*v0002 y z w +
    q0609 y z w*v0001 y z w +
    q0610 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0008Data r0202Data) (product q0009Data r0201Data)) (product q0010Data r0200Data)) (product q0107Data r0103Data)) (product q0108Data r0102Data)) (product q0109Data r0101Data)) (product q0110Data r0100Data)) (product q0205Data r0005Data)) (product q0207Data r0003Data)) (product q0208Data r0002Data)) (product q0209Data r0001Data)) (product q0210Data r0000Data)) (product q0402Data v0208Data)) (product q0403Data v0207Data)) (product q0404Data v0206Data)) (product q0405Data v0205Data)) (product q0406Data v0204Data)) (product q0407Data v0203Data)) (product q0408Data v0202Data)) (product q0409Data v0201Data)) (product q0410Data v0200Data)) (product q0500Data v0110Data)) (product q0501Data v0109Data)) (product q0502Data v0108Data)) (product q0503Data v0107Data)) (product q0504Data v0106Data)) (product q0505Data v0105Data)) (product q0506Data v0104Data)) (product q0507Data v0103Data)) (product q0508Data v0102Data)) (product q0509Data v0101Data)) (product q0510Data v0100Data)) (product q0600Data v0010Data)) (product q0601Data v0009Data)) (product q0602Data v0008Data)) (product q0603Data v0007Data)) (product q0604Data v0006Data)) (product q0605Data v0005Data)) (product q0606Data v0004Data)) (product q0607Data v0003Data)) (product q0608Data v0002Data)) (product q0609Data v0001Data)) (product q0610Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0008, q0009, q0010, q0107, q0108, q0109, q0110, q0205, q0207, q0208, q0209, q0210, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x10

compact_certificate theorem row2_x11 (y z w : ℂ) :
    q0009 y z w*r0202 y z w +
    q0010 y z w*r0201 y z w +
    q0011 y z w*r0200 y z w +
    q0108 y z w*r0103 y z w +
    q0109 y z w*r0102 y z w +
    q0110 y z w*r0101 y z w +
    q0111 y z w*r0100 y z w +
    q0206 y z w*r0005 y z w +
    q0208 y z w*r0003 y z w +
    q0209 y z w*r0002 y z w +
    q0210 y z w*r0001 y z w +
    q0211 y z w*r0000 y z w +
    q0403 y z w*v0208 y z w +
    q0404 y z w*v0207 y z w +
    q0405 y z w*v0206 y z w +
    q0406 y z w*v0205 y z w +
    q0407 y z w*v0204 y z w +
    q0408 y z w*v0203 y z w +
    q0409 y z w*v0202 y z w +
    q0410 y z w*v0201 y z w +
    q0411 y z w*v0200 y z w +
    q0501 y z w*v0110 y z w +
    q0502 y z w*v0109 y z w +
    q0503 y z w*v0108 y z w +
    q0504 y z w*v0107 y z w +
    q0505 y z w*v0106 y z w +
    q0506 y z w*v0105 y z w +
    q0507 y z w*v0104 y z w +
    q0508 y z w*v0103 y z w +
    q0509 y z w*v0102 y z w +
    q0510 y z w*v0101 y z w +
    q0511 y z w*v0100 y z w +
    q0600 y z w*v0011 y z w +
    q0601 y z w*v0010 y z w +
    q0602 y z w*v0009 y z w +
    q0603 y z w*v0008 y z w +
    q0604 y z w*v0007 y z w +
    q0605 y z w*v0006 y z w +
    q0606 y z w*v0005 y z w +
    q0607 y z w*v0004 y z w +
    q0608 y z w*v0003 y z w +
    q0609 y z w*v0002 y z w +
    q0610 y z w*v0001 y z w +
    q0611 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0009Data r0202Data) (product q0010Data r0201Data)) (product q0011Data r0200Data)) (product q0108Data r0103Data)) (product q0109Data r0102Data)) (product q0110Data r0101Data)) (product q0111Data r0100Data)) (product q0206Data r0005Data)) (product q0208Data r0003Data)) (product q0209Data r0002Data)) (product q0210Data r0001Data)) (product q0211Data r0000Data)) (product q0403Data v0208Data)) (product q0404Data v0207Data)) (product q0405Data v0206Data)) (product q0406Data v0205Data)) (product q0407Data v0204Data)) (product q0408Data v0203Data)) (product q0409Data v0202Data)) (product q0410Data v0201Data)) (product q0411Data v0200Data)) (product q0501Data v0110Data)) (product q0502Data v0109Data)) (product q0503Data v0108Data)) (product q0504Data v0107Data)) (product q0505Data v0106Data)) (product q0506Data v0105Data)) (product q0507Data v0104Data)) (product q0508Data v0103Data)) (product q0509Data v0102Data)) (product q0510Data v0101Data)) (product q0511Data v0100Data)) (product q0600Data v0011Data)) (product q0601Data v0010Data)) (product q0602Data v0009Data)) (product q0603Data v0008Data)) (product q0604Data v0007Data)) (product q0605Data v0006Data)) (product q0606Data v0005Data)) (product q0607Data v0004Data)) (product q0608Data v0003Data)) (product q0609Data v0002Data)) (product q0610Data v0001Data)) (product q0611Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0009, q0010, q0011, q0108, q0109, q0110, q0111, q0206, q0208, q0209, q0210, q0211, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x11

compact_certificate theorem row2_x12 (y z w : ℂ) :
    q0010 y z w*r0202 y z w +
    q0011 y z w*r0201 y z w +
    q0012 y z w*r0200 y z w +
    q0109 y z w*r0103 y z w +
    q0110 y z w*r0102 y z w +
    q0111 y z w*r0101 y z w +
    q0112 y z w*r0100 y z w +
    q0207 y z w*r0005 y z w +
    q0209 y z w*r0003 y z w +
    q0210 y z w*r0002 y z w +
    q0211 y z w*r0001 y z w +
    q0212 y z w*r0000 y z w +
    q0404 y z w*v0208 y z w +
    q0405 y z w*v0207 y z w +
    q0406 y z w*v0206 y z w +
    q0407 y z w*v0205 y z w +
    q0408 y z w*v0204 y z w +
    q0409 y z w*v0203 y z w +
    q0410 y z w*v0202 y z w +
    q0411 y z w*v0201 y z w +
    q0412 y z w*v0200 y z w +
    q0502 y z w*v0110 y z w +
    q0503 y z w*v0109 y z w +
    q0504 y z w*v0108 y z w +
    q0505 y z w*v0107 y z w +
    q0506 y z w*v0106 y z w +
    q0507 y z w*v0105 y z w +
    q0508 y z w*v0104 y z w +
    q0509 y z w*v0103 y z w +
    q0510 y z w*v0102 y z w +
    q0511 y z w*v0101 y z w +
    q0512 y z w*v0100 y z w +
    q0601 y z w*v0011 y z w +
    q0602 y z w*v0010 y z w +
    q0603 y z w*v0009 y z w +
    q0604 y z w*v0008 y z w +
    q0605 y z w*v0007 y z w +
    q0606 y z w*v0006 y z w +
    q0607 y z w*v0005 y z w +
    q0608 y z w*v0004 y z w +
    q0609 y z w*v0003 y z w +
    q0610 y z w*v0002 y z w +
    q0611 y z w*v0001 y z w +
    q0612 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0010Data r0202Data) (product q0011Data r0201Data)) (product q0012Data r0200Data)) (product q0109Data r0103Data)) (product q0110Data r0102Data)) (product q0111Data r0101Data)) (product q0112Data r0100Data)) (product q0207Data r0005Data)) (product q0209Data r0003Data)) (product q0210Data r0002Data)) (product q0211Data r0001Data)) (product q0212Data r0000Data)) (product q0404Data v0208Data)) (product q0405Data v0207Data)) (product q0406Data v0206Data)) (product q0407Data v0205Data)) (product q0408Data v0204Data)) (product q0409Data v0203Data)) (product q0410Data v0202Data)) (product q0411Data v0201Data)) (product q0412Data v0200Data)) (product q0502Data v0110Data)) (product q0503Data v0109Data)) (product q0504Data v0108Data)) (product q0505Data v0107Data)) (product q0506Data v0106Data)) (product q0507Data v0105Data)) (product q0508Data v0104Data)) (product q0509Data v0103Data)) (product q0510Data v0102Data)) (product q0511Data v0101Data)) (product q0512Data v0100Data)) (product q0601Data v0011Data)) (product q0602Data v0010Data)) (product q0603Data v0009Data)) (product q0604Data v0008Data)) (product q0605Data v0007Data)) (product q0606Data v0006Data)) (product q0607Data v0005Data)) (product q0608Data v0004Data)) (product q0609Data v0003Data)) (product q0610Data v0002Data)) (product q0611Data v0001Data)) (product q0612Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0010, q0011, q0012, q0109, q0110, q0111, q0112, q0207, q0209, q0210, q0211, q0212, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x12

compact_certificate theorem row2_x13 (y z w : ℂ) :
    q0011 y z w*r0202 y z w +
    q0012 y z w*r0201 y z w +
    q0013 y z w*r0200 y z w +
    q0110 y z w*r0103 y z w +
    q0111 y z w*r0102 y z w +
    q0112 y z w*r0101 y z w +
    q0113 y z w*r0100 y z w +
    q0208 y z w*r0005 y z w +
    q0210 y z w*r0003 y z w +
    q0211 y z w*r0002 y z w +
    q0212 y z w*r0001 y z w +
    q0213 y z w*r0000 y z w +
    q0405 y z w*v0208 y z w +
    q0406 y z w*v0207 y z w +
    q0407 y z w*v0206 y z w +
    q0408 y z w*v0205 y z w +
    q0409 y z w*v0204 y z w +
    q0410 y z w*v0203 y z w +
    q0411 y z w*v0202 y z w +
    q0412 y z w*v0201 y z w +
    q0413 y z w*v0200 y z w +
    q0503 y z w*v0110 y z w +
    q0504 y z w*v0109 y z w +
    q0505 y z w*v0108 y z w +
    q0506 y z w*v0107 y z w +
    q0507 y z w*v0106 y z w +
    q0508 y z w*v0105 y z w +
    q0509 y z w*v0104 y z w +
    q0510 y z w*v0103 y z w +
    q0511 y z w*v0102 y z w +
    q0512 y z w*v0101 y z w +
    q0513 y z w*v0100 y z w +
    q0602 y z w*v0011 y z w +
    q0603 y z w*v0010 y z w +
    q0604 y z w*v0009 y z w +
    q0605 y z w*v0008 y z w +
    q0606 y z w*v0007 y z w +
    q0607 y z w*v0006 y z w +
    q0608 y z w*v0005 y z w +
    q0609 y z w*v0004 y z w +
    q0610 y z w*v0003 y z w +
    q0611 y z w*v0002 y z w +
    q0612 y z w*v0001 y z w +
    q0613 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0011Data r0202Data) (product q0012Data r0201Data)) (product q0013Data r0200Data)) (product q0110Data r0103Data)) (product q0111Data r0102Data)) (product q0112Data r0101Data)) (product q0113Data r0100Data)) (product q0208Data r0005Data)) (product q0210Data r0003Data)) (product q0211Data r0002Data)) (product q0212Data r0001Data)) (product q0213Data r0000Data)) (product q0405Data v0208Data)) (product q0406Data v0207Data)) (product q0407Data v0206Data)) (product q0408Data v0205Data)) (product q0409Data v0204Data)) (product q0410Data v0203Data)) (product q0411Data v0202Data)) (product q0412Data v0201Data)) (product q0413Data v0200Data)) (product q0503Data v0110Data)) (product q0504Data v0109Data)) (product q0505Data v0108Data)) (product q0506Data v0107Data)) (product q0507Data v0106Data)) (product q0508Data v0105Data)) (product q0509Data v0104Data)) (product q0510Data v0103Data)) (product q0511Data v0102Data)) (product q0512Data v0101Data)) (product q0513Data v0100Data)) (product q0602Data v0011Data)) (product q0603Data v0010Data)) (product q0604Data v0009Data)) (product q0605Data v0008Data)) (product q0606Data v0007Data)) (product q0607Data v0006Data)) (product q0608Data v0005Data)) (product q0609Data v0004Data)) (product q0610Data v0003Data)) (product q0611Data v0002Data)) (product q0612Data v0001Data)) (product q0613Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0011, q0012, q0013, q0110, q0111, q0112, q0113, q0208, q0210, q0211, q0212, q0213, q0405, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x13

compact_certificate theorem row2_x14 (y z w : ℂ) :
    q0012 y z w*r0202 y z w +
    q0013 y z w*r0201 y z w +
    q0014 y z w*r0200 y z w +
    q0111 y z w*r0103 y z w +
    q0112 y z w*r0102 y z w +
    q0113 y z w*r0101 y z w +
    q0114 y z w*r0100 y z w +
    q0209 y z w*r0005 y z w +
    q0211 y z w*r0003 y z w +
    q0212 y z w*r0002 y z w +
    q0213 y z w*r0001 y z w +
    q0214 y z w*r0000 y z w +
    q0406 y z w*v0208 y z w +
    q0407 y z w*v0207 y z w +
    q0408 y z w*v0206 y z w +
    q0409 y z w*v0205 y z w +
    q0410 y z w*v0204 y z w +
    q0411 y z w*v0203 y z w +
    q0412 y z w*v0202 y z w +
    q0413 y z w*v0201 y z w +
    q0414 y z w*v0200 y z w +
    q0504 y z w*v0110 y z w +
    q0505 y z w*v0109 y z w +
    q0506 y z w*v0108 y z w +
    q0507 y z w*v0107 y z w +
    q0508 y z w*v0106 y z w +
    q0509 y z w*v0105 y z w +
    q0510 y z w*v0104 y z w +
    q0511 y z w*v0103 y z w +
    q0512 y z w*v0102 y z w +
    q0513 y z w*v0101 y z w +
    q0514 y z w*v0100 y z w +
    q0603 y z w*v0011 y z w +
    q0604 y z w*v0010 y z w +
    q0605 y z w*v0009 y z w +
    q0606 y z w*v0008 y z w +
    q0607 y z w*v0007 y z w +
    q0608 y z w*v0006 y z w +
    q0609 y z w*v0005 y z w +
    q0610 y z w*v0004 y z w +
    q0611 y z w*v0003 y z w +
    q0612 y z w*v0002 y z w +
    q0613 y z w*v0001 y z w +
    q0614 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0012Data r0202Data) (product q0013Data r0201Data)) (product q0014Data r0200Data)) (product q0111Data r0103Data)) (product q0112Data r0102Data)) (product q0113Data r0101Data)) (product q0114Data r0100Data)) (product q0209Data r0005Data)) (product q0211Data r0003Data)) (product q0212Data r0002Data)) (product q0213Data r0001Data)) (product q0214Data r0000Data)) (product q0406Data v0208Data)) (product q0407Data v0207Data)) (product q0408Data v0206Data)) (product q0409Data v0205Data)) (product q0410Data v0204Data)) (product q0411Data v0203Data)) (product q0412Data v0202Data)) (product q0413Data v0201Data)) (product q0414Data v0200Data)) (product q0504Data v0110Data)) (product q0505Data v0109Data)) (product q0506Data v0108Data)) (product q0507Data v0107Data)) (product q0508Data v0106Data)) (product q0509Data v0105Data)) (product q0510Data v0104Data)) (product q0511Data v0103Data)) (product q0512Data v0102Data)) (product q0513Data v0101Data)) (product q0514Data v0100Data)) (product q0603Data v0011Data)) (product q0604Data v0010Data)) (product q0605Data v0009Data)) (product q0606Data v0008Data)) (product q0607Data v0007Data)) (product q0608Data v0006Data)) (product q0609Data v0005Data)) (product q0610Data v0004Data)) (product q0611Data v0003Data)) (product q0612Data v0002Data)) (product q0613Data v0001Data)) (product q0614Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0012, q0013, q0014, q0111, q0112, q0113, q0114, q0209, q0211, q0212, q0213, q0214, q0406, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x14

compact_certificate theorem row2_x15 (y z w : ℂ) :
    q0013 y z w*r0202 y z w +
    q0014 y z w*r0201 y z w +
    q0015 y z w*r0200 y z w +
    q0112 y z w*r0103 y z w +
    q0113 y z w*r0102 y z w +
    q0114 y z w*r0101 y z w +
    q0115 y z w*r0100 y z w +
    q0210 y z w*r0005 y z w +
    q0212 y z w*r0003 y z w +
    q0213 y z w*r0002 y z w +
    q0214 y z w*r0001 y z w +
    q0215 y z w*r0000 y z w +
    q0407 y z w*v0208 y z w +
    q0408 y z w*v0207 y z w +
    q0409 y z w*v0206 y z w +
    q0410 y z w*v0205 y z w +
    q0411 y z w*v0204 y z w +
    q0412 y z w*v0203 y z w +
    q0413 y z w*v0202 y z w +
    q0414 y z w*v0201 y z w +
    q0415 y z w*v0200 y z w +
    q0505 y z w*v0110 y z w +
    q0506 y z w*v0109 y z w +
    q0507 y z w*v0108 y z w +
    q0508 y z w*v0107 y z w +
    q0509 y z w*v0106 y z w +
    q0510 y z w*v0105 y z w +
    q0511 y z w*v0104 y z w +
    q0512 y z w*v0103 y z w +
    q0513 y z w*v0102 y z w +
    q0514 y z w*v0101 y z w +
    q0515 y z w*v0100 y z w +
    q0604 y z w*v0011 y z w +
    q0605 y z w*v0010 y z w +
    q0606 y z w*v0009 y z w +
    q0607 y z w*v0008 y z w +
    q0608 y z w*v0007 y z w +
    q0609 y z w*v0006 y z w +
    q0610 y z w*v0005 y z w +
    q0611 y z w*v0004 y z w +
    q0612 y z w*v0003 y z w +
    q0613 y z w*v0002 y z w +
    q0614 y z w*v0001 y z w +
    q0615 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0013Data r0202Data) (product q0014Data r0201Data)) (product q0015Data r0200Data)) (product q0112Data r0103Data)) (product q0113Data r0102Data)) (product q0114Data r0101Data)) (product q0115Data r0100Data)) (product q0210Data r0005Data)) (product q0212Data r0003Data)) (product q0213Data r0002Data)) (product q0214Data r0001Data)) (product q0215Data r0000Data)) (product q0407Data v0208Data)) (product q0408Data v0207Data)) (product q0409Data v0206Data)) (product q0410Data v0205Data)) (product q0411Data v0204Data)) (product q0412Data v0203Data)) (product q0413Data v0202Data)) (product q0414Data v0201Data)) (product q0415Data v0200Data)) (product q0505Data v0110Data)) (product q0506Data v0109Data)) (product q0507Data v0108Data)) (product q0508Data v0107Data)) (product q0509Data v0106Data)) (product q0510Data v0105Data)) (product q0511Data v0104Data)) (product q0512Data v0103Data)) (product q0513Data v0102Data)) (product q0514Data v0101Data)) (product q0515Data v0100Data)) (product q0604Data v0011Data)) (product q0605Data v0010Data)) (product q0606Data v0009Data)) (product q0607Data v0008Data)) (product q0608Data v0007Data)) (product q0609Data v0006Data)) (product q0610Data v0005Data)) (product q0611Data v0004Data)) (product q0612Data v0003Data)) (product q0613Data v0002Data)) (product q0614Data v0001Data)) (product q0615Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0013, q0014, q0015, q0112, q0113, q0114, q0115, q0210, q0212, q0213, q0214, q0215, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0505, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0604, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x15

compact_certificate theorem row2_x16 (y z w : ℂ) :
    q0014 y z w*r0202 y z w +
    q0015 y z w*r0201 y z w +
    q0016 y z w*r0200 y z w +
    q0113 y z w*r0103 y z w +
    q0114 y z w*r0102 y z w +
    q0115 y z w*r0101 y z w +
    q0116 y z w*r0100 y z w +
    q0211 y z w*r0005 y z w +
    q0213 y z w*r0003 y z w +
    q0214 y z w*r0002 y z w +
    q0215 y z w*r0001 y z w +
    q0216 y z w*r0000 y z w +
    q0408 y z w*v0208 y z w +
    q0409 y z w*v0207 y z w +
    q0410 y z w*v0206 y z w +
    q0411 y z w*v0205 y z w +
    q0412 y z w*v0204 y z w +
    q0413 y z w*v0203 y z w +
    q0414 y z w*v0202 y z w +
    q0415 y z w*v0201 y z w +
    q0416 y z w*v0200 y z w +
    q0506 y z w*v0110 y z w +
    q0507 y z w*v0109 y z w +
    q0508 y z w*v0108 y z w +
    q0509 y z w*v0107 y z w +
    q0510 y z w*v0106 y z w +
    q0511 y z w*v0105 y z w +
    q0512 y z w*v0104 y z w +
    q0513 y z w*v0103 y z w +
    q0514 y z w*v0102 y z w +
    q0515 y z w*v0101 y z w +
    q0516 y z w*v0100 y z w +
    q0605 y z w*v0011 y z w +
    q0606 y z w*v0010 y z w +
    q0607 y z w*v0009 y z w +
    q0608 y z w*v0008 y z w +
    q0609 y z w*v0007 y z w +
    q0610 y z w*v0006 y z w +
    q0611 y z w*v0005 y z w +
    q0612 y z w*v0004 y z w +
    q0613 y z w*v0003 y z w +
    q0614 y z w*v0002 y z w +
    q0615 y z w*v0001 y z w +
    q0616 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0014Data r0202Data) (product q0015Data r0201Data)) (product q0016Data r0200Data)) (product q0113Data r0103Data)) (product q0114Data r0102Data)) (product q0115Data r0101Data)) (product q0116Data r0100Data)) (product q0211Data r0005Data)) (product q0213Data r0003Data)) (product q0214Data r0002Data)) (product q0215Data r0001Data)) (product q0216Data r0000Data)) (product q0408Data v0208Data)) (product q0409Data v0207Data)) (product q0410Data v0206Data)) (product q0411Data v0205Data)) (product q0412Data v0204Data)) (product q0413Data v0203Data)) (product q0414Data v0202Data)) (product q0415Data v0201Data)) (product q0416Data v0200Data)) (product q0506Data v0110Data)) (product q0507Data v0109Data)) (product q0508Data v0108Data)) (product q0509Data v0107Data)) (product q0510Data v0106Data)) (product q0511Data v0105Data)) (product q0512Data v0104Data)) (product q0513Data v0103Data)) (product q0514Data v0102Data)) (product q0515Data v0101Data)) (product q0516Data v0100Data)) (product q0605Data v0011Data)) (product q0606Data v0010Data)) (product q0607Data v0009Data)) (product q0608Data v0008Data)) (product q0609Data v0007Data)) (product q0610Data v0006Data)) (product q0611Data v0005Data)) (product q0612Data v0004Data)) (product q0613Data v0003Data)) (product q0614Data v0002Data)) (product q0615Data v0001Data)) (product q0616Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0014, q0015, q0016, q0113, q0114, q0115, q0116, q0211, q0213, q0214, q0215, q0216, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0605, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x16

compact_certificate theorem row2_x17 (y z w : ℂ) :
    q0015 y z w*r0202 y z w +
    q0016 y z w*r0201 y z w +
    q0017 y z w*r0200 y z w +
    q0114 y z w*r0103 y z w +
    q0115 y z w*r0102 y z w +
    q0116 y z w*r0101 y z w +
    q0117 y z w*r0100 y z w +
    q0212 y z w*r0005 y z w +
    q0214 y z w*r0003 y z w +
    q0215 y z w*r0002 y z w +
    q0216 y z w*r0001 y z w +
    q0217 y z w*r0000 y z w +
    q0409 y z w*v0208 y z w +
    q0410 y z w*v0207 y z w +
    q0411 y z w*v0206 y z w +
    q0412 y z w*v0205 y z w +
    q0413 y z w*v0204 y z w +
    q0414 y z w*v0203 y z w +
    q0415 y z w*v0202 y z w +
    q0416 y z w*v0201 y z w +
    q0417 y z w*v0200 y z w +
    q0507 y z w*v0110 y z w +
    q0508 y z w*v0109 y z w +
    q0509 y z w*v0108 y z w +
    q0510 y z w*v0107 y z w +
    q0511 y z w*v0106 y z w +
    q0512 y z w*v0105 y z w +
    q0513 y z w*v0104 y z w +
    q0514 y z w*v0103 y z w +
    q0515 y z w*v0102 y z w +
    q0516 y z w*v0101 y z w +
    q0517 y z w*v0100 y z w +
    q0606 y z w*v0011 y z w +
    q0607 y z w*v0010 y z w +
    q0608 y z w*v0009 y z w +
    q0609 y z w*v0008 y z w +
    q0610 y z w*v0007 y z w +
    q0611 y z w*v0006 y z w +
    q0612 y z w*v0005 y z w +
    q0613 y z w*v0004 y z w +
    q0614 y z w*v0003 y z w +
    q0615 y z w*v0002 y z w +
    q0616 y z w*v0001 y z w +
    q0617 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0015Data r0202Data) (product q0016Data r0201Data)) (product q0017Data r0200Data)) (product q0114Data r0103Data)) (product q0115Data r0102Data)) (product q0116Data r0101Data)) (product q0117Data r0100Data)) (product q0212Data r0005Data)) (product q0214Data r0003Data)) (product q0215Data r0002Data)) (product q0216Data r0001Data)) (product q0217Data r0000Data)) (product q0409Data v0208Data)) (product q0410Data v0207Data)) (product q0411Data v0206Data)) (product q0412Data v0205Data)) (product q0413Data v0204Data)) (product q0414Data v0203Data)) (product q0415Data v0202Data)) (product q0416Data v0201Data)) (product q0417Data v0200Data)) (product q0507Data v0110Data)) (product q0508Data v0109Data)) (product q0509Data v0108Data)) (product q0510Data v0107Data)) (product q0511Data v0106Data)) (product q0512Data v0105Data)) (product q0513Data v0104Data)) (product q0514Data v0103Data)) (product q0515Data v0102Data)) (product q0516Data v0101Data)) (product q0517Data v0100Data)) (product q0606Data v0011Data)) (product q0607Data v0010Data)) (product q0608Data v0009Data)) (product q0609Data v0008Data)) (product q0610Data v0007Data)) (product q0611Data v0006Data)) (product q0612Data v0005Data)) (product q0613Data v0004Data)) (product q0614Data v0003Data)) (product q0615Data v0002Data)) (product q0616Data v0001Data)) (product q0617Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0015, q0016, q0017, q0114, q0115, q0116, q0117, q0212, q0214, q0215, q0216, q0217, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0606, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x17

compact_certificate theorem row2_x18 (y z w : ℂ) :
    q0016 y z w*r0202 y z w +
    q0017 y z w*r0201 y z w +
    q0018 y z w*r0200 y z w +
    q0115 y z w*r0103 y z w +
    q0116 y z w*r0102 y z w +
    q0117 y z w*r0101 y z w +
    q0118 y z w*r0100 y z w +
    q0213 y z w*r0005 y z w +
    q0215 y z w*r0003 y z w +
    q0216 y z w*r0002 y z w +
    q0217 y z w*r0001 y z w +
    q0218 y z w*r0000 y z w +
    q0410 y z w*v0208 y z w +
    q0411 y z w*v0207 y z w +
    q0412 y z w*v0206 y z w +
    q0413 y z w*v0205 y z w +
    q0414 y z w*v0204 y z w +
    q0415 y z w*v0203 y z w +
    q0416 y z w*v0202 y z w +
    q0417 y z w*v0201 y z w +
    q0418 y z w*v0200 y z w +
    q0508 y z w*v0110 y z w +
    q0509 y z w*v0109 y z w +
    q0510 y z w*v0108 y z w +
    q0511 y z w*v0107 y z w +
    q0512 y z w*v0106 y z w +
    q0513 y z w*v0105 y z w +
    q0514 y z w*v0104 y z w +
    q0515 y z w*v0103 y z w +
    q0516 y z w*v0102 y z w +
    q0517 y z w*v0101 y z w +
    q0518 y z w*v0100 y z w +
    q0607 y z w*v0011 y z w +
    q0608 y z w*v0010 y z w +
    q0609 y z w*v0009 y z w +
    q0610 y z w*v0008 y z w +
    q0611 y z w*v0007 y z w +
    q0612 y z w*v0006 y z w +
    q0613 y z w*v0005 y z w +
    q0614 y z w*v0004 y z w +
    q0615 y z w*v0003 y z w +
    q0616 y z w*v0002 y z w +
    q0617 y z w*v0001 y z w +
    q0618 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0016Data r0202Data) (product q0017Data r0201Data)) (product q0018Data r0200Data)) (product q0115Data r0103Data)) (product q0116Data r0102Data)) (product q0117Data r0101Data)) (product q0118Data r0100Data)) (product q0213Data r0005Data)) (product q0215Data r0003Data)) (product q0216Data r0002Data)) (product q0217Data r0001Data)) (product q0218Data r0000Data)) (product q0410Data v0208Data)) (product q0411Data v0207Data)) (product q0412Data v0206Data)) (product q0413Data v0205Data)) (product q0414Data v0204Data)) (product q0415Data v0203Data)) (product q0416Data v0202Data)) (product q0417Data v0201Data)) (product q0418Data v0200Data)) (product q0508Data v0110Data)) (product q0509Data v0109Data)) (product q0510Data v0108Data)) (product q0511Data v0107Data)) (product q0512Data v0106Data)) (product q0513Data v0105Data)) (product q0514Data v0104Data)) (product q0515Data v0103Data)) (product q0516Data v0102Data)) (product q0517Data v0101Data)) (product q0518Data v0100Data)) (product q0607Data v0011Data)) (product q0608Data v0010Data)) (product q0609Data v0009Data)) (product q0610Data v0008Data)) (product q0611Data v0007Data)) (product q0612Data v0006Data)) (product q0613Data v0005Data)) (product q0614Data v0004Data)) (product q0615Data v0003Data)) (product q0616Data v0002Data)) (product q0617Data v0001Data)) (product q0618Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0016, q0017, q0018, q0115, q0116, q0117, q0118, q0213, q0215, q0216, q0217, q0218, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0607, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x18

compact_certificate theorem row2_x19 (y z w : ℂ) :
    q0017 y z w*r0202 y z w +
    q0018 y z w*r0201 y z w +
    q0019 y z w*r0200 y z w +
    q0116 y z w*r0103 y z w +
    q0117 y z w*r0102 y z w +
    q0118 y z w*r0101 y z w +
    q0119 y z w*r0100 y z w +
    q0214 y z w*r0005 y z w +
    q0216 y z w*r0003 y z w +
    q0217 y z w*r0002 y z w +
    q0218 y z w*r0001 y z w +
    q0219 y z w*r0000 y z w +
    q0411 y z w*v0208 y z w +
    q0412 y z w*v0207 y z w +
    q0413 y z w*v0206 y z w +
    q0414 y z w*v0205 y z w +
    q0415 y z w*v0204 y z w +
    q0416 y z w*v0203 y z w +
    q0417 y z w*v0202 y z w +
    q0418 y z w*v0201 y z w +
    q0419 y z w*v0200 y z w +
    q0509 y z w*v0110 y z w +
    q0510 y z w*v0109 y z w +
    q0511 y z w*v0108 y z w +
    q0512 y z w*v0107 y z w +
    q0513 y z w*v0106 y z w +
    q0514 y z w*v0105 y z w +
    q0515 y z w*v0104 y z w +
    q0516 y z w*v0103 y z w +
    q0517 y z w*v0102 y z w +
    q0518 y z w*v0101 y z w +
    q0519 y z w*v0100 y z w +
    q0608 y z w*v0011 y z w +
    q0609 y z w*v0010 y z w +
    q0610 y z w*v0009 y z w +
    q0611 y z w*v0008 y z w +
    q0612 y z w*v0007 y z w +
    q0613 y z w*v0006 y z w +
    q0614 y z w*v0005 y z w +
    q0615 y z w*v0004 y z w +
    q0616 y z w*v0003 y z w +
    q0617 y z w*v0002 y z w +
    q0618 y z w*v0001 y z w +
    q0619 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0017Data r0202Data) (product q0018Data r0201Data)) (product q0019Data r0200Data)) (product q0116Data r0103Data)) (product q0117Data r0102Data)) (product q0118Data r0101Data)) (product q0119Data r0100Data)) (product q0214Data r0005Data)) (product q0216Data r0003Data)) (product q0217Data r0002Data)) (product q0218Data r0001Data)) (product q0219Data r0000Data)) (product q0411Data v0208Data)) (product q0412Data v0207Data)) (product q0413Data v0206Data)) (product q0414Data v0205Data)) (product q0415Data v0204Data)) (product q0416Data v0203Data)) (product q0417Data v0202Data)) (product q0418Data v0201Data)) (product q0419Data v0200Data)) (product q0509Data v0110Data)) (product q0510Data v0109Data)) (product q0511Data v0108Data)) (product q0512Data v0107Data)) (product q0513Data v0106Data)) (product q0514Data v0105Data)) (product q0515Data v0104Data)) (product q0516Data v0103Data)) (product q0517Data v0102Data)) (product q0518Data v0101Data)) (product q0519Data v0100Data)) (product q0608Data v0011Data)) (product q0609Data v0010Data)) (product q0610Data v0009Data)) (product q0611Data v0008Data)) (product q0612Data v0007Data)) (product q0613Data v0006Data)) (product q0614Data v0005Data)) (product q0615Data v0004Data)) (product q0616Data v0003Data)) (product q0617Data v0002Data)) (product q0618Data v0001Data)) (product q0619Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0017, q0018, q0019, q0116, q0117, q0118, q0119, q0214, q0216, q0217, q0218, q0219, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0608, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x19

compact_certificate theorem row2_x20 (y z w : ℂ) :
    q0018 y z w*r0202 y z w +
    q0019 y z w*r0201 y z w +
    q0020 y z w*r0200 y z w +
    q0117 y z w*r0103 y z w +
    q0118 y z w*r0102 y z w +
    q0119 y z w*r0101 y z w +
    q0120 y z w*r0100 y z w +
    q0215 y z w*r0005 y z w +
    q0217 y z w*r0003 y z w +
    q0218 y z w*r0002 y z w +
    q0219 y z w*r0001 y z w +
    q0220 y z w*r0000 y z w +
    q0412 y z w*v0208 y z w +
    q0413 y z w*v0207 y z w +
    q0414 y z w*v0206 y z w +
    q0415 y z w*v0205 y z w +
    q0416 y z w*v0204 y z w +
    q0417 y z w*v0203 y z w +
    q0418 y z w*v0202 y z w +
    q0419 y z w*v0201 y z w +
    q0420 y z w*v0200 y z w +
    q0510 y z w*v0110 y z w +
    q0511 y z w*v0109 y z w +
    q0512 y z w*v0108 y z w +
    q0513 y z w*v0107 y z w +
    q0514 y z w*v0106 y z w +
    q0515 y z w*v0105 y z w +
    q0516 y z w*v0104 y z w +
    q0517 y z w*v0103 y z w +
    q0518 y z w*v0102 y z w +
    q0519 y z w*v0101 y z w +
    q0520 y z w*v0100 y z w +
    q0609 y z w*v0011 y z w +
    q0610 y z w*v0010 y z w +
    q0611 y z w*v0009 y z w +
    q0612 y z w*v0008 y z w +
    q0613 y z w*v0007 y z w +
    q0614 y z w*v0006 y z w +
    q0615 y z w*v0005 y z w +
    q0616 y z w*v0004 y z w +
    q0617 y z w*v0003 y z w +
    q0618 y z w*v0002 y z w +
    q0619 y z w*v0001 y z w +
    q0620 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0018Data r0202Data) (product q0019Data r0201Data)) (product q0020Data r0200Data)) (product q0117Data r0103Data)) (product q0118Data r0102Data)) (product q0119Data r0101Data)) (product q0120Data r0100Data)) (product q0215Data r0005Data)) (product q0217Data r0003Data)) (product q0218Data r0002Data)) (product q0219Data r0001Data)) (product q0220Data r0000Data)) (product q0412Data v0208Data)) (product q0413Data v0207Data)) (product q0414Data v0206Data)) (product q0415Data v0205Data)) (product q0416Data v0204Data)) (product q0417Data v0203Data)) (product q0418Data v0202Data)) (product q0419Data v0201Data)) (product q0420Data v0200Data)) (product q0510Data v0110Data)) (product q0511Data v0109Data)) (product q0512Data v0108Data)) (product q0513Data v0107Data)) (product q0514Data v0106Data)) (product q0515Data v0105Data)) (product q0516Data v0104Data)) (product q0517Data v0103Data)) (product q0518Data v0102Data)) (product q0519Data v0101Data)) (product q0520Data v0100Data)) (product q0609Data v0011Data)) (product q0610Data v0010Data)) (product q0611Data v0009Data)) (product q0612Data v0008Data)) (product q0613Data v0007Data)) (product q0614Data v0006Data)) (product q0615Data v0005Data)) (product q0616Data v0004Data)) (product q0617Data v0003Data)) (product q0618Data v0002Data)) (product q0619Data v0001Data)) (product q0620Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0018, q0019, q0020, q0117, q0118, q0119, q0120, q0215, q0217, q0218, q0219, q0220, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0609, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x20

compact_certificate theorem row2_x21 (y z w : ℂ) :
    q0019 y z w*r0202 y z w +
    q0020 y z w*r0201 y z w +
    q0021 y z w*r0200 y z w +
    q0118 y z w*r0103 y z w +
    q0119 y z w*r0102 y z w +
    q0120 y z w*r0101 y z w +
    q0121 y z w*r0100 y z w +
    q0216 y z w*r0005 y z w +
    q0218 y z w*r0003 y z w +
    q0219 y z w*r0002 y z w +
    q0220 y z w*r0001 y z w +
    q0221 y z w*r0000 y z w +
    q0413 y z w*v0208 y z w +
    q0414 y z w*v0207 y z w +
    q0415 y z w*v0206 y z w +
    q0416 y z w*v0205 y z w +
    q0417 y z w*v0204 y z w +
    q0418 y z w*v0203 y z w +
    q0419 y z w*v0202 y z w +
    q0420 y z w*v0201 y z w +
    q0421 y z w*v0200 y z w +
    q0511 y z w*v0110 y z w +
    q0512 y z w*v0109 y z w +
    q0513 y z w*v0108 y z w +
    q0514 y z w*v0107 y z w +
    q0515 y z w*v0106 y z w +
    q0516 y z w*v0105 y z w +
    q0517 y z w*v0104 y z w +
    q0518 y z w*v0103 y z w +
    q0519 y z w*v0102 y z w +
    q0520 y z w*v0101 y z w +
    q0521 y z w*v0100 y z w +
    q0610 y z w*v0011 y z w +
    q0611 y z w*v0010 y z w +
    q0612 y z w*v0009 y z w +
    q0613 y z w*v0008 y z w +
    q0614 y z w*v0007 y z w +
    q0615 y z w*v0006 y z w +
    q0616 y z w*v0005 y z w +
    q0617 y z w*v0004 y z w +
    q0618 y z w*v0003 y z w +
    q0619 y z w*v0002 y z w +
    q0620 y z w*v0001 y z w +
    q0621 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0019Data r0202Data) (product q0020Data r0201Data)) (product q0021Data r0200Data)) (product q0118Data r0103Data)) (product q0119Data r0102Data)) (product q0120Data r0101Data)) (product q0121Data r0100Data)) (product q0216Data r0005Data)) (product q0218Data r0003Data)) (product q0219Data r0002Data)) (product q0220Data r0001Data)) (product q0221Data r0000Data)) (product q0413Data v0208Data)) (product q0414Data v0207Data)) (product q0415Data v0206Data)) (product q0416Data v0205Data)) (product q0417Data v0204Data)) (product q0418Data v0203Data)) (product q0419Data v0202Data)) (product q0420Data v0201Data)) (product q0421Data v0200Data)) (product q0511Data v0110Data)) (product q0512Data v0109Data)) (product q0513Data v0108Data)) (product q0514Data v0107Data)) (product q0515Data v0106Data)) (product q0516Data v0105Data)) (product q0517Data v0104Data)) (product q0518Data v0103Data)) (product q0519Data v0102Data)) (product q0520Data v0101Data)) (product q0521Data v0100Data)) (product q0610Data v0011Data)) (product q0611Data v0010Data)) (product q0612Data v0009Data)) (product q0613Data v0008Data)) (product q0614Data v0007Data)) (product q0615Data v0006Data)) (product q0616Data v0005Data)) (product q0617Data v0004Data)) (product q0618Data v0003Data)) (product q0619Data v0002Data)) (product q0620Data v0001Data)) (product q0621Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0019, q0020, q0021, q0118, q0119, q0120, q0121, q0216, q0218, q0219, q0220, q0221, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0610, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x21

compact_certificate theorem row2_x22 (y z w : ℂ) :
    q0020 y z w*r0202 y z w +
    q0021 y z w*r0201 y z w +
    q0022 y z w*r0200 y z w +
    q0119 y z w*r0103 y z w +
    q0120 y z w*r0102 y z w +
    q0121 y z w*r0101 y z w +
    q0122 y z w*r0100 y z w +
    q0217 y z w*r0005 y z w +
    q0219 y z w*r0003 y z w +
    q0220 y z w*r0002 y z w +
    q0221 y z w*r0001 y z w +
    q0222 y z w*r0000 y z w +
    q0414 y z w*v0208 y z w +
    q0415 y z w*v0207 y z w +
    q0416 y z w*v0206 y z w +
    q0417 y z w*v0205 y z w +
    q0418 y z w*v0204 y z w +
    q0419 y z w*v0203 y z w +
    q0420 y z w*v0202 y z w +
    q0421 y z w*v0201 y z w +
    q0422 y z w*v0200 y z w +
    q0512 y z w*v0110 y z w +
    q0513 y z w*v0109 y z w +
    q0514 y z w*v0108 y z w +
    q0515 y z w*v0107 y z w +
    q0516 y z w*v0106 y z w +
    q0517 y z w*v0105 y z w +
    q0518 y z w*v0104 y z w +
    q0519 y z w*v0103 y z w +
    q0520 y z w*v0102 y z w +
    q0521 y z w*v0101 y z w +
    q0522 y z w*v0100 y z w +
    q0611 y z w*v0011 y z w +
    q0612 y z w*v0010 y z w +
    q0613 y z w*v0009 y z w +
    q0614 y z w*v0008 y z w +
    q0615 y z w*v0007 y z w +
    q0616 y z w*v0006 y z w +
    q0617 y z w*v0005 y z w +
    q0618 y z w*v0004 y z w +
    q0619 y z w*v0003 y z w +
    q0620 y z w*v0002 y z w +
    q0621 y z w*v0001 y z w +
    q0622 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0020Data r0202Data) (product q0021Data r0201Data)) (product q0022Data r0200Data)) (product q0119Data r0103Data)) (product q0120Data r0102Data)) (product q0121Data r0101Data)) (product q0122Data r0100Data)) (product q0217Data r0005Data)) (product q0219Data r0003Data)) (product q0220Data r0002Data)) (product q0221Data r0001Data)) (product q0222Data r0000Data)) (product q0414Data v0208Data)) (product q0415Data v0207Data)) (product q0416Data v0206Data)) (product q0417Data v0205Data)) (product q0418Data v0204Data)) (product q0419Data v0203Data)) (product q0420Data v0202Data)) (product q0421Data v0201Data)) (product q0422Data v0200Data)) (product q0512Data v0110Data)) (product q0513Data v0109Data)) (product q0514Data v0108Data)) (product q0515Data v0107Data)) (product q0516Data v0106Data)) (product q0517Data v0105Data)) (product q0518Data v0104Data)) (product q0519Data v0103Data)) (product q0520Data v0102Data)) (product q0521Data v0101Data)) (product q0522Data v0100Data)) (product q0611Data v0011Data)) (product q0612Data v0010Data)) (product q0613Data v0009Data)) (product q0614Data v0008Data)) (product q0615Data v0007Data)) (product q0616Data v0006Data)) (product q0617Data v0005Data)) (product q0618Data v0004Data)) (product q0619Data v0003Data)) (product q0620Data v0002Data)) (product q0621Data v0001Data)) (product q0622Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0020, q0021, q0022, q0119, q0120, q0121, q0122, q0217, q0219, q0220, q0221, q0222, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0611, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x22

compact_certificate theorem row2_x23 (y z w : ℂ) :
    q0021 y z w*r0202 y z w +
    q0022 y z w*r0201 y z w +
    q0023 y z w*r0200 y z w +
    q0120 y z w*r0103 y z w +
    q0121 y z w*r0102 y z w +
    q0122 y z w*r0101 y z w +
    q0123 y z w*r0100 y z w +
    q0218 y z w*r0005 y z w +
    q0220 y z w*r0003 y z w +
    q0221 y z w*r0002 y z w +
    q0222 y z w*r0001 y z w +
    q0223 y z w*r0000 y z w +
    q0415 y z w*v0208 y z w +
    q0416 y z w*v0207 y z w +
    q0417 y z w*v0206 y z w +
    q0418 y z w*v0205 y z w +
    q0419 y z w*v0204 y z w +
    q0420 y z w*v0203 y z w +
    q0421 y z w*v0202 y z w +
    q0422 y z w*v0201 y z w +
    q0423 y z w*v0200 y z w +
    q0513 y z w*v0110 y z w +
    q0514 y z w*v0109 y z w +
    q0515 y z w*v0108 y z w +
    q0516 y z w*v0107 y z w +
    q0517 y z w*v0106 y z w +
    q0518 y z w*v0105 y z w +
    q0519 y z w*v0104 y z w +
    q0520 y z w*v0103 y z w +
    q0521 y z w*v0102 y z w +
    q0522 y z w*v0101 y z w +
    q0523 y z w*v0100 y z w +
    q0612 y z w*v0011 y z w +
    q0613 y z w*v0010 y z w +
    q0614 y z w*v0009 y z w +
    q0615 y z w*v0008 y z w +
    q0616 y z w*v0007 y z w +
    q0617 y z w*v0006 y z w +
    q0618 y z w*v0005 y z w +
    q0619 y z w*v0004 y z w +
    q0620 y z w*v0003 y z w +
    q0621 y z w*v0002 y z w +
    q0622 y z w*v0001 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0021Data r0202Data) (product q0022Data r0201Data)) (product q0023Data r0200Data)) (product q0120Data r0103Data)) (product q0121Data r0102Data)) (product q0122Data r0101Data)) (product q0123Data r0100Data)) (product q0218Data r0005Data)) (product q0220Data r0003Data)) (product q0221Data r0002Data)) (product q0222Data r0001Data)) (product q0223Data r0000Data)) (product q0415Data v0208Data)) (product q0416Data v0207Data)) (product q0417Data v0206Data)) (product q0418Data v0205Data)) (product q0419Data v0204Data)) (product q0420Data v0203Data)) (product q0421Data v0202Data)) (product q0422Data v0201Data)) (product q0423Data v0200Data)) (product q0513Data v0110Data)) (product q0514Data v0109Data)) (product q0515Data v0108Data)) (product q0516Data v0107Data)) (product q0517Data v0106Data)) (product q0518Data v0105Data)) (product q0519Data v0104Data)) (product q0520Data v0103Data)) (product q0521Data v0102Data)) (product q0522Data v0101Data)) (product q0523Data v0100Data)) (product q0612Data v0011Data)) (product q0613Data v0010Data)) (product q0614Data v0009Data)) (product q0615Data v0008Data)) (product q0616Data v0007Data)) (product q0617Data v0006Data)) (product q0618Data v0005Data)) (product q0619Data v0004Data)) (product q0620Data v0003Data)) (product q0621Data v0002Data)) (product q0622Data v0001Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0021, q0022, q0023, q0120, q0121, q0122, q0123, q0218, q0220, q0221, q0222, q0223, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0612, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x23

compact_certificate theorem row2_x24 (y z w : ℂ) :
    q0022 y z w*r0202 y z w +
    q0023 y z w*r0201 y z w +
    q0024 y z w*r0200 y z w +
    q0121 y z w*r0103 y z w +
    q0122 y z w*r0102 y z w +
    q0123 y z w*r0101 y z w +
    q0124 y z w*r0100 y z w +
    q0219 y z w*r0005 y z w +
    q0221 y z w*r0003 y z w +
    q0222 y z w*r0002 y z w +
    q0223 y z w*r0001 y z w +
    q0224 y z w*r0000 y z w +
    q0416 y z w*v0208 y z w +
    q0417 y z w*v0207 y z w +
    q0418 y z w*v0206 y z w +
    q0419 y z w*v0205 y z w +
    q0420 y z w*v0204 y z w +
    q0421 y z w*v0203 y z w +
    q0422 y z w*v0202 y z w +
    q0423 y z w*v0201 y z w +
    q0424 y z w*v0200 y z w +
    q0514 y z w*v0110 y z w +
    q0515 y z w*v0109 y z w +
    q0516 y z w*v0108 y z w +
    q0517 y z w*v0107 y z w +
    q0518 y z w*v0106 y z w +
    q0519 y z w*v0105 y z w +
    q0520 y z w*v0104 y z w +
    q0521 y z w*v0103 y z w +
    q0522 y z w*v0102 y z w +
    q0523 y z w*v0101 y z w +
    q0613 y z w*v0011 y z w +
    q0614 y z w*v0010 y z w +
    q0615 y z w*v0009 y z w +
    q0616 y z w*v0008 y z w +
    q0617 y z w*v0007 y z w +
    q0618 y z w*v0006 y z w +
    q0619 y z w*v0005 y z w +
    q0620 y z w*v0004 y z w +
    q0621 y z w*v0003 y z w +
    q0622 y z w*v0002 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0022Data r0202Data) (product q0023Data r0201Data)) (product q0024Data r0200Data)) (product q0121Data r0103Data)) (product q0122Data r0102Data)) (product q0123Data r0101Data)) (product q0124Data r0100Data)) (product q0219Data r0005Data)) (product q0221Data r0003Data)) (product q0222Data r0002Data)) (product q0223Data r0001Data)) (product q0224Data r0000Data)) (product q0416Data v0208Data)) (product q0417Data v0207Data)) (product q0418Data v0206Data)) (product q0419Data v0205Data)) (product q0420Data v0204Data)) (product q0421Data v0203Data)) (product q0422Data v0202Data)) (product q0423Data v0201Data)) (product q0424Data v0200Data)) (product q0514Data v0110Data)) (product q0515Data v0109Data)) (product q0516Data v0108Data)) (product q0517Data v0107Data)) (product q0518Data v0106Data)) (product q0519Data v0105Data)) (product q0520Data v0104Data)) (product q0521Data v0103Data)) (product q0522Data v0102Data)) (product q0523Data v0101Data)) (product q0613Data v0011Data)) (product q0614Data v0010Data)) (product q0615Data v0009Data)) (product q0616Data v0008Data)) (product q0617Data v0007Data)) (product q0618Data v0006Data)) (product q0619Data v0005Data)) (product q0620Data v0004Data)) (product q0621Data v0003Data)) (product q0622Data v0002Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0022, q0023, q0024, q0121, q0122, q0123, q0124, q0219, q0221, q0222, q0223, q0224, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0613, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x24

compact_certificate theorem row2_x25 (y z w : ℂ) :
    q0023 y z w*r0202 y z w +
    q0024 y z w*r0201 y z w +
    q0025 y z w*r0200 y z w +
    q0122 y z w*r0103 y z w +
    q0123 y z w*r0102 y z w +
    q0124 y z w*r0101 y z w +
    q0125 y z w*r0100 y z w +
    q0220 y z w*r0005 y z w +
    q0222 y z w*r0003 y z w +
    q0223 y z w*r0002 y z w +
    q0224 y z w*r0001 y z w +
    q0225 y z w*r0000 y z w +
    q0417 y z w*v0208 y z w +
    q0418 y z w*v0207 y z w +
    q0419 y z w*v0206 y z w +
    q0420 y z w*v0205 y z w +
    q0421 y z w*v0204 y z w +
    q0422 y z w*v0203 y z w +
    q0423 y z w*v0202 y z w +
    q0424 y z w*v0201 y z w +
    q0515 y z w*v0110 y z w +
    q0516 y z w*v0109 y z w +
    q0517 y z w*v0108 y z w +
    q0518 y z w*v0107 y z w +
    q0519 y z w*v0106 y z w +
    q0520 y z w*v0105 y z w +
    q0521 y z w*v0104 y z w +
    q0522 y z w*v0103 y z w +
    q0523 y z w*v0102 y z w +
    q0614 y z w*v0011 y z w +
    q0615 y z w*v0010 y z w +
    q0616 y z w*v0009 y z w +
    q0617 y z w*v0008 y z w +
    q0618 y z w*v0007 y z w +
    q0619 y z w*v0006 y z w +
    q0620 y z w*v0005 y z w +
    q0621 y z w*v0004 y z w +
    q0622 y z w*v0003 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0023Data r0202Data) (product q0024Data r0201Data)) (product q0025Data r0200Data)) (product q0122Data r0103Data)) (product q0123Data r0102Data)) (product q0124Data r0101Data)) (product q0125Data r0100Data)) (product q0220Data r0005Data)) (product q0222Data r0003Data)) (product q0223Data r0002Data)) (product q0224Data r0001Data)) (product q0225Data r0000Data)) (product q0417Data v0208Data)) (product q0418Data v0207Data)) (product q0419Data v0206Data)) (product q0420Data v0205Data)) (product q0421Data v0204Data)) (product q0422Data v0203Data)) (product q0423Data v0202Data)) (product q0424Data v0201Data)) (product q0515Data v0110Data)) (product q0516Data v0109Data)) (product q0517Data v0108Data)) (product q0518Data v0107Data)) (product q0519Data v0106Data)) (product q0520Data v0105Data)) (product q0521Data v0104Data)) (product q0522Data v0103Data)) (product q0523Data v0102Data)) (product q0614Data v0011Data)) (product q0615Data v0010Data)) (product q0616Data v0009Data)) (product q0617Data v0008Data)) (product q0618Data v0007Data)) (product q0619Data v0006Data)) (product q0620Data v0005Data)) (product q0621Data v0004Data)) (product q0622Data v0003Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0023, q0024, q0025, q0122, q0123, q0124, q0125, q0220, q0222, q0223, q0224, q0225, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0614, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x25

compact_certificate theorem row2_x26 (y z w : ℂ) :
    q0024 y z w*r0202 y z w +
    q0025 y z w*r0201 y z w +
    q0026 y z w*r0200 y z w +
    q0123 y z w*r0103 y z w +
    q0124 y z w*r0102 y z w +
    q0125 y z w*r0101 y z w +
    q0126 y z w*r0100 y z w +
    q0221 y z w*r0005 y z w +
    q0223 y z w*r0003 y z w +
    q0224 y z w*r0002 y z w +
    q0225 y z w*r0001 y z w +
    q0226 y z w*r0000 y z w +
    q0418 y z w*v0208 y z w +
    q0419 y z w*v0207 y z w +
    q0420 y z w*v0206 y z w +
    q0421 y z w*v0205 y z w +
    q0422 y z w*v0204 y z w +
    q0423 y z w*v0203 y z w +
    q0424 y z w*v0202 y z w +
    q0516 y z w*v0110 y z w +
    q0517 y z w*v0109 y z w +
    q0518 y z w*v0108 y z w +
    q0519 y z w*v0107 y z w +
    q0520 y z w*v0106 y z w +
    q0521 y z w*v0105 y z w +
    q0522 y z w*v0104 y z w +
    q0523 y z w*v0103 y z w +
    q0615 y z w*v0011 y z w +
    q0616 y z w*v0010 y z w +
    q0617 y z w*v0009 y z w +
    q0618 y z w*v0008 y z w +
    q0619 y z w*v0007 y z w +
    q0620 y z w*v0006 y z w +
    q0621 y z w*v0005 y z w +
    q0622 y z w*v0004 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0024Data r0202Data) (product q0025Data r0201Data)) (product q0026Data r0200Data)) (product q0123Data r0103Data)) (product q0124Data r0102Data)) (product q0125Data r0101Data)) (product q0126Data r0100Data)) (product q0221Data r0005Data)) (product q0223Data r0003Data)) (product q0224Data r0002Data)) (product q0225Data r0001Data)) (product q0226Data r0000Data)) (product q0418Data v0208Data)) (product q0419Data v0207Data)) (product q0420Data v0206Data)) (product q0421Data v0205Data)) (product q0422Data v0204Data)) (product q0423Data v0203Data)) (product q0424Data v0202Data)) (product q0516Data v0110Data)) (product q0517Data v0109Data)) (product q0518Data v0108Data)) (product q0519Data v0107Data)) (product q0520Data v0106Data)) (product q0521Data v0105Data)) (product q0522Data v0104Data)) (product q0523Data v0103Data)) (product q0615Data v0011Data)) (product q0616Data v0010Data)) (product q0617Data v0009Data)) (product q0618Data v0008Data)) (product q0619Data v0007Data)) (product q0620Data v0006Data)) (product q0621Data v0005Data)) (product q0622Data v0004Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0024, q0025, q0026, q0123, q0124, q0125, q0126, q0221, q0223, q0224, q0225, q0226, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0615, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x26

compact_certificate theorem row2_x27 (y z w : ℂ) :
    q0025 y z w*r0202 y z w +
    q0026 y z w*r0201 y z w +
    q0027 y z w*r0200 y z w +
    q0124 y z w*r0103 y z w +
    q0125 y z w*r0102 y z w +
    q0126 y z w*r0101 y z w +
    q0127 y z w*r0100 y z w +
    q0222 y z w*r0005 y z w +
    q0224 y z w*r0003 y z w +
    q0225 y z w*r0002 y z w +
    q0226 y z w*r0001 y z w +
    q0227 y z w*r0000 y z w +
    q0419 y z w*v0208 y z w +
    q0420 y z w*v0207 y z w +
    q0421 y z w*v0206 y z w +
    q0422 y z w*v0205 y z w +
    q0423 y z w*v0204 y z w +
    q0424 y z w*v0203 y z w +
    q0517 y z w*v0110 y z w +
    q0518 y z w*v0109 y z w +
    q0519 y z w*v0108 y z w +
    q0520 y z w*v0107 y z w +
    q0521 y z w*v0106 y z w +
    q0522 y z w*v0105 y z w +
    q0523 y z w*v0104 y z w +
    q0616 y z w*v0011 y z w +
    q0617 y z w*v0010 y z w +
    q0618 y z w*v0009 y z w +
    q0619 y z w*v0008 y z w +
    q0620 y z w*v0007 y z w +
    q0621 y z w*v0006 y z w +
    q0622 y z w*v0005 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0025Data r0202Data) (product q0026Data r0201Data)) (product q0027Data r0200Data)) (product q0124Data r0103Data)) (product q0125Data r0102Data)) (product q0126Data r0101Data)) (product q0127Data r0100Data)) (product q0222Data r0005Data)) (product q0224Data r0003Data)) (product q0225Data r0002Data)) (product q0226Data r0001Data)) (product q0227Data r0000Data)) (product q0419Data v0208Data)) (product q0420Data v0207Data)) (product q0421Data v0206Data)) (product q0422Data v0205Data)) (product q0423Data v0204Data)) (product q0424Data v0203Data)) (product q0517Data v0110Data)) (product q0518Data v0109Data)) (product q0519Data v0108Data)) (product q0520Data v0107Data)) (product q0521Data v0106Data)) (product q0522Data v0105Data)) (product q0523Data v0104Data)) (product q0616Data v0011Data)) (product q0617Data v0010Data)) (product q0618Data v0009Data)) (product q0619Data v0008Data)) (product q0620Data v0007Data)) (product q0621Data v0006Data)) (product q0622Data v0005Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0025, q0026, q0027, q0124, q0125, q0126, q0127, q0222, q0224, q0225, q0226, q0227, q0419, q0420, q0421, q0422, q0423, q0424, q0517, q0518, q0519, q0520, q0521, q0522, q0523, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x27

compact_certificate theorem row2_x28 (y z w : ℂ) :
    q0026 y z w*r0202 y z w +
    q0027 y z w*r0201 y z w +
    q0028 y z w*r0200 y z w +
    q0125 y z w*r0103 y z w +
    q0126 y z w*r0102 y z w +
    q0127 y z w*r0101 y z w +
    q0128 y z w*r0100 y z w +
    q0223 y z w*r0005 y z w +
    q0225 y z w*r0003 y z w +
    q0226 y z w*r0002 y z w +
    q0227 y z w*r0001 y z w +
    q0228 y z w*r0000 y z w +
    q0420 y z w*v0208 y z w +
    q0421 y z w*v0207 y z w +
    q0422 y z w*v0206 y z w +
    q0423 y z w*v0205 y z w +
    q0424 y z w*v0204 y z w +
    q0518 y z w*v0110 y z w +
    q0519 y z w*v0109 y z w +
    q0520 y z w*v0108 y z w +
    q0521 y z w*v0107 y z w +
    q0522 y z w*v0106 y z w +
    q0523 y z w*v0105 y z w +
    q0617 y z w*v0011 y z w +
    q0618 y z w*v0010 y z w +
    q0619 y z w*v0009 y z w +
    q0620 y z w*v0008 y z w +
    q0621 y z w*v0007 y z w +
    q0622 y z w*v0006 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0026Data r0202Data) (product q0027Data r0201Data)) (product q0028Data r0200Data)) (product q0125Data r0103Data)) (product q0126Data r0102Data)) (product q0127Data r0101Data)) (product q0128Data r0100Data)) (product q0223Data r0005Data)) (product q0225Data r0003Data)) (product q0226Data r0002Data)) (product q0227Data r0001Data)) (product q0228Data r0000Data)) (product q0420Data v0208Data)) (product q0421Data v0207Data)) (product q0422Data v0206Data)) (product q0423Data v0205Data)) (product q0424Data v0204Data)) (product q0518Data v0110Data)) (product q0519Data v0109Data)) (product q0520Data v0108Data)) (product q0521Data v0107Data)) (product q0522Data v0106Data)) (product q0523Data v0105Data)) (product q0617Data v0011Data)) (product q0618Data v0010Data)) (product q0619Data v0009Data)) (product q0620Data v0008Data)) (product q0621Data v0007Data)) (product q0622Data v0006Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0026, q0027, q0028, q0125, q0126, q0127, q0128, q0223, q0225, q0226, q0227, q0228, q0420, q0421, q0422, q0423, q0424, q0518, q0519, q0520, q0521, q0522, q0523, q0617, q0618, q0619, q0620, q0621, q0622, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0006, v0007, v0008, v0009, v0010, v0011, v0105, v0106, v0107, v0108, v0109, v0110, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x28

compact_certificate theorem row2_x29 (y z w : ℂ) :
    q0027 y z w*r0202 y z w +
    q0028 y z w*r0201 y z w +
    q0029 y z w*r0200 y z w +
    q0126 y z w*r0103 y z w +
    q0127 y z w*r0102 y z w +
    q0128 y z w*r0101 y z w +
    q0129 y z w*r0100 y z w +
    q0224 y z w*r0005 y z w +
    q0226 y z w*r0003 y z w +
    q0227 y z w*r0002 y z w +
    q0228 y z w*r0001 y z w +
    q0421 y z w*v0208 y z w +
    q0422 y z w*v0207 y z w +
    q0423 y z w*v0206 y z w +
    q0424 y z w*v0205 y z w +
    q0519 y z w*v0110 y z w +
    q0520 y z w*v0109 y z w +
    q0521 y z w*v0108 y z w +
    q0522 y z w*v0107 y z w +
    q0523 y z w*v0106 y z w +
    q0618 y z w*v0011 y z w +
    q0619 y z w*v0010 y z w +
    q0620 y z w*v0009 y z w +
    q0621 y z w*v0008 y z w +
    q0622 y z w*v0007 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0027Data r0202Data) (product q0028Data r0201Data)) (product q0029Data r0200Data)) (product q0126Data r0103Data)) (product q0127Data r0102Data)) (product q0128Data r0101Data)) (product q0129Data r0100Data)) (product q0224Data r0005Data)) (product q0226Data r0003Data)) (product q0227Data r0002Data)) (product q0228Data r0001Data)) (product q0421Data v0208Data)) (product q0422Data v0207Data)) (product q0423Data v0206Data)) (product q0424Data v0205Data)) (product q0519Data v0110Data)) (product q0520Data v0109Data)) (product q0521Data v0108Data)) (product q0522Data v0107Data)) (product q0523Data v0106Data)) (product q0618Data v0011Data)) (product q0619Data v0010Data)) (product q0620Data v0009Data)) (product q0621Data v0008Data)) (product q0622Data v0007Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0027, q0028, q0029, q0126, q0127, q0128, q0129, q0224, q0226, q0227, q0228, q0421, q0422, q0423, q0424, q0519, q0520, q0521, q0522, q0523, q0618, q0619, q0620, q0621, q0622, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0007, v0008, v0009, v0010, v0011, v0106, v0107, v0108, v0109, v0110, v0205, v0206, v0207, v0208] using he

#print axioms row2_x29

compact_certificate theorem row2_x30 (y z w : ℂ) :
    q0028 y z w*r0202 y z w +
    q0029 y z w*r0201 y z w +
    q0030 y z w*r0200 y z w +
    q0127 y z w*r0103 y z w +
    q0128 y z w*r0102 y z w +
    q0129 y z w*r0101 y z w +
    q0225 y z w*r0005 y z w +
    q0227 y z w*r0003 y z w +
    q0228 y z w*r0002 y z w +
    q0422 y z w*v0208 y z w +
    q0423 y z w*v0207 y z w +
    q0424 y z w*v0206 y z w +
    q0520 y z w*v0110 y z w +
    q0521 y z w*v0109 y z w +
    q0522 y z w*v0108 y z w +
    q0523 y z w*v0107 y z w +
    q0619 y z w*v0011 y z w +
    q0620 y z w*v0010 y z w +
    q0621 y z w*v0009 y z w +
    q0622 y z w*v0008 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0028Data r0202Data) (product q0029Data r0201Data)) (product q0030Data r0200Data)) (product q0127Data r0103Data)) (product q0128Data r0102Data)) (product q0129Data r0101Data)) (product q0225Data r0005Data)) (product q0227Data r0003Data)) (product q0228Data r0002Data)) (product q0422Data v0208Data)) (product q0423Data v0207Data)) (product q0424Data v0206Data)) (product q0520Data v0110Data)) (product q0521Data v0109Data)) (product q0522Data v0108Data)) (product q0523Data v0107Data)) (product q0619Data v0011Data)) (product q0620Data v0010Data)) (product q0621Data v0009Data)) (product q0622Data v0008Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0028, q0029, q0030, q0127, q0128, q0129, q0225, q0227, q0228, q0422, q0423, q0424, q0520, q0521, q0522, q0523, q0619, q0620, q0621, q0622, r0002, r0003, r0005, r0101, r0102, r0103, r0200, r0201, r0202, v0008, v0009, v0010, v0011, v0107, v0108, v0109, v0110, v0206, v0207, v0208] using he

#print axioms row2_x30

compact_certificate theorem row2_x31 (y z w : ℂ) :
    q0029 y z w*r0202 y z w +
    q0030 y z w*r0201 y z w +
    q0128 y z w*r0103 y z w +
    q0129 y z w*r0102 y z w +
    q0226 y z w*r0005 y z w +
    q0228 y z w*r0003 y z w +
    q0423 y z w*v0208 y z w +
    q0424 y z w*v0207 y z w +
    q0521 y z w*v0110 y z w +
    q0522 y z w*v0109 y z w +
    q0523 y z w*v0108 y z w +
    q0620 y z w*v0011 y z w +
    q0621 y z w*v0010 y z w +
    q0622 y z w*v0009 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0029Data r0202Data) (product q0030Data r0201Data)) (product q0128Data r0103Data)) (product q0129Data r0102Data)) (product q0226Data r0005Data)) (product q0228Data r0003Data)) (product q0423Data v0208Data)) (product q0424Data v0207Data)) (product q0521Data v0110Data)) (product q0522Data v0109Data)) (product q0523Data v0108Data)) (product q0620Data v0011Data)) (product q0621Data v0010Data)) (product q0622Data v0009Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0029, q0030, q0128, q0129, q0226, q0228, q0423, q0424, q0521, q0522, q0523, q0620, q0621, q0622, r0003, r0005, r0102, r0103, r0201, r0202, v0009, v0010, v0011, v0108, v0109, v0110, v0207, v0208] using he

#print axioms row2_x31

compact_certificate theorem row2_x32 (y z w : ℂ) :
    q0030 y z w*r0202 y z w +
    q0129 y z w*r0103 y z w +
    q0227 y z w*r0005 y z w +
    q0424 y z w*v0208 y z w +
    q0522 y z w*v0110 y z w +
    q0523 y z w*v0109 y z w +
    q0621 y z w*v0011 y z w +
    q0622 y z w*v0010 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0030Data r0202Data) (product q0129Data r0103Data)) (product q0227Data r0005Data)) (product q0424Data v0208Data)) (product q0522Data v0110Data)) (product q0523Data v0109Data)) (product q0621Data v0011Data)) (product q0622Data v0010Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0030, q0129, q0227, q0424, q0522, q0523, q0621, q0622, r0005, r0103, r0202, v0010, v0011, v0109, v0110, v0208] using he

#print axioms row2_x32

compact_certificate theorem row2_x33 (y z w : ℂ) :
    q0228 y z w*r0005 y z w +
    q0523 y z w*v0110 y z w +
    q0622 y z w*v0011 y z w=0 := by
  have h : (merge (merge (product q0228Data r0005Data) (product q0523Data v0110Data)) (product q0622Data v0011Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0228, q0523, q0622, r0005, v0011, v0110] using he

#print axioms row2_x33

compact_certificate theorem row2_coefficient00 (y z w : ℂ) : (rowPoly2 y z w).coeff 0=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x00 y z w

#print axioms row2_coefficient00

compact_certificate theorem row2_coefficient01 (y z w : ℂ) : (rowPoly2 y z w).coeff 1=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x01 y z w

#print axioms row2_coefficient01

compact_certificate theorem row2_coefficient02 (y z w : ℂ) : (rowPoly2 y z w).coeff 2=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x02 y z w

#print axioms row2_coefficient02

compact_certificate theorem row2_coefficient03 (y z w : ℂ) : (rowPoly2 y z w).coeff 3=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x03 y z w

#print axioms row2_coefficient03

compact_certificate theorem row2_coefficient04 (y z w : ℂ) : (rowPoly2 y z w).coeff 4=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x04 y z w

#print axioms row2_coefficient04

compact_certificate theorem row2_coefficient05 (y z w : ℂ) : (rowPoly2 y z w).coeff 5=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x05 y z w

#print axioms row2_coefficient05

compact_certificate theorem row2_coefficient06 (y z w : ℂ) : (rowPoly2 y z w).coeff 6=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x06 y z w

#print axioms row2_coefficient06

compact_certificate theorem row2_coefficient07 (y z w : ℂ) : (rowPoly2 y z w).coeff 7=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x07 y z w

#print axioms row2_coefficient07

compact_certificate theorem row2_coefficient08 (y z w : ℂ) : (rowPoly2 y z w).coeff 8=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x08 y z w

#print axioms row2_coefficient08

compact_certificate theorem row2_coefficient09 (y z w : ℂ) : (rowPoly2 y z w).coeff 9=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x09 y z w

#print axioms row2_coefficient09

compact_certificate theorem row2_coefficient10 (y z w : ℂ) : (rowPoly2 y z w).coeff 10=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x10 y z w

#print axioms row2_coefficient10

compact_certificate theorem row2_coefficient11 (y z w : ℂ) : (rowPoly2 y z w).coeff 11=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x11 y z w

#print axioms row2_coefficient11

compact_certificate theorem row2_coefficient12 (y z w : ℂ) : (rowPoly2 y z w).coeff 12=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x12 y z w

#print axioms row2_coefficient12

compact_certificate theorem row2_coefficient13 (y z w : ℂ) : (rowPoly2 y z w).coeff 13=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x13 y z w

#print axioms row2_coefficient13

compact_certificate theorem row2_coefficient14 (y z w : ℂ) : (rowPoly2 y z w).coeff 14=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x14 y z w

#print axioms row2_coefficient14

compact_certificate theorem row2_coefficient15 (y z w : ℂ) : (rowPoly2 y z w).coeff 15=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x15 y z w

#print axioms row2_coefficient15

compact_certificate theorem row2_coefficient16 (y z w : ℂ) : (rowPoly2 y z w).coeff 16=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x16 y z w

#print axioms row2_coefficient16

compact_certificate theorem row2_coefficient17 (y z w : ℂ) : (rowPoly2 y z w).coeff 17=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x17 y z w

#print axioms row2_coefficient17

compact_certificate theorem row2_coefficient18 (y z w : ℂ) : (rowPoly2 y z w).coeff 18=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x18 y z w

#print axioms row2_coefficient18

compact_certificate theorem row2_coefficient19 (y z w : ℂ) : (rowPoly2 y z w).coeff 19=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x19 y z w

#print axioms row2_coefficient19

compact_certificate theorem row2_coefficient20 (y z w : ℂ) : (rowPoly2 y z w).coeff 20=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x20 y z w

#print axioms row2_coefficient20

compact_certificate theorem row2_coefficient21 (y z w : ℂ) : (rowPoly2 y z w).coeff 21=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x21 y z w

#print axioms row2_coefficient21

compact_certificate theorem row2_coefficient22 (y z w : ℂ) : (rowPoly2 y z w).coeff 22=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x22 y z w

#print axioms row2_coefficient22

compact_certificate theorem row2_coefficient23 (y z w : ℂ) : (rowPoly2 y z w).coeff 23=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x23 y z w

#print axioms row2_coefficient23

compact_certificate theorem row2_coefficient24 (y z w : ℂ) : (rowPoly2 y z w).coeff 24=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x24 y z w

#print axioms row2_coefficient24

compact_certificate theorem row2_coefficient25 (y z w : ℂ) : (rowPoly2 y z w).coeff 25=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x25 y z w

#print axioms row2_coefficient25

compact_certificate theorem row2_coefficient26 (y z w : ℂ) : (rowPoly2 y z w).coeff 26=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x26 y z w

#print axioms row2_coefficient26

compact_certificate theorem row2_coefficient27 (y z w : ℂ) : (rowPoly2 y z w).coeff 27=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x27 y z w

#print axioms row2_coefficient27

compact_certificate theorem row2_coefficient28 (y z w : ℂ) : (rowPoly2 y z w).coeff 28=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x28 y z w

#print axioms row2_coefficient28

compact_certificate theorem row2_coefficient29 (y z w : ℂ) : (rowPoly2 y z w).coeff 29=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x29 y z w

#print axioms row2_coefficient29

compact_certificate theorem row2_coefficient30 (y z w : ℂ) : (rowPoly2 y z w).coeff 30=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x30 y z w

#print axioms row2_coefficient30

compact_certificate theorem row2_coefficient31 (y z w : ℂ) : (rowPoly2 y z w).coeff 31=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x31 y z w

#print axioms row2_coefficient31

compact_certificate theorem row2_coefficient32 (y z w : ℂ) : (rowPoly2 y z w).coeff 32=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x32 y z w

#print axioms row2_coefficient32

compact_certificate theorem row2_coefficient33 (y z w : ℂ) : (rowPoly2 y z w).coeff 33=0 := by
  simpa [rowPoly2,qPoly0,rPoly2,qPoly1,rPoly1,qPoly2,rPoly0,qPoly4,vPoly2,qPoly5,vPoly1,qPoly6,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row2_x33 y z w

#print axioms row2_coefficient33


}
end SmallLevelTwentySixResultantBatchedMMP
end
end
