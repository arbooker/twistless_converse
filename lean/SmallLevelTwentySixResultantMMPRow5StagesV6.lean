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
compact_certificate theorem row5_x01 (y z w : ℂ) :
    q0201 y z w*r0300 y z w +
    q0301 y z w*r0200 y z w +
    q0500 y z w*v0401 y z w +
    q0600 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (product q0201Data r0300Data) (product q0301Data r0200Data)) (product q0500Data v0401Data)) (product q0600Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0201, q0301, q0500, q0600, r0200, r0300, v0301, v0401] using he

#print axioms row5_x01

compact_certificate theorem row5_x02 (y z w : ℂ) :
    q0201 y z w*r0301 y z w +
    q0202 y z w*r0300 y z w +
    q0301 y z w*r0201 y z w +
    q0302 y z w*r0200 y z w +
    q0500 y z w*v0402 y z w +
    q0501 y z w*v0401 y z w +
    q0600 y z w*v0302 y z w +
    q0601 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0201Data r0301Data) (product q0202Data r0300Data)) (product q0301Data r0201Data)) (product q0302Data r0200Data)) (product q0500Data v0402Data)) (product q0501Data v0401Data)) (product q0600Data v0302Data)) (product q0601Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0201, q0202, q0301, q0302, q0500, q0501, q0600, q0601, r0200, r0201, r0300, r0301, v0301, v0302, v0401, v0402] using he

#print axioms row5_x02

compact_certificate theorem row5_x03 (y z w : ℂ) :
    q0202 y z w*r0301 y z w +
    q0203 y z w*r0300 y z w +
    q0301 y z w*r0202 y z w +
    q0302 y z w*r0201 y z w +
    q0303 y z w*r0200 y z w +
    q0500 y z w*v0403 y z w +
    q0501 y z w*v0402 y z w +
    q0502 y z w*v0401 y z w +
    q0600 y z w*v0303 y z w +
    q0601 y z w*v0302 y z w +
    q0602 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0202Data r0301Data) (product q0203Data r0300Data)) (product q0301Data r0202Data)) (product q0302Data r0201Data)) (product q0303Data r0200Data)) (product q0500Data v0403Data)) (product q0501Data v0402Data)) (product q0502Data v0401Data)) (product q0600Data v0303Data)) (product q0601Data v0302Data)) (product q0602Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0202, q0203, q0301, q0302, q0303, q0500, q0501, q0502, q0600, q0601, q0602, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0401, v0402, v0403] using he

#print axioms row5_x03

compact_certificate theorem row5_x04 (y z w : ℂ) :
    q0203 y z w*r0301 y z w +
    q0204 y z w*r0300 y z w +
    q0302 y z w*r0202 y z w +
    q0303 y z w*r0201 y z w +
    q0304 y z w*r0200 y z w +
    q0500 y z w*v0404 y z w +
    q0501 y z w*v0403 y z w +
    q0502 y z w*v0402 y z w +
    q0503 y z w*v0401 y z w +
    q0600 y z w*v0304 y z w +
    q0601 y z w*v0303 y z w +
    q0602 y z w*v0302 y z w +
    q0603 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0203Data r0301Data) (product q0204Data r0300Data)) (product q0302Data r0202Data)) (product q0303Data r0201Data)) (product q0304Data r0200Data)) (product q0500Data v0404Data)) (product q0501Data v0403Data)) (product q0502Data v0402Data)) (product q0503Data v0401Data)) (product q0600Data v0304Data)) (product q0601Data v0303Data)) (product q0602Data v0302Data)) (product q0603Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0203, q0204, q0302, q0303, q0304, q0500, q0501, q0502, q0503, q0600, q0601, q0602, q0603, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0401, v0402, v0403, v0404] using he

#print axioms row5_x04

compact_certificate theorem row5_x05 (y z w : ℂ) :
    q0204 y z w*r0301 y z w +
    q0205 y z w*r0300 y z w +
    q0303 y z w*r0202 y z w +
    q0304 y z w*r0201 y z w +
    q0305 y z w*r0200 y z w +
    q0500 y z w*v0405 y z w +
    q0501 y z w*v0404 y z w +
    q0502 y z w*v0403 y z w +
    q0503 y z w*v0402 y z w +
    q0504 y z w*v0401 y z w +
    q0600 y z w*v0305 y z w +
    q0601 y z w*v0304 y z w +
    q0602 y z w*v0303 y z w +
    q0603 y z w*v0302 y z w +
    q0604 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0204Data r0301Data) (product q0205Data r0300Data)) (product q0303Data r0202Data)) (product q0304Data r0201Data)) (product q0305Data r0200Data)) (product q0500Data v0405Data)) (product q0501Data v0404Data)) (product q0502Data v0403Data)) (product q0503Data v0402Data)) (product q0504Data v0401Data)) (product q0600Data v0305Data)) (product q0601Data v0304Data)) (product q0602Data v0303Data)) (product q0603Data v0302Data)) (product q0604Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0204, q0205, q0303, q0304, q0305, q0500, q0501, q0502, q0503, q0504, q0600, q0601, q0602, q0603, q0604, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0401, v0402, v0403, v0404, v0405] using he

#print axioms row5_x05

compact_certificate theorem row5_x06 (y z w : ℂ) :
    q0205 y z w*r0301 y z w +
    q0206 y z w*r0300 y z w +
    q0304 y z w*r0202 y z w +
    q0305 y z w*r0201 y z w +
    q0306 y z w*r0200 y z w +
    q0500 y z w*v0406 y z w +
    q0501 y z w*v0405 y z w +
    q0502 y z w*v0404 y z w +
    q0503 y z w*v0403 y z w +
    q0504 y z w*v0402 y z w +
    q0505 y z w*v0401 y z w +
    q0600 y z w*v0306 y z w +
    q0601 y z w*v0305 y z w +
    q0602 y z w*v0304 y z w +
    q0603 y z w*v0303 y z w +
    q0604 y z w*v0302 y z w +
    q0605 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0205Data r0301Data) (product q0206Data r0300Data)) (product q0304Data r0202Data)) (product q0305Data r0201Data)) (product q0306Data r0200Data)) (product q0500Data v0406Data)) (product q0501Data v0405Data)) (product q0502Data v0404Data)) (product q0503Data v0403Data)) (product q0504Data v0402Data)) (product q0505Data v0401Data)) (product q0600Data v0306Data)) (product q0601Data v0305Data)) (product q0602Data v0304Data)) (product q0603Data v0303Data)) (product q0604Data v0302Data)) (product q0605Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0205, q0206, q0304, q0305, q0306, q0500, q0501, q0502, q0503, q0504, q0505, q0600, q0601, q0602, q0603, q0604, q0605, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x06

compact_certificate theorem row5_x07 (y z w : ℂ) :
    q0206 y z w*r0301 y z w +
    q0207 y z w*r0300 y z w +
    q0305 y z w*r0202 y z w +
    q0306 y z w*r0201 y z w +
    q0307 y z w*r0200 y z w +
    q0501 y z w*v0406 y z w +
    q0502 y z w*v0405 y z w +
    q0503 y z w*v0404 y z w +
    q0504 y z w*v0403 y z w +
    q0505 y z w*v0402 y z w +
    q0506 y z w*v0401 y z w +
    q0600 y z w*v0307 y z w +
    q0601 y z w*v0306 y z w +
    q0602 y z w*v0305 y z w +
    q0603 y z w*v0304 y z w +
    q0604 y z w*v0303 y z w +
    q0605 y z w*v0302 y z w +
    q0606 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0206Data r0301Data) (product q0207Data r0300Data)) (product q0305Data r0202Data)) (product q0306Data r0201Data)) (product q0307Data r0200Data)) (product q0501Data v0406Data)) (product q0502Data v0405Data)) (product q0503Data v0404Data)) (product q0504Data v0403Data)) (product q0505Data v0402Data)) (product q0506Data v0401Data)) (product q0600Data v0307Data)) (product q0601Data v0306Data)) (product q0602Data v0305Data)) (product q0603Data v0304Data)) (product q0604Data v0303Data)) (product q0605Data v0302Data)) (product q0606Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0206, q0207, q0305, q0306, q0307, q0501, q0502, q0503, q0504, q0505, q0506, q0600, q0601, q0602, q0603, q0604, q0605, q0606, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x07

compact_certificate theorem row5_x08 (y z w : ℂ) :
    q0207 y z w*r0301 y z w +
    q0208 y z w*r0300 y z w +
    q0306 y z w*r0202 y z w +
    q0307 y z w*r0201 y z w +
    q0308 y z w*r0200 y z w +
    q0502 y z w*v0406 y z w +
    q0503 y z w*v0405 y z w +
    q0504 y z w*v0404 y z w +
    q0505 y z w*v0403 y z w +
    q0506 y z w*v0402 y z w +
    q0507 y z w*v0401 y z w +
    q0601 y z w*v0307 y z w +
    q0602 y z w*v0306 y z w +
    q0603 y z w*v0305 y z w +
    q0604 y z w*v0304 y z w +
    q0605 y z w*v0303 y z w +
    q0606 y z w*v0302 y z w +
    q0607 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0207Data r0301Data) (product q0208Data r0300Data)) (product q0306Data r0202Data)) (product q0307Data r0201Data)) (product q0308Data r0200Data)) (product q0502Data v0406Data)) (product q0503Data v0405Data)) (product q0504Data v0404Data)) (product q0505Data v0403Data)) (product q0506Data v0402Data)) (product q0507Data v0401Data)) (product q0601Data v0307Data)) (product q0602Data v0306Data)) (product q0603Data v0305Data)) (product q0604Data v0304Data)) (product q0605Data v0303Data)) (product q0606Data v0302Data)) (product q0607Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0207, q0208, q0306, q0307, q0308, q0502, q0503, q0504, q0505, q0506, q0507, q0601, q0602, q0603, q0604, q0605, q0606, q0607, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x08

compact_certificate theorem row5_x09 (y z w : ℂ) :
    q0208 y z w*r0301 y z w +
    q0209 y z w*r0300 y z w +
    q0307 y z w*r0202 y z w +
    q0308 y z w*r0201 y z w +
    q0309 y z w*r0200 y z w +
    q0503 y z w*v0406 y z w +
    q0504 y z w*v0405 y z w +
    q0505 y z w*v0404 y z w +
    q0506 y z w*v0403 y z w +
    q0507 y z w*v0402 y z w +
    q0508 y z w*v0401 y z w +
    q0602 y z w*v0307 y z w +
    q0603 y z w*v0306 y z w +
    q0604 y z w*v0305 y z w +
    q0605 y z w*v0304 y z w +
    q0606 y z w*v0303 y z w +
    q0607 y z w*v0302 y z w +
    q0608 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0208Data r0301Data) (product q0209Data r0300Data)) (product q0307Data r0202Data)) (product q0308Data r0201Data)) (product q0309Data r0200Data)) (product q0503Data v0406Data)) (product q0504Data v0405Data)) (product q0505Data v0404Data)) (product q0506Data v0403Data)) (product q0507Data v0402Data)) (product q0508Data v0401Data)) (product q0602Data v0307Data)) (product q0603Data v0306Data)) (product q0604Data v0305Data)) (product q0605Data v0304Data)) (product q0606Data v0303Data)) (product q0607Data v0302Data)) (product q0608Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0208, q0209, q0307, q0308, q0309, q0503, q0504, q0505, q0506, q0507, q0508, q0602, q0603, q0604, q0605, q0606, q0607, q0608, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x09

compact_certificate theorem row5_x10 (y z w : ℂ) :
    q0209 y z w*r0301 y z w +
    q0210 y z w*r0300 y z w +
    q0308 y z w*r0202 y z w +
    q0309 y z w*r0201 y z w +
    q0310 y z w*r0200 y z w +
    q0504 y z w*v0406 y z w +
    q0505 y z w*v0405 y z w +
    q0506 y z w*v0404 y z w +
    q0507 y z w*v0403 y z w +
    q0508 y z w*v0402 y z w +
    q0509 y z w*v0401 y z w +
    q0603 y z w*v0307 y z w +
    q0604 y z w*v0306 y z w +
    q0605 y z w*v0305 y z w +
    q0606 y z w*v0304 y z w +
    q0607 y z w*v0303 y z w +
    q0608 y z w*v0302 y z w +
    q0609 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0209Data r0301Data) (product q0210Data r0300Data)) (product q0308Data r0202Data)) (product q0309Data r0201Data)) (product q0310Data r0200Data)) (product q0504Data v0406Data)) (product q0505Data v0405Data)) (product q0506Data v0404Data)) (product q0507Data v0403Data)) (product q0508Data v0402Data)) (product q0509Data v0401Data)) (product q0603Data v0307Data)) (product q0604Data v0306Data)) (product q0605Data v0305Data)) (product q0606Data v0304Data)) (product q0607Data v0303Data)) (product q0608Data v0302Data)) (product q0609Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0209, q0210, q0308, q0309, q0310, q0504, q0505, q0506, q0507, q0508, q0509, q0603, q0604, q0605, q0606, q0607, q0608, q0609, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x10

compact_certificate theorem row5_x11 (y z w : ℂ) :
    q0210 y z w*r0301 y z w +
    q0211 y z w*r0300 y z w +
    q0309 y z w*r0202 y z w +
    q0310 y z w*r0201 y z w +
    q0311 y z w*r0200 y z w +
    q0505 y z w*v0406 y z w +
    q0506 y z w*v0405 y z w +
    q0507 y z w*v0404 y z w +
    q0508 y z w*v0403 y z w +
    q0509 y z w*v0402 y z w +
    q0510 y z w*v0401 y z w +
    q0604 y z w*v0307 y z w +
    q0605 y z w*v0306 y z w +
    q0606 y z w*v0305 y z w +
    q0607 y z w*v0304 y z w +
    q0608 y z w*v0303 y z w +
    q0609 y z w*v0302 y z w +
    q0610 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0210Data r0301Data) (product q0211Data r0300Data)) (product q0309Data r0202Data)) (product q0310Data r0201Data)) (product q0311Data r0200Data)) (product q0505Data v0406Data)) (product q0506Data v0405Data)) (product q0507Data v0404Data)) (product q0508Data v0403Data)) (product q0509Data v0402Data)) (product q0510Data v0401Data)) (product q0604Data v0307Data)) (product q0605Data v0306Data)) (product q0606Data v0305Data)) (product q0607Data v0304Data)) (product q0608Data v0303Data)) (product q0609Data v0302Data)) (product q0610Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0210, q0211, q0309, q0310, q0311, q0505, q0506, q0507, q0508, q0509, q0510, q0604, q0605, q0606, q0607, q0608, q0609, q0610, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x11

compact_certificate theorem row5_x12 (y z w : ℂ) :
    q0211 y z w*r0301 y z w +
    q0212 y z w*r0300 y z w +
    q0310 y z w*r0202 y z w +
    q0311 y z w*r0201 y z w +
    q0312 y z w*r0200 y z w +
    q0506 y z w*v0406 y z w +
    q0507 y z w*v0405 y z w +
    q0508 y z w*v0404 y z w +
    q0509 y z w*v0403 y z w +
    q0510 y z w*v0402 y z w +
    q0511 y z w*v0401 y z w +
    q0605 y z w*v0307 y z w +
    q0606 y z w*v0306 y z w +
    q0607 y z w*v0305 y z w +
    q0608 y z w*v0304 y z w +
    q0609 y z w*v0303 y z w +
    q0610 y z w*v0302 y z w +
    q0611 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0211Data r0301Data) (product q0212Data r0300Data)) (product q0310Data r0202Data)) (product q0311Data r0201Data)) (product q0312Data r0200Data)) (product q0506Data v0406Data)) (product q0507Data v0405Data)) (product q0508Data v0404Data)) (product q0509Data v0403Data)) (product q0510Data v0402Data)) (product q0511Data v0401Data)) (product q0605Data v0307Data)) (product q0606Data v0306Data)) (product q0607Data v0305Data)) (product q0608Data v0304Data)) (product q0609Data v0303Data)) (product q0610Data v0302Data)) (product q0611Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0211, q0212, q0310, q0311, q0312, q0506, q0507, q0508, q0509, q0510, q0511, q0605, q0606, q0607, q0608, q0609, q0610, q0611, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x12

compact_certificate theorem row5_x13 (y z w : ℂ) :
    q0212 y z w*r0301 y z w +
    q0213 y z w*r0300 y z w +
    q0311 y z w*r0202 y z w +
    q0312 y z w*r0201 y z w +
    q0313 y z w*r0200 y z w +
    q0507 y z w*v0406 y z w +
    q0508 y z w*v0405 y z w +
    q0509 y z w*v0404 y z w +
    q0510 y z w*v0403 y z w +
    q0511 y z w*v0402 y z w +
    q0512 y z w*v0401 y z w +
    q0606 y z w*v0307 y z w +
    q0607 y z w*v0306 y z w +
    q0608 y z w*v0305 y z w +
    q0609 y z w*v0304 y z w +
    q0610 y z w*v0303 y z w +
    q0611 y z w*v0302 y z w +
    q0612 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0212Data r0301Data) (product q0213Data r0300Data)) (product q0311Data r0202Data)) (product q0312Data r0201Data)) (product q0313Data r0200Data)) (product q0507Data v0406Data)) (product q0508Data v0405Data)) (product q0509Data v0404Data)) (product q0510Data v0403Data)) (product q0511Data v0402Data)) (product q0512Data v0401Data)) (product q0606Data v0307Data)) (product q0607Data v0306Data)) (product q0608Data v0305Data)) (product q0609Data v0304Data)) (product q0610Data v0303Data)) (product q0611Data v0302Data)) (product q0612Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0212, q0213, q0311, q0312, q0313, q0507, q0508, q0509, q0510, q0511, q0512, q0606, q0607, q0608, q0609, q0610, q0611, q0612, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x13

compact_certificate theorem row5_x14 (y z w : ℂ) :
    q0213 y z w*r0301 y z w +
    q0214 y z w*r0300 y z w +
    q0312 y z w*r0202 y z w +
    q0313 y z w*r0201 y z w +
    q0314 y z w*r0200 y z w +
    q0508 y z w*v0406 y z w +
    q0509 y z w*v0405 y z w +
    q0510 y z w*v0404 y z w +
    q0511 y z w*v0403 y z w +
    q0512 y z w*v0402 y z w +
    q0513 y z w*v0401 y z w +
    q0607 y z w*v0307 y z w +
    q0608 y z w*v0306 y z w +
    q0609 y z w*v0305 y z w +
    q0610 y z w*v0304 y z w +
    q0611 y z w*v0303 y z w +
    q0612 y z w*v0302 y z w +
    q0613 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0213Data r0301Data) (product q0214Data r0300Data)) (product q0312Data r0202Data)) (product q0313Data r0201Data)) (product q0314Data r0200Data)) (product q0508Data v0406Data)) (product q0509Data v0405Data)) (product q0510Data v0404Data)) (product q0511Data v0403Data)) (product q0512Data v0402Data)) (product q0513Data v0401Data)) (product q0607Data v0307Data)) (product q0608Data v0306Data)) (product q0609Data v0305Data)) (product q0610Data v0304Data)) (product q0611Data v0303Data)) (product q0612Data v0302Data)) (product q0613Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0213, q0214, q0312, q0313, q0314, q0508, q0509, q0510, q0511, q0512, q0513, q0607, q0608, q0609, q0610, q0611, q0612, q0613, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x14

compact_certificate theorem row5_x15 (y z w : ℂ) :
    q0214 y z w*r0301 y z w +
    q0215 y z w*r0300 y z w +
    q0313 y z w*r0202 y z w +
    q0314 y z w*r0201 y z w +
    q0315 y z w*r0200 y z w +
    q0509 y z w*v0406 y z w +
    q0510 y z w*v0405 y z w +
    q0511 y z w*v0404 y z w +
    q0512 y z w*v0403 y z w +
    q0513 y z w*v0402 y z w +
    q0514 y z w*v0401 y z w +
    q0608 y z w*v0307 y z w +
    q0609 y z w*v0306 y z w +
    q0610 y z w*v0305 y z w +
    q0611 y z w*v0304 y z w +
    q0612 y z w*v0303 y z w +
    q0613 y z w*v0302 y z w +
    q0614 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0214Data r0301Data) (product q0215Data r0300Data)) (product q0313Data r0202Data)) (product q0314Data r0201Data)) (product q0315Data r0200Data)) (product q0509Data v0406Data)) (product q0510Data v0405Data)) (product q0511Data v0404Data)) (product q0512Data v0403Data)) (product q0513Data v0402Data)) (product q0514Data v0401Data)) (product q0608Data v0307Data)) (product q0609Data v0306Data)) (product q0610Data v0305Data)) (product q0611Data v0304Data)) (product q0612Data v0303Data)) (product q0613Data v0302Data)) (product q0614Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0214, q0215, q0313, q0314, q0315, q0509, q0510, q0511, q0512, q0513, q0514, q0608, q0609, q0610, q0611, q0612, q0613, q0614, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x15

compact_certificate theorem row5_x16 (y z w : ℂ) :
    q0215 y z w*r0301 y z w +
    q0216 y z w*r0300 y z w +
    q0314 y z w*r0202 y z w +
    q0315 y z w*r0201 y z w +
    q0316 y z w*r0200 y z w +
    q0510 y z w*v0406 y z w +
    q0511 y z w*v0405 y z w +
    q0512 y z w*v0404 y z w +
    q0513 y z w*v0403 y z w +
    q0514 y z w*v0402 y z w +
    q0515 y z w*v0401 y z w +
    q0609 y z w*v0307 y z w +
    q0610 y z w*v0306 y z w +
    q0611 y z w*v0305 y z w +
    q0612 y z w*v0304 y z w +
    q0613 y z w*v0303 y z w +
    q0614 y z w*v0302 y z w +
    q0615 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0215Data r0301Data) (product q0216Data r0300Data)) (product q0314Data r0202Data)) (product q0315Data r0201Data)) (product q0316Data r0200Data)) (product q0510Data v0406Data)) (product q0511Data v0405Data)) (product q0512Data v0404Data)) (product q0513Data v0403Data)) (product q0514Data v0402Data)) (product q0515Data v0401Data)) (product q0609Data v0307Data)) (product q0610Data v0306Data)) (product q0611Data v0305Data)) (product q0612Data v0304Data)) (product q0613Data v0303Data)) (product q0614Data v0302Data)) (product q0615Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0215, q0216, q0314, q0315, q0316, q0510, q0511, q0512, q0513, q0514, q0515, q0609, q0610, q0611, q0612, q0613, q0614, q0615, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x16

compact_certificate theorem row5_x17 (y z w : ℂ) :
    q0216 y z w*r0301 y z w +
    q0217 y z w*r0300 y z w +
    q0315 y z w*r0202 y z w +
    q0316 y z w*r0201 y z w +
    q0317 y z w*r0200 y z w +
    q0511 y z w*v0406 y z w +
    q0512 y z w*v0405 y z w +
    q0513 y z w*v0404 y z w +
    q0514 y z w*v0403 y z w +
    q0515 y z w*v0402 y z w +
    q0516 y z w*v0401 y z w +
    q0610 y z w*v0307 y z w +
    q0611 y z w*v0306 y z w +
    q0612 y z w*v0305 y z w +
    q0613 y z w*v0304 y z w +
    q0614 y z w*v0303 y z w +
    q0615 y z w*v0302 y z w +
    q0616 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0216Data r0301Data) (product q0217Data r0300Data)) (product q0315Data r0202Data)) (product q0316Data r0201Data)) (product q0317Data r0200Data)) (product q0511Data v0406Data)) (product q0512Data v0405Data)) (product q0513Data v0404Data)) (product q0514Data v0403Data)) (product q0515Data v0402Data)) (product q0516Data v0401Data)) (product q0610Data v0307Data)) (product q0611Data v0306Data)) (product q0612Data v0305Data)) (product q0613Data v0304Data)) (product q0614Data v0303Data)) (product q0615Data v0302Data)) (product q0616Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0216, q0217, q0315, q0316, q0317, q0511, q0512, q0513, q0514, q0515, q0516, q0610, q0611, q0612, q0613, q0614, q0615, q0616, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x17

compact_certificate theorem row5_x18 (y z w : ℂ) :
    q0217 y z w*r0301 y z w +
    q0218 y z w*r0300 y z w +
    q0316 y z w*r0202 y z w +
    q0317 y z w*r0201 y z w +
    q0318 y z w*r0200 y z w +
    q0512 y z w*v0406 y z w +
    q0513 y z w*v0405 y z w +
    q0514 y z w*v0404 y z w +
    q0515 y z w*v0403 y z w +
    q0516 y z w*v0402 y z w +
    q0517 y z w*v0401 y z w +
    q0611 y z w*v0307 y z w +
    q0612 y z w*v0306 y z w +
    q0613 y z w*v0305 y z w +
    q0614 y z w*v0304 y z w +
    q0615 y z w*v0303 y z w +
    q0616 y z w*v0302 y z w +
    q0617 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0217Data r0301Data) (product q0218Data r0300Data)) (product q0316Data r0202Data)) (product q0317Data r0201Data)) (product q0318Data r0200Data)) (product q0512Data v0406Data)) (product q0513Data v0405Data)) (product q0514Data v0404Data)) (product q0515Data v0403Data)) (product q0516Data v0402Data)) (product q0517Data v0401Data)) (product q0611Data v0307Data)) (product q0612Data v0306Data)) (product q0613Data v0305Data)) (product q0614Data v0304Data)) (product q0615Data v0303Data)) (product q0616Data v0302Data)) (product q0617Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0217, q0218, q0316, q0317, q0318, q0512, q0513, q0514, q0515, q0516, q0517, q0611, q0612, q0613, q0614, q0615, q0616, q0617, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x18

compact_certificate theorem row5_x19 (y z w : ℂ) :
    q0218 y z w*r0301 y z w +
    q0219 y z w*r0300 y z w +
    q0317 y z w*r0202 y z w +
    q0318 y z w*r0201 y z w +
    q0319 y z w*r0200 y z w +
    q0513 y z w*v0406 y z w +
    q0514 y z w*v0405 y z w +
    q0515 y z w*v0404 y z w +
    q0516 y z w*v0403 y z w +
    q0517 y z w*v0402 y z w +
    q0518 y z w*v0401 y z w +
    q0612 y z w*v0307 y z w +
    q0613 y z w*v0306 y z w +
    q0614 y z w*v0305 y z w +
    q0615 y z w*v0304 y z w +
    q0616 y z w*v0303 y z w +
    q0617 y z w*v0302 y z w +
    q0618 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0218Data r0301Data) (product q0219Data r0300Data)) (product q0317Data r0202Data)) (product q0318Data r0201Data)) (product q0319Data r0200Data)) (product q0513Data v0406Data)) (product q0514Data v0405Data)) (product q0515Data v0404Data)) (product q0516Data v0403Data)) (product q0517Data v0402Data)) (product q0518Data v0401Data)) (product q0612Data v0307Data)) (product q0613Data v0306Data)) (product q0614Data v0305Data)) (product q0615Data v0304Data)) (product q0616Data v0303Data)) (product q0617Data v0302Data)) (product q0618Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0218, q0219, q0317, q0318, q0319, q0513, q0514, q0515, q0516, q0517, q0518, q0612, q0613, q0614, q0615, q0616, q0617, q0618, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x19

compact_certificate theorem row5_x20 (y z w : ℂ) :
    q0219 y z w*r0301 y z w +
    q0220 y z w*r0300 y z w +
    q0318 y z w*r0202 y z w +
    q0319 y z w*r0201 y z w +
    q0320 y z w*r0200 y z w +
    q0514 y z w*v0406 y z w +
    q0515 y z w*v0405 y z w +
    q0516 y z w*v0404 y z w +
    q0517 y z w*v0403 y z w +
    q0518 y z w*v0402 y z w +
    q0519 y z w*v0401 y z w +
    q0613 y z w*v0307 y z w +
    q0614 y z w*v0306 y z w +
    q0615 y z w*v0305 y z w +
    q0616 y z w*v0304 y z w +
    q0617 y z w*v0303 y z w +
    q0618 y z w*v0302 y z w +
    q0619 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0219Data r0301Data) (product q0220Data r0300Data)) (product q0318Data r0202Data)) (product q0319Data r0201Data)) (product q0320Data r0200Data)) (product q0514Data v0406Data)) (product q0515Data v0405Data)) (product q0516Data v0404Data)) (product q0517Data v0403Data)) (product q0518Data v0402Data)) (product q0519Data v0401Data)) (product q0613Data v0307Data)) (product q0614Data v0306Data)) (product q0615Data v0305Data)) (product q0616Data v0304Data)) (product q0617Data v0303Data)) (product q0618Data v0302Data)) (product q0619Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0219, q0220, q0318, q0319, q0320, q0514, q0515, q0516, q0517, q0518, q0519, q0613, q0614, q0615, q0616, q0617, q0618, q0619, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x20

compact_certificate theorem row5_x21 (y z w : ℂ) :
    q0220 y z w*r0301 y z w +
    q0221 y z w*r0300 y z w +
    q0319 y z w*r0202 y z w +
    q0320 y z w*r0201 y z w +
    q0321 y z w*r0200 y z w +
    q0515 y z w*v0406 y z w +
    q0516 y z w*v0405 y z w +
    q0517 y z w*v0404 y z w +
    q0518 y z w*v0403 y z w +
    q0519 y z w*v0402 y z w +
    q0520 y z w*v0401 y z w +
    q0614 y z w*v0307 y z w +
    q0615 y z w*v0306 y z w +
    q0616 y z w*v0305 y z w +
    q0617 y z w*v0304 y z w +
    q0618 y z w*v0303 y z w +
    q0619 y z w*v0302 y z w +
    q0620 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0220Data r0301Data) (product q0221Data r0300Data)) (product q0319Data r0202Data)) (product q0320Data r0201Data)) (product q0321Data r0200Data)) (product q0515Data v0406Data)) (product q0516Data v0405Data)) (product q0517Data v0404Data)) (product q0518Data v0403Data)) (product q0519Data v0402Data)) (product q0520Data v0401Data)) (product q0614Data v0307Data)) (product q0615Data v0306Data)) (product q0616Data v0305Data)) (product q0617Data v0304Data)) (product q0618Data v0303Data)) (product q0619Data v0302Data)) (product q0620Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0220, q0221, q0319, q0320, q0321, q0515, q0516, q0517, q0518, q0519, q0520, q0614, q0615, q0616, q0617, q0618, q0619, q0620, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x21

compact_certificate theorem row5_x22 (y z w : ℂ) :
    q0221 y z w*r0301 y z w +
    q0222 y z w*r0300 y z w +
    q0320 y z w*r0202 y z w +
    q0321 y z w*r0201 y z w +
    q0322 y z w*r0200 y z w +
    q0516 y z w*v0406 y z w +
    q0517 y z w*v0405 y z w +
    q0518 y z w*v0404 y z w +
    q0519 y z w*v0403 y z w +
    q0520 y z w*v0402 y z w +
    q0521 y z w*v0401 y z w +
    q0615 y z w*v0307 y z w +
    q0616 y z w*v0306 y z w +
    q0617 y z w*v0305 y z w +
    q0618 y z w*v0304 y z w +
    q0619 y z w*v0303 y z w +
    q0620 y z w*v0302 y z w +
    q0621 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0221Data r0301Data) (product q0222Data r0300Data)) (product q0320Data r0202Data)) (product q0321Data r0201Data)) (product q0322Data r0200Data)) (product q0516Data v0406Data)) (product q0517Data v0405Data)) (product q0518Data v0404Data)) (product q0519Data v0403Data)) (product q0520Data v0402Data)) (product q0521Data v0401Data)) (product q0615Data v0307Data)) (product q0616Data v0306Data)) (product q0617Data v0305Data)) (product q0618Data v0304Data)) (product q0619Data v0303Data)) (product q0620Data v0302Data)) (product q0621Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0221, q0222, q0320, q0321, q0322, q0516, q0517, q0518, q0519, q0520, q0521, q0615, q0616, q0617, q0618, q0619, q0620, q0621, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x22

compact_certificate theorem row5_x23 (y z w : ℂ) :
    q0222 y z w*r0301 y z w +
    q0223 y z w*r0300 y z w +
    q0321 y z w*r0202 y z w +
    q0322 y z w*r0201 y z w +
    q0323 y z w*r0200 y z w +
    q0517 y z w*v0406 y z w +
    q0518 y z w*v0405 y z w +
    q0519 y z w*v0404 y z w +
    q0520 y z w*v0403 y z w +
    q0521 y z w*v0402 y z w +
    q0522 y z w*v0401 y z w +
    q0616 y z w*v0307 y z w +
    q0617 y z w*v0306 y z w +
    q0618 y z w*v0305 y z w +
    q0619 y z w*v0304 y z w +
    q0620 y z w*v0303 y z w +
    q0621 y z w*v0302 y z w +
    q0622 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0222Data r0301Data) (product q0223Data r0300Data)) (product q0321Data r0202Data)) (product q0322Data r0201Data)) (product q0323Data r0200Data)) (product q0517Data v0406Data)) (product q0518Data v0405Data)) (product q0519Data v0404Data)) (product q0520Data v0403Data)) (product q0521Data v0402Data)) (product q0522Data v0401Data)) (product q0616Data v0307Data)) (product q0617Data v0306Data)) (product q0618Data v0305Data)) (product q0619Data v0304Data)) (product q0620Data v0303Data)) (product q0621Data v0302Data)) (product q0622Data v0301Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0222, q0223, q0321, q0322, q0323, q0517, q0518, q0519, q0520, q0521, q0522, q0616, q0617, q0618, q0619, q0620, q0621, q0622, r0200, r0201, r0202, r0300, r0301, v0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x23

compact_certificate theorem row5_x24 (y z w : ℂ) :
    q0223 y z w*r0301 y z w +
    q0224 y z w*r0300 y z w +
    q0322 y z w*r0202 y z w +
    q0323 y z w*r0201 y z w +
    q0324 y z w*r0200 y z w +
    q0518 y z w*v0406 y z w +
    q0519 y z w*v0405 y z w +
    q0520 y z w*v0404 y z w +
    q0521 y z w*v0403 y z w +
    q0522 y z w*v0402 y z w +
    q0523 y z w*v0401 y z w +
    q0617 y z w*v0307 y z w +
    q0618 y z w*v0306 y z w +
    q0619 y z w*v0305 y z w +
    q0620 y z w*v0304 y z w +
    q0621 y z w*v0303 y z w +
    q0622 y z w*v0302 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0223Data r0301Data) (product q0224Data r0300Data)) (product q0322Data r0202Data)) (product q0323Data r0201Data)) (product q0324Data r0200Data)) (product q0518Data v0406Data)) (product q0519Data v0405Data)) (product q0520Data v0404Data)) (product q0521Data v0403Data)) (product q0522Data v0402Data)) (product q0523Data v0401Data)) (product q0617Data v0307Data)) (product q0618Data v0306Data)) (product q0619Data v0305Data)) (product q0620Data v0304Data)) (product q0621Data v0303Data)) (product q0622Data v0302Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0223, q0224, q0322, q0323, q0324, q0518, q0519, q0520, q0521, q0522, q0523, q0617, q0618, q0619, q0620, q0621, q0622, r0200, r0201, r0202, r0300, r0301, v0302, v0303, v0304, v0305, v0306, v0307, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x24

compact_certificate theorem row5_x25 (y z w : ℂ) :
    q0224 y z w*r0301 y z w +
    q0225 y z w*r0300 y z w +
    q0323 y z w*r0202 y z w +
    q0324 y z w*r0201 y z w +
    q0325 y z w*r0200 y z w +
    q0519 y z w*v0406 y z w +
    q0520 y z w*v0405 y z w +
    q0521 y z w*v0404 y z w +
    q0522 y z w*v0403 y z w +
    q0523 y z w*v0402 y z w +
    q0618 y z w*v0307 y z w +
    q0619 y z w*v0306 y z w +
    q0620 y z w*v0305 y z w +
    q0621 y z w*v0304 y z w +
    q0622 y z w*v0303 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0224Data r0301Data) (product q0225Data r0300Data)) (product q0323Data r0202Data)) (product q0324Data r0201Data)) (product q0325Data r0200Data)) (product q0519Data v0406Data)) (product q0520Data v0405Data)) (product q0521Data v0404Data)) (product q0522Data v0403Data)) (product q0523Data v0402Data)) (product q0618Data v0307Data)) (product q0619Data v0306Data)) (product q0620Data v0305Data)) (product q0621Data v0304Data)) (product q0622Data v0303Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0224, q0225, q0323, q0324, q0325, q0519, q0520, q0521, q0522, q0523, q0618, q0619, q0620, q0621, q0622, r0200, r0201, r0202, r0300, r0301, v0303, v0304, v0305, v0306, v0307, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row5_x25

compact_certificate theorem row5_x26 (y z w : ℂ) :
    q0225 y z w*r0301 y z w +
    q0226 y z w*r0300 y z w +
    q0324 y z w*r0202 y z w +
    q0325 y z w*r0201 y z w +
    q0326 y z w*r0200 y z w +
    q0520 y z w*v0406 y z w +
    q0521 y z w*v0405 y z w +
    q0522 y z w*v0404 y z w +
    q0523 y z w*v0403 y z w +
    q0619 y z w*v0307 y z w +
    q0620 y z w*v0306 y z w +
    q0621 y z w*v0305 y z w +
    q0622 y z w*v0304 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0225Data r0301Data) (product q0226Data r0300Data)) (product q0324Data r0202Data)) (product q0325Data r0201Data)) (product q0326Data r0200Data)) (product q0520Data v0406Data)) (product q0521Data v0405Data)) (product q0522Data v0404Data)) (product q0523Data v0403Data)) (product q0619Data v0307Data)) (product q0620Data v0306Data)) (product q0621Data v0305Data)) (product q0622Data v0304Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0225, q0226, q0324, q0325, q0326, q0520, q0521, q0522, q0523, q0619, q0620, q0621, q0622, r0200, r0201, r0202, r0300, r0301, v0304, v0305, v0306, v0307, v0403, v0404, v0405, v0406] using he

#print axioms row5_x26

compact_certificate theorem row5_x27 (y z w : ℂ) :
    q0226 y z w*r0301 y z w +
    q0227 y z w*r0300 y z w +
    q0325 y z w*r0202 y z w +
    q0326 y z w*r0201 y z w +
    q0327 y z w*r0200 y z w +
    q0521 y z w*v0406 y z w +
    q0522 y z w*v0405 y z w +
    q0523 y z w*v0404 y z w +
    q0620 y z w*v0307 y z w +
    q0621 y z w*v0306 y z w +
    q0622 y z w*v0305 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0226Data r0301Data) (product q0227Data r0300Data)) (product q0325Data r0202Data)) (product q0326Data r0201Data)) (product q0327Data r0200Data)) (product q0521Data v0406Data)) (product q0522Data v0405Data)) (product q0523Data v0404Data)) (product q0620Data v0307Data)) (product q0621Data v0306Data)) (product q0622Data v0305Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0226, q0227, q0325, q0326, q0327, q0521, q0522, q0523, q0620, q0621, q0622, r0200, r0201, r0202, r0300, r0301, v0305, v0306, v0307, v0404, v0405, v0406] using he

#print axioms row5_x27

compact_certificate theorem row5_x28 (y z w : ℂ) :
    q0227 y z w*r0301 y z w +
    q0228 y z w*r0300 y z w +
    q0326 y z w*r0202 y z w +
    q0327 y z w*r0201 y z w +
    q0522 y z w*v0406 y z w +
    q0523 y z w*v0405 y z w +
    q0621 y z w*v0307 y z w +
    q0622 y z w*v0306 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0227Data r0301Data) (product q0228Data r0300Data)) (product q0326Data r0202Data)) (product q0327Data r0201Data)) (product q0522Data v0406Data)) (product q0523Data v0405Data)) (product q0621Data v0307Data)) (product q0622Data v0306Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0227, q0228, q0326, q0327, q0522, q0523, q0621, q0622, r0201, r0202, r0300, r0301, v0306, v0307, v0405, v0406] using he

#print axioms row5_x28

compact_certificate theorem row5_x29 (y z w : ℂ) :
    q0228 y z w*r0301 y z w +
    q0327 y z w*r0202 y z w +
    q0523 y z w*v0406 y z w +
    q0622 y z w*v0307 y z w=0 := by
  have h : (merge (merge (merge (product q0228Data r0301Data) (product q0327Data r0202Data)) (product q0523Data v0406Data)) (product q0622Data v0307Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0228, q0327, q0523, q0622, r0202, r0301, v0307, v0406] using he

#print axioms row5_x29

compact_certificate theorem row5_coefficient01 (y z w : ℂ) : (rowPoly5 y z w).coeff 1=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x01 y z w

#print axioms row5_coefficient01

compact_certificate theorem row5_coefficient02 (y z w : ℂ) : (rowPoly5 y z w).coeff 2=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x02 y z w

#print axioms row5_coefficient02

compact_certificate theorem row5_coefficient03 (y z w : ℂ) : (rowPoly5 y z w).coeff 3=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x03 y z w

#print axioms row5_coefficient03

compact_certificate theorem row5_coefficient04 (y z w : ℂ) : (rowPoly5 y z w).coeff 4=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x04 y z w

#print axioms row5_coefficient04

compact_certificate theorem row5_coefficient05 (y z w : ℂ) : (rowPoly5 y z w).coeff 5=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x05 y z w

#print axioms row5_coefficient05

compact_certificate theorem row5_coefficient06 (y z w : ℂ) : (rowPoly5 y z w).coeff 6=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x06 y z w

#print axioms row5_coefficient06

compact_certificate theorem row5_coefficient07 (y z w : ℂ) : (rowPoly5 y z w).coeff 7=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x07 y z w

#print axioms row5_coefficient07

compact_certificate theorem row5_coefficient08 (y z w : ℂ) : (rowPoly5 y z w).coeff 8=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x08 y z w

#print axioms row5_coefficient08

compact_certificate theorem row5_coefficient09 (y z w : ℂ) : (rowPoly5 y z w).coeff 9=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x09 y z w

#print axioms row5_coefficient09

compact_certificate theorem row5_coefficient10 (y z w : ℂ) : (rowPoly5 y z w).coeff 10=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x10 y z w

#print axioms row5_coefficient10

compact_certificate theorem row5_coefficient11 (y z w : ℂ) : (rowPoly5 y z w).coeff 11=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x11 y z w

#print axioms row5_coefficient11

compact_certificate theorem row5_coefficient12 (y z w : ℂ) : (rowPoly5 y z w).coeff 12=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x12 y z w

#print axioms row5_coefficient12

compact_certificate theorem row5_coefficient13 (y z w : ℂ) : (rowPoly5 y z w).coeff 13=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x13 y z w

#print axioms row5_coefficient13

compact_certificate theorem row5_coefficient14 (y z w : ℂ) : (rowPoly5 y z w).coeff 14=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x14 y z w

#print axioms row5_coefficient14

compact_certificate theorem row5_coefficient15 (y z w : ℂ) : (rowPoly5 y z w).coeff 15=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x15 y z w

#print axioms row5_coefficient15

compact_certificate theorem row5_coefficient16 (y z w : ℂ) : (rowPoly5 y z w).coeff 16=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x16 y z w

#print axioms row5_coefficient16

compact_certificate theorem row5_coefficient17 (y z w : ℂ) : (rowPoly5 y z w).coeff 17=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x17 y z w

#print axioms row5_coefficient17

compact_certificate theorem row5_coefficient18 (y z w : ℂ) : (rowPoly5 y z w).coeff 18=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x18 y z w

#print axioms row5_coefficient18

compact_certificate theorem row5_coefficient19 (y z w : ℂ) : (rowPoly5 y z w).coeff 19=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x19 y z w

#print axioms row5_coefficient19

compact_certificate theorem row5_coefficient20 (y z w : ℂ) : (rowPoly5 y z w).coeff 20=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x20 y z w

#print axioms row5_coefficient20

compact_certificate theorem row5_coefficient21 (y z w : ℂ) : (rowPoly5 y z w).coeff 21=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x21 y z w

#print axioms row5_coefficient21

compact_certificate theorem row5_coefficient22 (y z w : ℂ) : (rowPoly5 y z w).coeff 22=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x22 y z w

#print axioms row5_coefficient22

compact_certificate theorem row5_coefficient23 (y z w : ℂ) : (rowPoly5 y z w).coeff 23=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x23 y z w

#print axioms row5_coefficient23

compact_certificate theorem row5_coefficient24 (y z w : ℂ) : (rowPoly5 y z w).coeff 24=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x24 y z w

#print axioms row5_coefficient24

compact_certificate theorem row5_coefficient25 (y z w : ℂ) : (rowPoly5 y z w).coeff 25=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x25 y z w

#print axioms row5_coefficient25

compact_certificate theorem row5_coefficient26 (y z w : ℂ) : (rowPoly5 y z w).coeff 26=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x26 y z w

#print axioms row5_coefficient26

compact_certificate theorem row5_coefficient27 (y z w : ℂ) : (rowPoly5 y z w).coeff 27=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x27 y z w

#print axioms row5_coefficient27

compact_certificate theorem row5_coefficient28 (y z w : ℂ) : (rowPoly5 y z w).coeff 28=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x28 y z w

#print axioms row5_coefficient28

compact_certificate theorem row5_coefficient29 (y z w : ℂ) : (rowPoly5 y z w).coeff 29=0 := by
  simpa [rowPoly5,qPoly2,rPoly3,qPoly3,rPoly2,qPoly5,vPoly4,qPoly6,vPoly3,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row5_x29 y z w

#print axioms row5_coefficient29


}
end SmallLevelTwentySixResultantBatchedMMP
end
end
