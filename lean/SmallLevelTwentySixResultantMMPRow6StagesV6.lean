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
compact_certificate theorem row6_x01 (y z w : ℂ) :
    q0301 y z w*r0300 y z w +
    q0600 y z w*v0401 y z w=0 := by
  have h : (merge (product q0301Data r0300Data) (product q0600Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0301, q0600, r0300, v0401] using he

#print axioms row6_x01

compact_certificate theorem row6_x02 (y z w : ℂ) :
    q0301 y z w*r0301 y z w +
    q0302 y z w*r0300 y z w +
    q0600 y z w*v0402 y z w +
    q0601 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (product q0301Data r0301Data) (product q0302Data r0300Data)) (product q0600Data v0402Data)) (product q0601Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0301, q0302, q0600, q0601, r0300, r0301, v0401, v0402] using he

#print axioms row6_x02

compact_certificate theorem row6_x03 (y z w : ℂ) :
    q0302 y z w*r0301 y z w +
    q0303 y z w*r0300 y z w +
    q0600 y z w*v0403 y z w +
    q0601 y z w*v0402 y z w +
    q0602 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (product q0302Data r0301Data) (product q0303Data r0300Data)) (product q0600Data v0403Data)) (product q0601Data v0402Data)) (product q0602Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0302, q0303, q0600, q0601, q0602, r0300, r0301, v0401, v0402, v0403] using he

#print axioms row6_x03

compact_certificate theorem row6_x04 (y z w : ℂ) :
    q0303 y z w*r0301 y z w +
    q0304 y z w*r0300 y z w +
    q0600 y z w*v0404 y z w +
    q0601 y z w*v0403 y z w +
    q0602 y z w*v0402 y z w +
    q0603 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (product q0303Data r0301Data) (product q0304Data r0300Data)) (product q0600Data v0404Data)) (product q0601Data v0403Data)) (product q0602Data v0402Data)) (product q0603Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0303, q0304, q0600, q0601, q0602, q0603, r0300, r0301, v0401, v0402, v0403, v0404] using he

#print axioms row6_x04

compact_certificate theorem row6_x05 (y z w : ℂ) :
    q0304 y z w*r0301 y z w +
    q0305 y z w*r0300 y z w +
    q0600 y z w*v0405 y z w +
    q0601 y z w*v0404 y z w +
    q0602 y z w*v0403 y z w +
    q0603 y z w*v0402 y z w +
    q0604 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (product q0304Data r0301Data) (product q0305Data r0300Data)) (product q0600Data v0405Data)) (product q0601Data v0404Data)) (product q0602Data v0403Data)) (product q0603Data v0402Data)) (product q0604Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0304, q0305, q0600, q0601, q0602, q0603, q0604, r0300, r0301, v0401, v0402, v0403, v0404, v0405] using he

#print axioms row6_x05

compact_certificate theorem row6_x06 (y z w : ℂ) :
    q0305 y z w*r0301 y z w +
    q0306 y z w*r0300 y z w +
    q0600 y z w*v0406 y z w +
    q0601 y z w*v0405 y z w +
    q0602 y z w*v0404 y z w +
    q0603 y z w*v0403 y z w +
    q0604 y z w*v0402 y z w +
    q0605 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0305Data r0301Data) (product q0306Data r0300Data)) (product q0600Data v0406Data)) (product q0601Data v0405Data)) (product q0602Data v0404Data)) (product q0603Data v0403Data)) (product q0604Data v0402Data)) (product q0605Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0305, q0306, q0600, q0601, q0602, q0603, q0604, q0605, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x06

compact_certificate theorem row6_x07 (y z w : ℂ) :
    q0306 y z w*r0301 y z w +
    q0307 y z w*r0300 y z w +
    q0601 y z w*v0406 y z w +
    q0602 y z w*v0405 y z w +
    q0603 y z w*v0404 y z w +
    q0604 y z w*v0403 y z w +
    q0605 y z w*v0402 y z w +
    q0606 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0306Data r0301Data) (product q0307Data r0300Data)) (product q0601Data v0406Data)) (product q0602Data v0405Data)) (product q0603Data v0404Data)) (product q0604Data v0403Data)) (product q0605Data v0402Data)) (product q0606Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0306, q0307, q0601, q0602, q0603, q0604, q0605, q0606, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x07

compact_certificate theorem row6_x08 (y z w : ℂ) :
    q0307 y z w*r0301 y z w +
    q0308 y z w*r0300 y z w +
    q0602 y z w*v0406 y z w +
    q0603 y z w*v0405 y z w +
    q0604 y z w*v0404 y z w +
    q0605 y z w*v0403 y z w +
    q0606 y z w*v0402 y z w +
    q0607 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0307Data r0301Data) (product q0308Data r0300Data)) (product q0602Data v0406Data)) (product q0603Data v0405Data)) (product q0604Data v0404Data)) (product q0605Data v0403Data)) (product q0606Data v0402Data)) (product q0607Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0307, q0308, q0602, q0603, q0604, q0605, q0606, q0607, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x08

compact_certificate theorem row6_x09 (y z w : ℂ) :
    q0308 y z w*r0301 y z w +
    q0309 y z w*r0300 y z w +
    q0603 y z w*v0406 y z w +
    q0604 y z w*v0405 y z w +
    q0605 y z w*v0404 y z w +
    q0606 y z w*v0403 y z w +
    q0607 y z w*v0402 y z w +
    q0608 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0308Data r0301Data) (product q0309Data r0300Data)) (product q0603Data v0406Data)) (product q0604Data v0405Data)) (product q0605Data v0404Data)) (product q0606Data v0403Data)) (product q0607Data v0402Data)) (product q0608Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0308, q0309, q0603, q0604, q0605, q0606, q0607, q0608, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x09

compact_certificate theorem row6_x10 (y z w : ℂ) :
    q0309 y z w*r0301 y z w +
    q0310 y z w*r0300 y z w +
    q0604 y z w*v0406 y z w +
    q0605 y z w*v0405 y z w +
    q0606 y z w*v0404 y z w +
    q0607 y z w*v0403 y z w +
    q0608 y z w*v0402 y z w +
    q0609 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0309Data r0301Data) (product q0310Data r0300Data)) (product q0604Data v0406Data)) (product q0605Data v0405Data)) (product q0606Data v0404Data)) (product q0607Data v0403Data)) (product q0608Data v0402Data)) (product q0609Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0309, q0310, q0604, q0605, q0606, q0607, q0608, q0609, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x10

compact_certificate theorem row6_x11 (y z w : ℂ) :
    q0310 y z w*r0301 y z w +
    q0311 y z w*r0300 y z w +
    q0605 y z w*v0406 y z w +
    q0606 y z w*v0405 y z w +
    q0607 y z w*v0404 y z w +
    q0608 y z w*v0403 y z w +
    q0609 y z w*v0402 y z w +
    q0610 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0310Data r0301Data) (product q0311Data r0300Data)) (product q0605Data v0406Data)) (product q0606Data v0405Data)) (product q0607Data v0404Data)) (product q0608Data v0403Data)) (product q0609Data v0402Data)) (product q0610Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0310, q0311, q0605, q0606, q0607, q0608, q0609, q0610, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x11

compact_certificate theorem row6_x12 (y z w : ℂ) :
    q0311 y z w*r0301 y z w +
    q0312 y z w*r0300 y z w +
    q0606 y z w*v0406 y z w +
    q0607 y z w*v0405 y z w +
    q0608 y z w*v0404 y z w +
    q0609 y z w*v0403 y z w +
    q0610 y z w*v0402 y z w +
    q0611 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0311Data r0301Data) (product q0312Data r0300Data)) (product q0606Data v0406Data)) (product q0607Data v0405Data)) (product q0608Data v0404Data)) (product q0609Data v0403Data)) (product q0610Data v0402Data)) (product q0611Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0311, q0312, q0606, q0607, q0608, q0609, q0610, q0611, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x12

compact_certificate theorem row6_x13 (y z w : ℂ) :
    q0312 y z w*r0301 y z w +
    q0313 y z w*r0300 y z w +
    q0607 y z w*v0406 y z w +
    q0608 y z w*v0405 y z w +
    q0609 y z w*v0404 y z w +
    q0610 y z w*v0403 y z w +
    q0611 y z w*v0402 y z w +
    q0612 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0312Data r0301Data) (product q0313Data r0300Data)) (product q0607Data v0406Data)) (product q0608Data v0405Data)) (product q0609Data v0404Data)) (product q0610Data v0403Data)) (product q0611Data v0402Data)) (product q0612Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0312, q0313, q0607, q0608, q0609, q0610, q0611, q0612, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x13

compact_certificate theorem row6_x14 (y z w : ℂ) :
    q0313 y z w*r0301 y z w +
    q0314 y z w*r0300 y z w +
    q0608 y z w*v0406 y z w +
    q0609 y z w*v0405 y z w +
    q0610 y z w*v0404 y z w +
    q0611 y z w*v0403 y z w +
    q0612 y z w*v0402 y z w +
    q0613 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0313Data r0301Data) (product q0314Data r0300Data)) (product q0608Data v0406Data)) (product q0609Data v0405Data)) (product q0610Data v0404Data)) (product q0611Data v0403Data)) (product q0612Data v0402Data)) (product q0613Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0313, q0314, q0608, q0609, q0610, q0611, q0612, q0613, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x14

compact_certificate theorem row6_x15 (y z w : ℂ) :
    q0314 y z w*r0301 y z w +
    q0315 y z w*r0300 y z w +
    q0609 y z w*v0406 y z w +
    q0610 y z w*v0405 y z w +
    q0611 y z w*v0404 y z w +
    q0612 y z w*v0403 y z w +
    q0613 y z w*v0402 y z w +
    q0614 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0314Data r0301Data) (product q0315Data r0300Data)) (product q0609Data v0406Data)) (product q0610Data v0405Data)) (product q0611Data v0404Data)) (product q0612Data v0403Data)) (product q0613Data v0402Data)) (product q0614Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0314, q0315, q0609, q0610, q0611, q0612, q0613, q0614, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x15

compact_certificate theorem row6_x16 (y z w : ℂ) :
    q0315 y z w*r0301 y z w +
    q0316 y z w*r0300 y z w +
    q0610 y z w*v0406 y z w +
    q0611 y z w*v0405 y z w +
    q0612 y z w*v0404 y z w +
    q0613 y z w*v0403 y z w +
    q0614 y z w*v0402 y z w +
    q0615 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0315Data r0301Data) (product q0316Data r0300Data)) (product q0610Data v0406Data)) (product q0611Data v0405Data)) (product q0612Data v0404Data)) (product q0613Data v0403Data)) (product q0614Data v0402Data)) (product q0615Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0315, q0316, q0610, q0611, q0612, q0613, q0614, q0615, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x16

compact_certificate theorem row6_x17 (y z w : ℂ) :
    q0316 y z w*r0301 y z w +
    q0317 y z w*r0300 y z w +
    q0611 y z w*v0406 y z w +
    q0612 y z w*v0405 y z w +
    q0613 y z w*v0404 y z w +
    q0614 y z w*v0403 y z w +
    q0615 y z w*v0402 y z w +
    q0616 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0316Data r0301Data) (product q0317Data r0300Data)) (product q0611Data v0406Data)) (product q0612Data v0405Data)) (product q0613Data v0404Data)) (product q0614Data v0403Data)) (product q0615Data v0402Data)) (product q0616Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0316, q0317, q0611, q0612, q0613, q0614, q0615, q0616, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x17

compact_certificate theorem row6_x18 (y z w : ℂ) :
    q0317 y z w*r0301 y z w +
    q0318 y z w*r0300 y z w +
    q0612 y z w*v0406 y z w +
    q0613 y z w*v0405 y z w +
    q0614 y z w*v0404 y z w +
    q0615 y z w*v0403 y z w +
    q0616 y z w*v0402 y z w +
    q0617 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0317Data r0301Data) (product q0318Data r0300Data)) (product q0612Data v0406Data)) (product q0613Data v0405Data)) (product q0614Data v0404Data)) (product q0615Data v0403Data)) (product q0616Data v0402Data)) (product q0617Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0317, q0318, q0612, q0613, q0614, q0615, q0616, q0617, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x18

compact_certificate theorem row6_x19 (y z w : ℂ) :
    q0318 y z w*r0301 y z w +
    q0319 y z w*r0300 y z w +
    q0613 y z w*v0406 y z w +
    q0614 y z w*v0405 y z w +
    q0615 y z w*v0404 y z w +
    q0616 y z w*v0403 y z w +
    q0617 y z w*v0402 y z w +
    q0618 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0318Data r0301Data) (product q0319Data r0300Data)) (product q0613Data v0406Data)) (product q0614Data v0405Data)) (product q0615Data v0404Data)) (product q0616Data v0403Data)) (product q0617Data v0402Data)) (product q0618Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0318, q0319, q0613, q0614, q0615, q0616, q0617, q0618, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x19

compact_certificate theorem row6_x20 (y z w : ℂ) :
    q0319 y z w*r0301 y z w +
    q0320 y z w*r0300 y z w +
    q0614 y z w*v0406 y z w +
    q0615 y z w*v0405 y z w +
    q0616 y z w*v0404 y z w +
    q0617 y z w*v0403 y z w +
    q0618 y z w*v0402 y z w +
    q0619 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0319Data r0301Data) (product q0320Data r0300Data)) (product q0614Data v0406Data)) (product q0615Data v0405Data)) (product q0616Data v0404Data)) (product q0617Data v0403Data)) (product q0618Data v0402Data)) (product q0619Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0319, q0320, q0614, q0615, q0616, q0617, q0618, q0619, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x20

compact_certificate theorem row6_x21 (y z w : ℂ) :
    q0320 y z w*r0301 y z w +
    q0321 y z w*r0300 y z w +
    q0615 y z w*v0406 y z w +
    q0616 y z w*v0405 y z w +
    q0617 y z w*v0404 y z w +
    q0618 y z w*v0403 y z w +
    q0619 y z w*v0402 y z w +
    q0620 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0320Data r0301Data) (product q0321Data r0300Data)) (product q0615Data v0406Data)) (product q0616Data v0405Data)) (product q0617Data v0404Data)) (product q0618Data v0403Data)) (product q0619Data v0402Data)) (product q0620Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0320, q0321, q0615, q0616, q0617, q0618, q0619, q0620, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x21

compact_certificate theorem row6_x22 (y z w : ℂ) :
    q0321 y z w*r0301 y z w +
    q0322 y z w*r0300 y z w +
    q0616 y z w*v0406 y z w +
    q0617 y z w*v0405 y z w +
    q0618 y z w*v0404 y z w +
    q0619 y z w*v0403 y z w +
    q0620 y z w*v0402 y z w +
    q0621 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0321Data r0301Data) (product q0322Data r0300Data)) (product q0616Data v0406Data)) (product q0617Data v0405Data)) (product q0618Data v0404Data)) (product q0619Data v0403Data)) (product q0620Data v0402Data)) (product q0621Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0321, q0322, q0616, q0617, q0618, q0619, q0620, q0621, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x22

compact_certificate theorem row6_x23 (y z w : ℂ) :
    q0322 y z w*r0301 y z w +
    q0323 y z w*r0300 y z w +
    q0617 y z w*v0406 y z w +
    q0618 y z w*v0405 y z w +
    q0619 y z w*v0404 y z w +
    q0620 y z w*v0403 y z w +
    q0621 y z w*v0402 y z w +
    q0622 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0322Data r0301Data) (product q0323Data r0300Data)) (product q0617Data v0406Data)) (product q0618Data v0405Data)) (product q0619Data v0404Data)) (product q0620Data v0403Data)) (product q0621Data v0402Data)) (product q0622Data v0401Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0322, q0323, q0617, q0618, q0619, q0620, q0621, q0622, r0300, r0301, v0401, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x23

compact_certificate theorem row6_x24 (y z w : ℂ) :
    q0323 y z w*r0301 y z w +
    q0324 y z w*r0300 y z w +
    q0618 y z w*v0406 y z w +
    q0619 y z w*v0405 y z w +
    q0620 y z w*v0404 y z w +
    q0621 y z w*v0403 y z w +
    q0622 y z w*v0402 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (product q0323Data r0301Data) (product q0324Data r0300Data)) (product q0618Data v0406Data)) (product q0619Data v0405Data)) (product q0620Data v0404Data)) (product q0621Data v0403Data)) (product q0622Data v0402Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0323, q0324, q0618, q0619, q0620, q0621, q0622, r0300, r0301, v0402, v0403, v0404, v0405, v0406] using he

#print axioms row6_x24

compact_certificate theorem row6_x25 (y z w : ℂ) :
    q0324 y z w*r0301 y z w +
    q0325 y z w*r0300 y z w +
    q0619 y z w*v0406 y z w +
    q0620 y z w*v0405 y z w +
    q0621 y z w*v0404 y z w +
    q0622 y z w*v0403 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (product q0324Data r0301Data) (product q0325Data r0300Data)) (product q0619Data v0406Data)) (product q0620Data v0405Data)) (product q0621Data v0404Data)) (product q0622Data v0403Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0324, q0325, q0619, q0620, q0621, q0622, r0300, r0301, v0403, v0404, v0405, v0406] using he

#print axioms row6_x25

compact_certificate theorem row6_x26 (y z w : ℂ) :
    q0325 y z w*r0301 y z w +
    q0326 y z w*r0300 y z w +
    q0620 y z w*v0406 y z w +
    q0621 y z w*v0405 y z w +
    q0622 y z w*v0404 y z w=0 := by
  have h : (merge (merge (merge (merge (product q0325Data r0301Data) (product q0326Data r0300Data)) (product q0620Data v0406Data)) (product q0621Data v0405Data)) (product q0622Data v0404Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0325, q0326, q0620, q0621, q0622, r0300, r0301, v0404, v0405, v0406] using he

#print axioms row6_x26

compact_certificate theorem row6_x27 (y z w : ℂ) :
    q0326 y z w*r0301 y z w +
    q0327 y z w*r0300 y z w +
    q0621 y z w*v0406 y z w +
    q0622 y z w*v0405 y z w=0 := by
  have h : (merge (merge (merge (product q0326Data r0301Data) (product q0327Data r0300Data)) (product q0621Data v0406Data)) (product q0622Data v0405Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0326, q0327, q0621, q0622, r0300, r0301, v0405, v0406] using he

#print axioms row6_x27

compact_certificate theorem row6_x28 (y z w : ℂ) :
    q0327 y z w*r0301 y z w +
    q0622 y z w*v0406 y z w=0 := by
  have h : (merge (product q0327Data r0301Data) (product q0622Data v0406Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0327, q0622, r0301, v0406] using he

#print axioms row6_x28

compact_certificate theorem row6_coefficient01 (y z w : ℂ) : (rowPoly6 y z w).coeff 1=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x01 y z w

#print axioms row6_coefficient01

compact_certificate theorem row6_coefficient02 (y z w : ℂ) : (rowPoly6 y z w).coeff 2=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x02 y z w

#print axioms row6_coefficient02

compact_certificate theorem row6_coefficient03 (y z w : ℂ) : (rowPoly6 y z w).coeff 3=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x03 y z w

#print axioms row6_coefficient03

compact_certificate theorem row6_coefficient04 (y z w : ℂ) : (rowPoly6 y z w).coeff 4=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x04 y z w

#print axioms row6_coefficient04

compact_certificate theorem row6_coefficient05 (y z w : ℂ) : (rowPoly6 y z w).coeff 5=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x05 y z w

#print axioms row6_coefficient05

compact_certificate theorem row6_coefficient06 (y z w : ℂ) : (rowPoly6 y z w).coeff 6=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x06 y z w

#print axioms row6_coefficient06

compact_certificate theorem row6_coefficient07 (y z w : ℂ) : (rowPoly6 y z w).coeff 7=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x07 y z w

#print axioms row6_coefficient07

compact_certificate theorem row6_coefficient08 (y z w : ℂ) : (rowPoly6 y z w).coeff 8=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x08 y z w

#print axioms row6_coefficient08

compact_certificate theorem row6_coefficient09 (y z w : ℂ) : (rowPoly6 y z w).coeff 9=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x09 y z w

#print axioms row6_coefficient09

compact_certificate theorem row6_coefficient10 (y z w : ℂ) : (rowPoly6 y z w).coeff 10=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x10 y z w

#print axioms row6_coefficient10

compact_certificate theorem row6_coefficient11 (y z w : ℂ) : (rowPoly6 y z w).coeff 11=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x11 y z w

#print axioms row6_coefficient11

compact_certificate theorem row6_coefficient12 (y z w : ℂ) : (rowPoly6 y z w).coeff 12=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x12 y z w

#print axioms row6_coefficient12

compact_certificate theorem row6_coefficient13 (y z w : ℂ) : (rowPoly6 y z w).coeff 13=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x13 y z w

#print axioms row6_coefficient13

compact_certificate theorem row6_coefficient14 (y z w : ℂ) : (rowPoly6 y z w).coeff 14=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x14 y z w

#print axioms row6_coefficient14

compact_certificate theorem row6_coefficient15 (y z w : ℂ) : (rowPoly6 y z w).coeff 15=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x15 y z w

#print axioms row6_coefficient15

compact_certificate theorem row6_coefficient16 (y z w : ℂ) : (rowPoly6 y z w).coeff 16=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x16 y z w

#print axioms row6_coefficient16

compact_certificate theorem row6_coefficient17 (y z w : ℂ) : (rowPoly6 y z w).coeff 17=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x17 y z w

#print axioms row6_coefficient17

compact_certificate theorem row6_coefficient18 (y z w : ℂ) : (rowPoly6 y z w).coeff 18=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x18 y z w

#print axioms row6_coefficient18

compact_certificate theorem row6_coefficient19 (y z w : ℂ) : (rowPoly6 y z w).coeff 19=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x19 y z w

#print axioms row6_coefficient19

compact_certificate theorem row6_coefficient20 (y z w : ℂ) : (rowPoly6 y z w).coeff 20=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x20 y z w

#print axioms row6_coefficient20

compact_certificate theorem row6_coefficient21 (y z w : ℂ) : (rowPoly6 y z w).coeff 21=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x21 y z w

#print axioms row6_coefficient21

compact_certificate theorem row6_coefficient22 (y z w : ℂ) : (rowPoly6 y z w).coeff 22=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x22 y z w

#print axioms row6_coefficient22

compact_certificate theorem row6_coefficient23 (y z w : ℂ) : (rowPoly6 y z w).coeff 23=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x23 y z w

#print axioms row6_coefficient23

compact_certificate theorem row6_coefficient24 (y z w : ℂ) : (rowPoly6 y z w).coeff 24=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x24 y z w

#print axioms row6_coefficient24

compact_certificate theorem row6_coefficient25 (y z w : ℂ) : (rowPoly6 y z w).coeff 25=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x25 y z w

#print axioms row6_coefficient25

compact_certificate theorem row6_coefficient26 (y z w : ℂ) : (rowPoly6 y z w).coeff 26=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x26 y z w

#print axioms row6_coefficient26

compact_certificate theorem row6_coefficient27 (y z w : ℂ) : (rowPoly6 y z w).coeff 27=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x27 y z w

#print axioms row6_coefficient27

compact_certificate theorem row6_coefficient28 (y z w : ℂ) : (rowPoly6 y z w).coeff 28=0 := by
  simpa [rowPoly6,qPoly3,rPoly3,qPoly6,vPoly4,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row6_x28 y z w

#print axioms row6_coefficient28


}
end SmallLevelTwentySixResultantBatchedMMP
end
end
