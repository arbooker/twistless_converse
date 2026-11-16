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
compact_certificate theorem row1_x17 (y z w : ℂ) :
    q0014 y z w*r0103 y z w +
    q0015 y z w*r0102 y z w +
    q0016 y z w*r0101 y z w +
    q0017 y z w*r0100 y z w +
    q0112 y z w*r0005 y z w +
    q0114 y z w*r0003 y z w +
    q0115 y z w*r0002 y z w +
    q0116 y z w*r0001 y z w +
    q0117 y z w*r0000 y z w +
    q0407 y z w*v0110 y z w +
    q0408 y z w*v0109 y z w +
    q0409 y z w*v0108 y z w +
    q0410 y z w*v0107 y z w +
    q0411 y z w*v0106 y z w +
    q0412 y z w*v0105 y z w +
    q0413 y z w*v0104 y z w +
    q0414 y z w*v0103 y z w +
    q0415 y z w*v0102 y z w +
    q0416 y z w*v0101 y z w +
    q0417 y z w*v0100 y z w +
    q0506 y z w*v0011 y z w +
    q0507 y z w*v0010 y z w +
    q0508 y z w*v0009 y z w +
    q0509 y z w*v0008 y z w +
    q0510 y z w*v0007 y z w +
    q0511 y z w*v0006 y z w +
    q0512 y z w*v0005 y z w +
    q0513 y z w*v0004 y z w +
    q0514 y z w*v0003 y z w +
    q0515 y z w*v0002 y z w +
    q0516 y z w*v0001 y z w +
    q0517 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0014Data r0103Data) (product q0015Data r0102Data)) (product q0016Data r0101Data)) (product q0017Data r0100Data)) (product q0112Data r0005Data)) (product q0114Data r0003Data)) (product q0115Data r0002Data)) (product q0116Data r0001Data)) (product q0117Data r0000Data)) (product q0407Data v0110Data)) (product q0408Data v0109Data)) (product q0409Data v0108Data)) (product q0410Data v0107Data)) (product q0411Data v0106Data)) (product q0412Data v0105Data)) (product q0413Data v0104Data)) (product q0414Data v0103Data)) (product q0415Data v0102Data)) (product q0416Data v0101Data)) (product q0417Data v0100Data)) (product q0506Data v0011Data)) (product q0507Data v0010Data)) (product q0508Data v0009Data)) (product q0509Data v0008Data)) (product q0510Data v0007Data)) (product q0511Data v0006Data)) (product q0512Data v0005Data)) (product q0513Data v0004Data)) (product q0514Data v0003Data)) (product q0515Data v0002Data)) (product q0516Data v0001Data)) (product q0517Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0014, q0015, q0016, q0017, q0112, q0114, q0115, q0116, q0117, q0407, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0506, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x17

compact_certificate theorem row1_x18 (y z w : ℂ) :
    q0015 y z w*r0103 y z w +
    q0016 y z w*r0102 y z w +
    q0017 y z w*r0101 y z w +
    q0018 y z w*r0100 y z w +
    q0113 y z w*r0005 y z w +
    q0115 y z w*r0003 y z w +
    q0116 y z w*r0002 y z w +
    q0117 y z w*r0001 y z w +
    q0118 y z w*r0000 y z w +
    q0408 y z w*v0110 y z w +
    q0409 y z w*v0109 y z w +
    q0410 y z w*v0108 y z w +
    q0411 y z w*v0107 y z w +
    q0412 y z w*v0106 y z w +
    q0413 y z w*v0105 y z w +
    q0414 y z w*v0104 y z w +
    q0415 y z w*v0103 y z w +
    q0416 y z w*v0102 y z w +
    q0417 y z w*v0101 y z w +
    q0418 y z w*v0100 y z w +
    q0507 y z w*v0011 y z w +
    q0508 y z w*v0010 y z w +
    q0509 y z w*v0009 y z w +
    q0510 y z w*v0008 y z w +
    q0511 y z w*v0007 y z w +
    q0512 y z w*v0006 y z w +
    q0513 y z w*v0005 y z w +
    q0514 y z w*v0004 y z w +
    q0515 y z w*v0003 y z w +
    q0516 y z w*v0002 y z w +
    q0517 y z w*v0001 y z w +
    q0518 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0015Data r0103Data) (product q0016Data r0102Data)) (product q0017Data r0101Data)) (product q0018Data r0100Data)) (product q0113Data r0005Data)) (product q0115Data r0003Data)) (product q0116Data r0002Data)) (product q0117Data r0001Data)) (product q0118Data r0000Data)) (product q0408Data v0110Data)) (product q0409Data v0109Data)) (product q0410Data v0108Data)) (product q0411Data v0107Data)) (product q0412Data v0106Data)) (product q0413Data v0105Data)) (product q0414Data v0104Data)) (product q0415Data v0103Data)) (product q0416Data v0102Data)) (product q0417Data v0101Data)) (product q0418Data v0100Data)) (product q0507Data v0011Data)) (product q0508Data v0010Data)) (product q0509Data v0009Data)) (product q0510Data v0008Data)) (product q0511Data v0007Data)) (product q0512Data v0006Data)) (product q0513Data v0005Data)) (product q0514Data v0004Data)) (product q0515Data v0003Data)) (product q0516Data v0002Data)) (product q0517Data v0001Data)) (product q0518Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0015, q0016, q0017, q0018, q0113, q0115, q0116, q0117, q0118, q0408, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0507, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x18

compact_certificate theorem row1_x19 (y z w : ℂ) :
    q0016 y z w*r0103 y z w +
    q0017 y z w*r0102 y z w +
    q0018 y z w*r0101 y z w +
    q0019 y z w*r0100 y z w +
    q0114 y z w*r0005 y z w +
    q0116 y z w*r0003 y z w +
    q0117 y z w*r0002 y z w +
    q0118 y z w*r0001 y z w +
    q0119 y z w*r0000 y z w +
    q0409 y z w*v0110 y z w +
    q0410 y z w*v0109 y z w +
    q0411 y z w*v0108 y z w +
    q0412 y z w*v0107 y z w +
    q0413 y z w*v0106 y z w +
    q0414 y z w*v0105 y z w +
    q0415 y z w*v0104 y z w +
    q0416 y z w*v0103 y z w +
    q0417 y z w*v0102 y z w +
    q0418 y z w*v0101 y z w +
    q0419 y z w*v0100 y z w +
    q0508 y z w*v0011 y z w +
    q0509 y z w*v0010 y z w +
    q0510 y z w*v0009 y z w +
    q0511 y z w*v0008 y z w +
    q0512 y z w*v0007 y z w +
    q0513 y z w*v0006 y z w +
    q0514 y z w*v0005 y z w +
    q0515 y z w*v0004 y z w +
    q0516 y z w*v0003 y z w +
    q0517 y z w*v0002 y z w +
    q0518 y z w*v0001 y z w +
    q0519 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0016Data r0103Data) (product q0017Data r0102Data)) (product q0018Data r0101Data)) (product q0019Data r0100Data)) (product q0114Data r0005Data)) (product q0116Data r0003Data)) (product q0117Data r0002Data)) (product q0118Data r0001Data)) (product q0119Data r0000Data)) (product q0409Data v0110Data)) (product q0410Data v0109Data)) (product q0411Data v0108Data)) (product q0412Data v0107Data)) (product q0413Data v0106Data)) (product q0414Data v0105Data)) (product q0415Data v0104Data)) (product q0416Data v0103Data)) (product q0417Data v0102Data)) (product q0418Data v0101Data)) (product q0419Data v0100Data)) (product q0508Data v0011Data)) (product q0509Data v0010Data)) (product q0510Data v0009Data)) (product q0511Data v0008Data)) (product q0512Data v0007Data)) (product q0513Data v0006Data)) (product q0514Data v0005Data)) (product q0515Data v0004Data)) (product q0516Data v0003Data)) (product q0517Data v0002Data)) (product q0518Data v0001Data)) (product q0519Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0016, q0017, q0018, q0019, q0114, q0116, q0117, q0118, q0119, q0409, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0508, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x19

compact_certificate theorem row1_x20 (y z w : ℂ) :
    q0017 y z w*r0103 y z w +
    q0018 y z w*r0102 y z w +
    q0019 y z w*r0101 y z w +
    q0020 y z w*r0100 y z w +
    q0115 y z w*r0005 y z w +
    q0117 y z w*r0003 y z w +
    q0118 y z w*r0002 y z w +
    q0119 y z w*r0001 y z w +
    q0120 y z w*r0000 y z w +
    q0410 y z w*v0110 y z w +
    q0411 y z w*v0109 y z w +
    q0412 y z w*v0108 y z w +
    q0413 y z w*v0107 y z w +
    q0414 y z w*v0106 y z w +
    q0415 y z w*v0105 y z w +
    q0416 y z w*v0104 y z w +
    q0417 y z w*v0103 y z w +
    q0418 y z w*v0102 y z w +
    q0419 y z w*v0101 y z w +
    q0420 y z w*v0100 y z w +
    q0509 y z w*v0011 y z w +
    q0510 y z w*v0010 y z w +
    q0511 y z w*v0009 y z w +
    q0512 y z w*v0008 y z w +
    q0513 y z w*v0007 y z w +
    q0514 y z w*v0006 y z w +
    q0515 y z w*v0005 y z w +
    q0516 y z w*v0004 y z w +
    q0517 y z w*v0003 y z w +
    q0518 y z w*v0002 y z w +
    q0519 y z w*v0001 y z w +
    q0520 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0017Data r0103Data) (product q0018Data r0102Data)) (product q0019Data r0101Data)) (product q0020Data r0100Data)) (product q0115Data r0005Data)) (product q0117Data r0003Data)) (product q0118Data r0002Data)) (product q0119Data r0001Data)) (product q0120Data r0000Data)) (product q0410Data v0110Data)) (product q0411Data v0109Data)) (product q0412Data v0108Data)) (product q0413Data v0107Data)) (product q0414Data v0106Data)) (product q0415Data v0105Data)) (product q0416Data v0104Data)) (product q0417Data v0103Data)) (product q0418Data v0102Data)) (product q0419Data v0101Data)) (product q0420Data v0100Data)) (product q0509Data v0011Data)) (product q0510Data v0010Data)) (product q0511Data v0009Data)) (product q0512Data v0008Data)) (product q0513Data v0007Data)) (product q0514Data v0006Data)) (product q0515Data v0005Data)) (product q0516Data v0004Data)) (product q0517Data v0003Data)) (product q0518Data v0002Data)) (product q0519Data v0001Data)) (product q0520Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0017, q0018, q0019, q0020, q0115, q0117, q0118, q0119, q0120, q0410, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0509, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x20

compact_certificate theorem row1_x21 (y z w : ℂ) :
    q0018 y z w*r0103 y z w +
    q0019 y z w*r0102 y z w +
    q0020 y z w*r0101 y z w +
    q0021 y z w*r0100 y z w +
    q0116 y z w*r0005 y z w +
    q0118 y z w*r0003 y z w +
    q0119 y z w*r0002 y z w +
    q0120 y z w*r0001 y z w +
    q0121 y z w*r0000 y z w +
    q0411 y z w*v0110 y z w +
    q0412 y z w*v0109 y z w +
    q0413 y z w*v0108 y z w +
    q0414 y z w*v0107 y z w +
    q0415 y z w*v0106 y z w +
    q0416 y z w*v0105 y z w +
    q0417 y z w*v0104 y z w +
    q0418 y z w*v0103 y z w +
    q0419 y z w*v0102 y z w +
    q0420 y z w*v0101 y z w +
    q0421 y z w*v0100 y z w +
    q0510 y z w*v0011 y z w +
    q0511 y z w*v0010 y z w +
    q0512 y z w*v0009 y z w +
    q0513 y z w*v0008 y z w +
    q0514 y z w*v0007 y z w +
    q0515 y z w*v0006 y z w +
    q0516 y z w*v0005 y z w +
    q0517 y z w*v0004 y z w +
    q0518 y z w*v0003 y z w +
    q0519 y z w*v0002 y z w +
    q0520 y z w*v0001 y z w +
    q0521 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0018Data r0103Data) (product q0019Data r0102Data)) (product q0020Data r0101Data)) (product q0021Data r0100Data)) (product q0116Data r0005Data)) (product q0118Data r0003Data)) (product q0119Data r0002Data)) (product q0120Data r0001Data)) (product q0121Data r0000Data)) (product q0411Data v0110Data)) (product q0412Data v0109Data)) (product q0413Data v0108Data)) (product q0414Data v0107Data)) (product q0415Data v0106Data)) (product q0416Data v0105Data)) (product q0417Data v0104Data)) (product q0418Data v0103Data)) (product q0419Data v0102Data)) (product q0420Data v0101Data)) (product q0421Data v0100Data)) (product q0510Data v0011Data)) (product q0511Data v0010Data)) (product q0512Data v0009Data)) (product q0513Data v0008Data)) (product q0514Data v0007Data)) (product q0515Data v0006Data)) (product q0516Data v0005Data)) (product q0517Data v0004Data)) (product q0518Data v0003Data)) (product q0519Data v0002Data)) (product q0520Data v0001Data)) (product q0521Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0018, q0019, q0020, q0021, q0116, q0118, q0119, q0120, q0121, q0411, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0510, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x21

compact_certificate theorem row1_x22 (y z w : ℂ) :
    q0019 y z w*r0103 y z w +
    q0020 y z w*r0102 y z w +
    q0021 y z w*r0101 y z w +
    q0022 y z w*r0100 y z w +
    q0117 y z w*r0005 y z w +
    q0119 y z w*r0003 y z w +
    q0120 y z w*r0002 y z w +
    q0121 y z w*r0001 y z w +
    q0122 y z w*r0000 y z w +
    q0412 y z w*v0110 y z w +
    q0413 y z w*v0109 y z w +
    q0414 y z w*v0108 y z w +
    q0415 y z w*v0107 y z w +
    q0416 y z w*v0106 y z w +
    q0417 y z w*v0105 y z w +
    q0418 y z w*v0104 y z w +
    q0419 y z w*v0103 y z w +
    q0420 y z w*v0102 y z w +
    q0421 y z w*v0101 y z w +
    q0422 y z w*v0100 y z w +
    q0511 y z w*v0011 y z w +
    q0512 y z w*v0010 y z w +
    q0513 y z w*v0009 y z w +
    q0514 y z w*v0008 y z w +
    q0515 y z w*v0007 y z w +
    q0516 y z w*v0006 y z w +
    q0517 y z w*v0005 y z w +
    q0518 y z w*v0004 y z w +
    q0519 y z w*v0003 y z w +
    q0520 y z w*v0002 y z w +
    q0521 y z w*v0001 y z w +
    q0522 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0019Data r0103Data) (product q0020Data r0102Data)) (product q0021Data r0101Data)) (product q0022Data r0100Data)) (product q0117Data r0005Data)) (product q0119Data r0003Data)) (product q0120Data r0002Data)) (product q0121Data r0001Data)) (product q0122Data r0000Data)) (product q0412Data v0110Data)) (product q0413Data v0109Data)) (product q0414Data v0108Data)) (product q0415Data v0107Data)) (product q0416Data v0106Data)) (product q0417Data v0105Data)) (product q0418Data v0104Data)) (product q0419Data v0103Data)) (product q0420Data v0102Data)) (product q0421Data v0101Data)) (product q0422Data v0100Data)) (product q0511Data v0011Data)) (product q0512Data v0010Data)) (product q0513Data v0009Data)) (product q0514Data v0008Data)) (product q0515Data v0007Data)) (product q0516Data v0006Data)) (product q0517Data v0005Data)) (product q0518Data v0004Data)) (product q0519Data v0003Data)) (product q0520Data v0002Data)) (product q0521Data v0001Data)) (product q0522Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0019, q0020, q0021, q0022, q0117, q0119, q0120, q0121, q0122, q0412, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0511, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x22

compact_certificate theorem row1_x23 (y z w : ℂ) :
    q0020 y z w*r0103 y z w +
    q0021 y z w*r0102 y z w +
    q0022 y z w*r0101 y z w +
    q0023 y z w*r0100 y z w +
    q0118 y z w*r0005 y z w +
    q0120 y z w*r0003 y z w +
    q0121 y z w*r0002 y z w +
    q0122 y z w*r0001 y z w +
    q0123 y z w*r0000 y z w +
    q0413 y z w*v0110 y z w +
    q0414 y z w*v0109 y z w +
    q0415 y z w*v0108 y z w +
    q0416 y z w*v0107 y z w +
    q0417 y z w*v0106 y z w +
    q0418 y z w*v0105 y z w +
    q0419 y z w*v0104 y z w +
    q0420 y z w*v0103 y z w +
    q0421 y z w*v0102 y z w +
    q0422 y z w*v0101 y z w +
    q0423 y z w*v0100 y z w +
    q0512 y z w*v0011 y z w +
    q0513 y z w*v0010 y z w +
    q0514 y z w*v0009 y z w +
    q0515 y z w*v0008 y z w +
    q0516 y z w*v0007 y z w +
    q0517 y z w*v0006 y z w +
    q0518 y z w*v0005 y z w +
    q0519 y z w*v0004 y z w +
    q0520 y z w*v0003 y z w +
    q0521 y z w*v0002 y z w +
    q0522 y z w*v0001 y z w +
    q0523 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0020Data r0103Data) (product q0021Data r0102Data)) (product q0022Data r0101Data)) (product q0023Data r0100Data)) (product q0118Data r0005Data)) (product q0120Data r0003Data)) (product q0121Data r0002Data)) (product q0122Data r0001Data)) (product q0123Data r0000Data)) (product q0413Data v0110Data)) (product q0414Data v0109Data)) (product q0415Data v0108Data)) (product q0416Data v0107Data)) (product q0417Data v0106Data)) (product q0418Data v0105Data)) (product q0419Data v0104Data)) (product q0420Data v0103Data)) (product q0421Data v0102Data)) (product q0422Data v0101Data)) (product q0423Data v0100Data)) (product q0512Data v0011Data)) (product q0513Data v0010Data)) (product q0514Data v0009Data)) (product q0515Data v0008Data)) (product q0516Data v0007Data)) (product q0517Data v0006Data)) (product q0518Data v0005Data)) (product q0519Data v0004Data)) (product q0520Data v0003Data)) (product q0521Data v0002Data)) (product q0522Data v0001Data)) (product q0523Data v0000Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0020, q0021, q0022, q0023, q0118, q0120, q0121, q0122, q0123, q0413, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0512, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x23

compact_certificate theorem row1_x24 (y z w : ℂ) :
    q0021 y z w*r0103 y z w +
    q0022 y z w*r0102 y z w +
    q0023 y z w*r0101 y z w +
    q0024 y z w*r0100 y z w +
    q0119 y z w*r0005 y z w +
    q0121 y z w*r0003 y z w +
    q0122 y z w*r0002 y z w +
    q0123 y z w*r0001 y z w +
    q0124 y z w*r0000 y z w +
    q0414 y z w*v0110 y z w +
    q0415 y z w*v0109 y z w +
    q0416 y z w*v0108 y z w +
    q0417 y z w*v0107 y z w +
    q0418 y z w*v0106 y z w +
    q0419 y z w*v0105 y z w +
    q0420 y z w*v0104 y z w +
    q0421 y z w*v0103 y z w +
    q0422 y z w*v0102 y z w +
    q0423 y z w*v0101 y z w +
    q0424 y z w*v0100 y z w +
    q0513 y z w*v0011 y z w +
    q0514 y z w*v0010 y z w +
    q0515 y z w*v0009 y z w +
    q0516 y z w*v0008 y z w +
    q0517 y z w*v0007 y z w +
    q0518 y z w*v0006 y z w +
    q0519 y z w*v0005 y z w +
    q0520 y z w*v0004 y z w +
    q0521 y z w*v0003 y z w +
    q0522 y z w*v0002 y z w +
    q0523 y z w*v0001 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0021Data r0103Data) (product q0022Data r0102Data)) (product q0023Data r0101Data)) (product q0024Data r0100Data)) (product q0119Data r0005Data)) (product q0121Data r0003Data)) (product q0122Data r0002Data)) (product q0123Data r0001Data)) (product q0124Data r0000Data)) (product q0414Data v0110Data)) (product q0415Data v0109Data)) (product q0416Data v0108Data)) (product q0417Data v0107Data)) (product q0418Data v0106Data)) (product q0419Data v0105Data)) (product q0420Data v0104Data)) (product q0421Data v0103Data)) (product q0422Data v0102Data)) (product q0423Data v0101Data)) (product q0424Data v0100Data)) (product q0513Data v0011Data)) (product q0514Data v0010Data)) (product q0515Data v0009Data)) (product q0516Data v0008Data)) (product q0517Data v0007Data)) (product q0518Data v0006Data)) (product q0519Data v0005Data)) (product q0520Data v0004Data)) (product q0521Data v0003Data)) (product q0522Data v0002Data)) (product q0523Data v0001Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0021, q0022, q0023, q0024, q0119, q0121, q0122, q0123, q0124, q0414, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0513, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x24

compact_certificate theorem row1_x25 (y z w : ℂ) :
    q0022 y z w*r0103 y z w +
    q0023 y z w*r0102 y z w +
    q0024 y z w*r0101 y z w +
    q0025 y z w*r0100 y z w +
    q0120 y z w*r0005 y z w +
    q0122 y z w*r0003 y z w +
    q0123 y z w*r0002 y z w +
    q0124 y z w*r0001 y z w +
    q0125 y z w*r0000 y z w +
    q0415 y z w*v0110 y z w +
    q0416 y z w*v0109 y z w +
    q0417 y z w*v0108 y z w +
    q0418 y z w*v0107 y z w +
    q0419 y z w*v0106 y z w +
    q0420 y z w*v0105 y z w +
    q0421 y z w*v0104 y z w +
    q0422 y z w*v0103 y z w +
    q0423 y z w*v0102 y z w +
    q0424 y z w*v0101 y z w +
    q0514 y z w*v0011 y z w +
    q0515 y z w*v0010 y z w +
    q0516 y z w*v0009 y z w +
    q0517 y z w*v0008 y z w +
    q0518 y z w*v0007 y z w +
    q0519 y z w*v0006 y z w +
    q0520 y z w*v0005 y z w +
    q0521 y z w*v0004 y z w +
    q0522 y z w*v0003 y z w +
    q0523 y z w*v0002 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0022Data r0103Data) (product q0023Data r0102Data)) (product q0024Data r0101Data)) (product q0025Data r0100Data)) (product q0120Data r0005Data)) (product q0122Data r0003Data)) (product q0123Data r0002Data)) (product q0124Data r0001Data)) (product q0125Data r0000Data)) (product q0415Data v0110Data)) (product q0416Data v0109Data)) (product q0417Data v0108Data)) (product q0418Data v0107Data)) (product q0419Data v0106Data)) (product q0420Data v0105Data)) (product q0421Data v0104Data)) (product q0422Data v0103Data)) (product q0423Data v0102Data)) (product q0424Data v0101Data)) (product q0514Data v0011Data)) (product q0515Data v0010Data)) (product q0516Data v0009Data)) (product q0517Data v0008Data)) (product q0518Data v0007Data)) (product q0519Data v0006Data)) (product q0520Data v0005Data)) (product q0521Data v0004Data)) (product q0522Data v0003Data)) (product q0523Data v0002Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0022, q0023, q0024, q0025, q0120, q0122, q0123, q0124, q0125, q0415, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0514, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x25

compact_certificate theorem row1_x26 (y z w : ℂ) :
    q0023 y z w*r0103 y z w +
    q0024 y z w*r0102 y z w +
    q0025 y z w*r0101 y z w +
    q0026 y z w*r0100 y z w +
    q0121 y z w*r0005 y z w +
    q0123 y z w*r0003 y z w +
    q0124 y z w*r0002 y z w +
    q0125 y z w*r0001 y z w +
    q0126 y z w*r0000 y z w +
    q0416 y z w*v0110 y z w +
    q0417 y z w*v0109 y z w +
    q0418 y z w*v0108 y z w +
    q0419 y z w*v0107 y z w +
    q0420 y z w*v0106 y z w +
    q0421 y z w*v0105 y z w +
    q0422 y z w*v0104 y z w +
    q0423 y z w*v0103 y z w +
    q0424 y z w*v0102 y z w +
    q0515 y z w*v0011 y z w +
    q0516 y z w*v0010 y z w +
    q0517 y z w*v0009 y z w +
    q0518 y z w*v0008 y z w +
    q0519 y z w*v0007 y z w +
    q0520 y z w*v0006 y z w +
    q0521 y z w*v0005 y z w +
    q0522 y z w*v0004 y z w +
    q0523 y z w*v0003 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0023Data r0103Data) (product q0024Data r0102Data)) (product q0025Data r0101Data)) (product q0026Data r0100Data)) (product q0121Data r0005Data)) (product q0123Data r0003Data)) (product q0124Data r0002Data)) (product q0125Data r0001Data)) (product q0126Data r0000Data)) (product q0416Data v0110Data)) (product q0417Data v0109Data)) (product q0418Data v0108Data)) (product q0419Data v0107Data)) (product q0420Data v0106Data)) (product q0421Data v0105Data)) (product q0422Data v0104Data)) (product q0423Data v0103Data)) (product q0424Data v0102Data)) (product q0515Data v0011Data)) (product q0516Data v0010Data)) (product q0517Data v0009Data)) (product q0518Data v0008Data)) (product q0519Data v0007Data)) (product q0520Data v0006Data)) (product q0521Data v0005Data)) (product q0522Data v0004Data)) (product q0523Data v0003Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0023, q0024, q0025, q0026, q0121, q0123, q0124, q0125, q0126, q0416, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0515, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x26

compact_certificate theorem row1_x27 (y z w : ℂ) :
    q0024 y z w*r0103 y z w +
    q0025 y z w*r0102 y z w +
    q0026 y z w*r0101 y z w +
    q0027 y z w*r0100 y z w +
    q0122 y z w*r0005 y z w +
    q0124 y z w*r0003 y z w +
    q0125 y z w*r0002 y z w +
    q0126 y z w*r0001 y z w +
    q0127 y z w*r0000 y z w +
    q0417 y z w*v0110 y z w +
    q0418 y z w*v0109 y z w +
    q0419 y z w*v0108 y z w +
    q0420 y z w*v0107 y z w +
    q0421 y z w*v0106 y z w +
    q0422 y z w*v0105 y z w +
    q0423 y z w*v0104 y z w +
    q0424 y z w*v0103 y z w +
    q0516 y z w*v0011 y z w +
    q0517 y z w*v0010 y z w +
    q0518 y z w*v0009 y z w +
    q0519 y z w*v0008 y z w +
    q0520 y z w*v0007 y z w +
    q0521 y z w*v0006 y z w +
    q0522 y z w*v0005 y z w +
    q0523 y z w*v0004 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0024Data r0103Data) (product q0025Data r0102Data)) (product q0026Data r0101Data)) (product q0027Data r0100Data)) (product q0122Data r0005Data)) (product q0124Data r0003Data)) (product q0125Data r0002Data)) (product q0126Data r0001Data)) (product q0127Data r0000Data)) (product q0417Data v0110Data)) (product q0418Data v0109Data)) (product q0419Data v0108Data)) (product q0420Data v0107Data)) (product q0421Data v0106Data)) (product q0422Data v0105Data)) (product q0423Data v0104Data)) (product q0424Data v0103Data)) (product q0516Data v0011Data)) (product q0517Data v0010Data)) (product q0518Data v0009Data)) (product q0519Data v0008Data)) (product q0520Data v0007Data)) (product q0521Data v0006Data)) (product q0522Data v0005Data)) (product q0523Data v0004Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0024, q0025, q0026, q0027, q0122, q0124, q0125, q0126, q0127, q0417, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0516, q0517, q0518, q0519, q0520, q0521, q0522, q0523, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x27

compact_certificate theorem row1_x28 (y z w : ℂ) :
    q0025 y z w*r0103 y z w +
    q0026 y z w*r0102 y z w +
    q0027 y z w*r0101 y z w +
    q0028 y z w*r0100 y z w +
    q0123 y z w*r0005 y z w +
    q0125 y z w*r0003 y z w +
    q0126 y z w*r0002 y z w +
    q0127 y z w*r0001 y z w +
    q0128 y z w*r0000 y z w +
    q0418 y z w*v0110 y z w +
    q0419 y z w*v0109 y z w +
    q0420 y z w*v0108 y z w +
    q0421 y z w*v0107 y z w +
    q0422 y z w*v0106 y z w +
    q0423 y z w*v0105 y z w +
    q0424 y z w*v0104 y z w +
    q0517 y z w*v0011 y z w +
    q0518 y z w*v0010 y z w +
    q0519 y z w*v0009 y z w +
    q0520 y z w*v0008 y z w +
    q0521 y z w*v0007 y z w +
    q0522 y z w*v0006 y z w +
    q0523 y z w*v0005 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0025Data r0103Data) (product q0026Data r0102Data)) (product q0027Data r0101Data)) (product q0028Data r0100Data)) (product q0123Data r0005Data)) (product q0125Data r0003Data)) (product q0126Data r0002Data)) (product q0127Data r0001Data)) (product q0128Data r0000Data)) (product q0418Data v0110Data)) (product q0419Data v0109Data)) (product q0420Data v0108Data)) (product q0421Data v0107Data)) (product q0422Data v0106Data)) (product q0423Data v0105Data)) (product q0424Data v0104Data)) (product q0517Data v0011Data)) (product q0518Data v0010Data)) (product q0519Data v0009Data)) (product q0520Data v0008Data)) (product q0521Data v0007Data)) (product q0522Data v0006Data)) (product q0523Data v0005Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0025, q0026, q0027, q0028, q0123, q0125, q0126, q0127, q0128, q0418, q0419, q0420, q0421, q0422, q0423, q0424, q0517, q0518, q0519, q0520, q0521, q0522, q0523, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0005, v0006, v0007, v0008, v0009, v0010, v0011, v0104, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x28

compact_certificate theorem row1_x29 (y z w : ℂ) :
    q0026 y z w*r0103 y z w +
    q0027 y z w*r0102 y z w +
    q0028 y z w*r0101 y z w +
    q0029 y z w*r0100 y z w +
    q0124 y z w*r0005 y z w +
    q0126 y z w*r0003 y z w +
    q0127 y z w*r0002 y z w +
    q0128 y z w*r0001 y z w +
    q0129 y z w*r0000 y z w +
    q0419 y z w*v0110 y z w +
    q0420 y z w*v0109 y z w +
    q0421 y z w*v0108 y z w +
    q0422 y z w*v0107 y z w +
    q0423 y z w*v0106 y z w +
    q0424 y z w*v0105 y z w +
    q0518 y z w*v0011 y z w +
    q0519 y z w*v0010 y z w +
    q0520 y z w*v0009 y z w +
    q0521 y z w*v0008 y z w +
    q0522 y z w*v0007 y z w +
    q0523 y z w*v0006 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0026Data r0103Data) (product q0027Data r0102Data)) (product q0028Data r0101Data)) (product q0029Data r0100Data)) (product q0124Data r0005Data)) (product q0126Data r0003Data)) (product q0127Data r0002Data)) (product q0128Data r0001Data)) (product q0129Data r0000Data)) (product q0419Data v0110Data)) (product q0420Data v0109Data)) (product q0421Data v0108Data)) (product q0422Data v0107Data)) (product q0423Data v0106Data)) (product q0424Data v0105Data)) (product q0518Data v0011Data)) (product q0519Data v0010Data)) (product q0520Data v0009Data)) (product q0521Data v0008Data)) (product q0522Data v0007Data)) (product q0523Data v0006Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0026, q0027, q0028, q0029, q0124, q0126, q0127, q0128, q0129, q0419, q0420, q0421, q0422, q0423, q0424, q0518, q0519, q0520, q0521, q0522, q0523, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0006, v0007, v0008, v0009, v0010, v0011, v0105, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x29

compact_certificate theorem row1_x30 (y z w : ℂ) :
    q0027 y z w*r0103 y z w +
    q0028 y z w*r0102 y z w +
    q0029 y z w*r0101 y z w +
    q0030 y z w*r0100 y z w +
    q0125 y z w*r0005 y z w +
    q0127 y z w*r0003 y z w +
    q0128 y z w*r0002 y z w +
    q0129 y z w*r0001 y z w +
    q0420 y z w*v0110 y z w +
    q0421 y z w*v0109 y z w +
    q0422 y z w*v0108 y z w +
    q0423 y z w*v0107 y z w +
    q0424 y z w*v0106 y z w +
    q0519 y z w*v0011 y z w +
    q0520 y z w*v0010 y z w +
    q0521 y z w*v0009 y z w +
    q0522 y z w*v0008 y z w +
    q0523 y z w*v0007 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0027Data r0103Data) (product q0028Data r0102Data)) (product q0029Data r0101Data)) (product q0030Data r0100Data)) (product q0125Data r0005Data)) (product q0127Data r0003Data)) (product q0128Data r0002Data)) (product q0129Data r0001Data)) (product q0420Data v0110Data)) (product q0421Data v0109Data)) (product q0422Data v0108Data)) (product q0423Data v0107Data)) (product q0424Data v0106Data)) (product q0519Data v0011Data)) (product q0520Data v0010Data)) (product q0521Data v0009Data)) (product q0522Data v0008Data)) (product q0523Data v0007Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0027, q0028, q0029, q0030, q0125, q0127, q0128, q0129, q0420, q0421, q0422, q0423, q0424, q0519, q0520, q0521, q0522, q0523, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, v0007, v0008, v0009, v0010, v0011, v0106, v0107, v0108, v0109, v0110] using he

#print axioms row1_x30

compact_certificate theorem row1_x31 (y z w : ℂ) :
    q0028 y z w*r0103 y z w +
    q0029 y z w*r0102 y z w +
    q0030 y z w*r0101 y z w +
    q0126 y z w*r0005 y z w +
    q0128 y z w*r0003 y z w +
    q0129 y z w*r0002 y z w +
    q0421 y z w*v0110 y z w +
    q0422 y z w*v0109 y z w +
    q0423 y z w*v0108 y z w +
    q0424 y z w*v0107 y z w +
    q0520 y z w*v0011 y z w +
    q0521 y z w*v0010 y z w +
    q0522 y z w*v0009 y z w +
    q0523 y z w*v0008 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0028Data r0103Data) (product q0029Data r0102Data)) (product q0030Data r0101Data)) (product q0126Data r0005Data)) (product q0128Data r0003Data)) (product q0129Data r0002Data)) (product q0421Data v0110Data)) (product q0422Data v0109Data)) (product q0423Data v0108Data)) (product q0424Data v0107Data)) (product q0520Data v0011Data)) (product q0521Data v0010Data)) (product q0522Data v0009Data)) (product q0523Data v0008Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0028, q0029, q0030, q0126, q0128, q0129, q0421, q0422, q0423, q0424, q0520, q0521, q0522, q0523, r0002, r0003, r0005, r0101, r0102, r0103, v0008, v0009, v0010, v0011, v0107, v0108, v0109, v0110] using he

#print axioms row1_x31

compact_certificate theorem row1_x32 (y z w : ℂ) :
    q0029 y z w*r0103 y z w +
    q0030 y z w*r0102 y z w +
    q0127 y z w*r0005 y z w +
    q0129 y z w*r0003 y z w +
    q0422 y z w*v0110 y z w +
    q0423 y z w*v0109 y z w +
    q0424 y z w*v0108 y z w +
    q0521 y z w*v0011 y z w +
    q0522 y z w*v0010 y z w +
    q0523 y z w*v0009 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0029Data r0103Data) (product q0030Data r0102Data)) (product q0127Data r0005Data)) (product q0129Data r0003Data)) (product q0422Data v0110Data)) (product q0423Data v0109Data)) (product q0424Data v0108Data)) (product q0521Data v0011Data)) (product q0522Data v0010Data)) (product q0523Data v0009Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0029, q0030, q0127, q0129, q0422, q0423, q0424, q0521, q0522, q0523, r0003, r0005, r0102, r0103, v0009, v0010, v0011, v0108, v0109, v0110] using he

#print axioms row1_x32

compact_certificate theorem row1_x33 (y z w : ℂ) :
    q0030 y z w*r0103 y z w +
    q0128 y z w*r0005 y z w +
    q0423 y z w*v0110 y z w +
    q0424 y z w*v0109 y z w +
    q0522 y z w*v0011 y z w +
    q0523 y z w*v0010 y z w=0 := by
  have h : (merge (merge (merge (merge (merge (product q0030Data r0103Data) (product q0128Data r0005Data)) (product q0423Data v0110Data)) (product q0424Data v0109Data)) (product q0522Data v0011Data)) (product q0523Data v0010Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0030, q0128, q0423, q0424, q0522, q0523, r0005, r0103, v0010, v0011, v0109, v0110] using he

#print axioms row1_x33

compact_certificate theorem row1_x34 (y z w : ℂ) :
    q0129 y z w*r0005 y z w +
    q0424 y z w*v0110 y z w +
    q0523 y z w*v0011 y z w=0 := by
  have h : (merge (merge (product q0129Data r0005Data) (product q0424Data v0110Data)) (product q0523Data v0011Data)) = [] := by staged_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0129, q0424, q0523, r0005, v0011, v0110] using he

#print axioms row1_x34

compact_certificate theorem row1_x35 (_y _z _w : ℂ) : (0:ℂ)=0 := rfl
#print axioms row1_x35

compact_certificate theorem row1_coefficient17 (y z w : ℂ) : (rowPoly1 y z w).coeff 17=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x17 y z w

#print axioms row1_coefficient17

compact_certificate theorem row1_coefficient18 (y z w : ℂ) : (rowPoly1 y z w).coeff 18=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x18 y z w

#print axioms row1_coefficient18

compact_certificate theorem row1_coefficient19 (y z w : ℂ) : (rowPoly1 y z w).coeff 19=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x19 y z w

#print axioms row1_coefficient19

compact_certificate theorem row1_coefficient20 (y z w : ℂ) : (rowPoly1 y z w).coeff 20=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x20 y z w

#print axioms row1_coefficient20

compact_certificate theorem row1_coefficient21 (y z w : ℂ) : (rowPoly1 y z w).coeff 21=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x21 y z w

#print axioms row1_coefficient21

compact_certificate theorem row1_coefficient22 (y z w : ℂ) : (rowPoly1 y z w).coeff 22=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x22 y z w

#print axioms row1_coefficient22

compact_certificate theorem row1_coefficient23 (y z w : ℂ) : (rowPoly1 y z w).coeff 23=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x23 y z w

#print axioms row1_coefficient23

compact_certificate theorem row1_coefficient24 (y z w : ℂ) : (rowPoly1 y z w).coeff 24=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x24 y z w

#print axioms row1_coefficient24

compact_certificate theorem row1_coefficient25 (y z w : ℂ) : (rowPoly1 y z w).coeff 25=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x25 y z w

#print axioms row1_coefficient25

compact_certificate theorem row1_coefficient26 (y z w : ℂ) : (rowPoly1 y z w).coeff 26=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x26 y z w

#print axioms row1_coefficient26

compact_certificate theorem row1_coefficient27 (y z w : ℂ) : (rowPoly1 y z w).coeff 27=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x27 y z w

#print axioms row1_coefficient27

compact_certificate theorem row1_coefficient28 (y z w : ℂ) : (rowPoly1 y z w).coeff 28=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x28 y z w

#print axioms row1_coefficient28

compact_certificate theorem row1_coefficient29 (y z w : ℂ) : (rowPoly1 y z w).coeff 29=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x29 y z w

#print axioms row1_coefficient29

compact_certificate theorem row1_coefficient30 (y z w : ℂ) : (rowPoly1 y z w).coeff 30=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x30 y z w

#print axioms row1_coefficient30

compact_certificate theorem row1_coefficient31 (y z w : ℂ) : (rowPoly1 y z w).coeff 31=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x31 y z w

#print axioms row1_coefficient31

compact_certificate theorem row1_coefficient32 (y z w : ℂ) : (rowPoly1 y z w).coeff 32=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x32 y z w

#print axioms row1_coefficient32

compact_certificate theorem row1_coefficient33 (y z w : ℂ) : (rowPoly1 y z w).coeff 33=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x33 y z w

#print axioms row1_coefficient33

compact_certificate theorem row1_coefficient34 (y z w : ℂ) : (rowPoly1 y z w).coeff 34=0 := by
  simpa [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc] using row1_x34 y z w

#print axioms row1_coefficient34

compact_certificate theorem row1_coefficient35 (y z w : ℂ) : (rowPoly1 y z w).coeff 35=0 := by
  simp [rowPoly1,qPoly0,rPoly1,qPoly1,rPoly0,qPoly4,vPoly1,qPoly5,vPoly0,coeff_add,coeff_mul_range,Finset.sum_range_succ,add_assoc]

#print axioms row1_coefficient35


}
end SmallLevelTwentySixResultantBatchedMMM
end
end
