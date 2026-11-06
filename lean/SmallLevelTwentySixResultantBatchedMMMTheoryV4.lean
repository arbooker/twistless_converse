module

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelCubicQuarticSylvesterV1
public import SmallLevelTwentySixResultantBatchedMMMZeroGroupedTheoryV4
public import SmallLevelTwentySixResultantCoefficientsMMMTheoryV4
public meta import QuantitativeArithmeticCompactCommandsV1

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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0014Data r0103Data) (product q0015Data r0102Data)) (product q0016Data r0101Data)) (product q0017Data r0100Data)) (product q0112Data r0005Data)) (product q0114Data r0003Data)) (product q0115Data r0002Data)) (product q0116Data r0001Data)) (product q0117Data r0000Data)) (product q0407Data v0110Data)) (product q0408Data v0109Data)) (product q0409Data v0108Data)) (product q0410Data v0107Data)) (product q0411Data v0106Data)) (product q0412Data v0105Data)) (product q0413Data v0104Data)) (product q0414Data v0103Data)) (product q0415Data v0102Data)) (product q0416Data v0101Data)) (product q0417Data v0100Data)) (product q0506Data v0011Data)) (product q0507Data v0010Data)) (product q0508Data v0009Data)) (product q0509Data v0008Data)) (product q0510Data v0007Data)) (product q0511Data v0006Data)) (product q0512Data v0005Data)) (product q0513Data v0004Data)) (product q0514Data v0003Data)) (product q0515Data v0002Data)) (product q0516Data v0001Data)) (product q0517Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0015Data r0103Data) (product q0016Data r0102Data)) (product q0017Data r0101Data)) (product q0018Data r0100Data)) (product q0113Data r0005Data)) (product q0115Data r0003Data)) (product q0116Data r0002Data)) (product q0117Data r0001Data)) (product q0118Data r0000Data)) (product q0408Data v0110Data)) (product q0409Data v0109Data)) (product q0410Data v0108Data)) (product q0411Data v0107Data)) (product q0412Data v0106Data)) (product q0413Data v0105Data)) (product q0414Data v0104Data)) (product q0415Data v0103Data)) (product q0416Data v0102Data)) (product q0417Data v0101Data)) (product q0418Data v0100Data)) (product q0507Data v0011Data)) (product q0508Data v0010Data)) (product q0509Data v0009Data)) (product q0510Data v0008Data)) (product q0511Data v0007Data)) (product q0512Data v0006Data)) (product q0513Data v0005Data)) (product q0514Data v0004Data)) (product q0515Data v0003Data)) (product q0516Data v0002Data)) (product q0517Data v0001Data)) (product q0518Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0016Data r0103Data) (product q0017Data r0102Data)) (product q0018Data r0101Data)) (product q0019Data r0100Data)) (product q0114Data r0005Data)) (product q0116Data r0003Data)) (product q0117Data r0002Data)) (product q0118Data r0001Data)) (product q0119Data r0000Data)) (product q0409Data v0110Data)) (product q0410Data v0109Data)) (product q0411Data v0108Data)) (product q0412Data v0107Data)) (product q0413Data v0106Data)) (product q0414Data v0105Data)) (product q0415Data v0104Data)) (product q0416Data v0103Data)) (product q0417Data v0102Data)) (product q0418Data v0101Data)) (product q0419Data v0100Data)) (product q0508Data v0011Data)) (product q0509Data v0010Data)) (product q0510Data v0009Data)) (product q0511Data v0008Data)) (product q0512Data v0007Data)) (product q0513Data v0006Data)) (product q0514Data v0005Data)) (product q0515Data v0004Data)) (product q0516Data v0003Data)) (product q0517Data v0002Data)) (product q0518Data v0001Data)) (product q0519Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0017Data r0103Data) (product q0018Data r0102Data)) (product q0019Data r0101Data)) (product q0020Data r0100Data)) (product q0115Data r0005Data)) (product q0117Data r0003Data)) (product q0118Data r0002Data)) (product q0119Data r0001Data)) (product q0120Data r0000Data)) (product q0410Data v0110Data)) (product q0411Data v0109Data)) (product q0412Data v0108Data)) (product q0413Data v0107Data)) (product q0414Data v0106Data)) (product q0415Data v0105Data)) (product q0416Data v0104Data)) (product q0417Data v0103Data)) (product q0418Data v0102Data)) (product q0419Data v0101Data)) (product q0420Data v0100Data)) (product q0509Data v0011Data)) (product q0510Data v0010Data)) (product q0511Data v0009Data)) (product q0512Data v0008Data)) (product q0513Data v0007Data)) (product q0514Data v0006Data)) (product q0515Data v0005Data)) (product q0516Data v0004Data)) (product q0517Data v0003Data)) (product q0518Data v0002Data)) (product q0519Data v0001Data)) (product q0520Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0018Data r0103Data) (product q0019Data r0102Data)) (product q0020Data r0101Data)) (product q0021Data r0100Data)) (product q0116Data r0005Data)) (product q0118Data r0003Data)) (product q0119Data r0002Data)) (product q0120Data r0001Data)) (product q0121Data r0000Data)) (product q0411Data v0110Data)) (product q0412Data v0109Data)) (product q0413Data v0108Data)) (product q0414Data v0107Data)) (product q0415Data v0106Data)) (product q0416Data v0105Data)) (product q0417Data v0104Data)) (product q0418Data v0103Data)) (product q0419Data v0102Data)) (product q0420Data v0101Data)) (product q0421Data v0100Data)) (product q0510Data v0011Data)) (product q0511Data v0010Data)) (product q0512Data v0009Data)) (product q0513Data v0008Data)) (product q0514Data v0007Data)) (product q0515Data v0006Data)) (product q0516Data v0005Data)) (product q0517Data v0004Data)) (product q0518Data v0003Data)) (product q0519Data v0002Data)) (product q0520Data v0001Data)) (product q0521Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0019Data r0103Data) (product q0020Data r0102Data)) (product q0021Data r0101Data)) (product q0022Data r0100Data)) (product q0117Data r0005Data)) (product q0119Data r0003Data)) (product q0120Data r0002Data)) (product q0121Data r0001Data)) (product q0122Data r0000Data)) (product q0412Data v0110Data)) (product q0413Data v0109Data)) (product q0414Data v0108Data)) (product q0415Data v0107Data)) (product q0416Data v0106Data)) (product q0417Data v0105Data)) (product q0418Data v0104Data)) (product q0419Data v0103Data)) (product q0420Data v0102Data)) (product q0421Data v0101Data)) (product q0422Data v0100Data)) (product q0511Data v0011Data)) (product q0512Data v0010Data)) (product q0513Data v0009Data)) (product q0514Data v0008Data)) (product q0515Data v0007Data)) (product q0516Data v0006Data)) (product q0517Data v0005Data)) (product q0518Data v0004Data)) (product q0519Data v0003Data)) (product q0520Data v0002Data)) (product q0521Data v0001Data)) (product q0522Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0020Data r0103Data) (product q0021Data r0102Data)) (product q0022Data r0101Data)) (product q0023Data r0100Data)) (product q0118Data r0005Data)) (product q0120Data r0003Data)) (product q0121Data r0002Data)) (product q0122Data r0001Data)) (product q0123Data r0000Data)) (product q0413Data v0110Data)) (product q0414Data v0109Data)) (product q0415Data v0108Data)) (product q0416Data v0107Data)) (product q0417Data v0106Data)) (product q0418Data v0105Data)) (product q0419Data v0104Data)) (product q0420Data v0103Data)) (product q0421Data v0102Data)) (product q0422Data v0101Data)) (product q0423Data v0100Data)) (product q0512Data v0011Data)) (product q0513Data v0010Data)) (product q0514Data v0009Data)) (product q0515Data v0008Data)) (product q0516Data v0007Data)) (product q0517Data v0006Data)) (product q0518Data v0005Data)) (product q0519Data v0004Data)) (product q0520Data v0003Data)) (product q0521Data v0002Data)) (product q0522Data v0001Data)) (product q0523Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0021Data r0103Data) (product q0022Data r0102Data)) (product q0023Data r0101Data)) (product q0024Data r0100Data)) (product q0119Data r0005Data)) (product q0121Data r0003Data)) (product q0122Data r0002Data)) (product q0123Data r0001Data)) (product q0124Data r0000Data)) (product q0414Data v0110Data)) (product q0415Data v0109Data)) (product q0416Data v0108Data)) (product q0417Data v0107Data)) (product q0418Data v0106Data)) (product q0419Data v0105Data)) (product q0420Data v0104Data)) (product q0421Data v0103Data)) (product q0422Data v0102Data)) (product q0423Data v0101Data)) (product q0424Data v0100Data)) (product q0513Data v0011Data)) (product q0514Data v0010Data)) (product q0515Data v0009Data)) (product q0516Data v0008Data)) (product q0517Data v0007Data)) (product q0518Data v0006Data)) (product q0519Data v0005Data)) (product q0520Data v0004Data)) (product q0521Data v0003Data)) (product q0522Data v0002Data)) (product q0523Data v0001Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0022Data r0103Data) (product q0023Data r0102Data)) (product q0024Data r0101Data)) (product q0025Data r0100Data)) (product q0120Data r0005Data)) (product q0122Data r0003Data)) (product q0123Data r0002Data)) (product q0124Data r0001Data)) (product q0125Data r0000Data)) (product q0415Data v0110Data)) (product q0416Data v0109Data)) (product q0417Data v0108Data)) (product q0418Data v0107Data)) (product q0419Data v0106Data)) (product q0420Data v0105Data)) (product q0421Data v0104Data)) (product q0422Data v0103Data)) (product q0423Data v0102Data)) (product q0424Data v0101Data)) (product q0514Data v0011Data)) (product q0515Data v0010Data)) (product q0516Data v0009Data)) (product q0517Data v0008Data)) (product q0518Data v0007Data)) (product q0519Data v0006Data)) (product q0520Data v0005Data)) (product q0521Data v0004Data)) (product q0522Data v0003Data)) (product q0523Data v0002Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0023Data r0103Data) (product q0024Data r0102Data)) (product q0025Data r0101Data)) (product q0026Data r0100Data)) (product q0121Data r0005Data)) (product q0123Data r0003Data)) (product q0124Data r0002Data)) (product q0125Data r0001Data)) (product q0126Data r0000Data)) (product q0416Data v0110Data)) (product q0417Data v0109Data)) (product q0418Data v0108Data)) (product q0419Data v0107Data)) (product q0420Data v0106Data)) (product q0421Data v0105Data)) (product q0422Data v0104Data)) (product q0423Data v0103Data)) (product q0424Data v0102Data)) (product q0515Data v0011Data)) (product q0516Data v0010Data)) (product q0517Data v0009Data)) (product q0518Data v0008Data)) (product q0519Data v0007Data)) (product q0520Data v0006Data)) (product q0521Data v0005Data)) (product q0522Data v0004Data)) (product q0523Data v0003Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0024Data r0103Data) (product q0025Data r0102Data)) (product q0026Data r0101Data)) (product q0027Data r0100Data)) (product q0122Data r0005Data)) (product q0124Data r0003Data)) (product q0125Data r0002Data)) (product q0126Data r0001Data)) (product q0127Data r0000Data)) (product q0417Data v0110Data)) (product q0418Data v0109Data)) (product q0419Data v0108Data)) (product q0420Data v0107Data)) (product q0421Data v0106Data)) (product q0422Data v0105Data)) (product q0423Data v0104Data)) (product q0424Data v0103Data)) (product q0516Data v0011Data)) (product q0517Data v0010Data)) (product q0518Data v0009Data)) (product q0519Data v0008Data)) (product q0520Data v0007Data)) (product q0521Data v0006Data)) (product q0522Data v0005Data)) (product q0523Data v0004Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0025Data r0103Data) (product q0026Data r0102Data)) (product q0027Data r0101Data)) (product q0028Data r0100Data)) (product q0123Data r0005Data)) (product q0125Data r0003Data)) (product q0126Data r0002Data)) (product q0127Data r0001Data)) (product q0128Data r0000Data)) (product q0418Data v0110Data)) (product q0419Data v0109Data)) (product q0420Data v0108Data)) (product q0421Data v0107Data)) (product q0422Data v0106Data)) (product q0423Data v0105Data)) (product q0424Data v0104Data)) (product q0517Data v0011Data)) (product q0518Data v0010Data)) (product q0519Data v0009Data)) (product q0520Data v0008Data)) (product q0521Data v0007Data)) (product q0522Data v0006Data)) (product q0523Data v0005Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0026Data r0103Data) (product q0027Data r0102Data)) (product q0028Data r0101Data)) (product q0029Data r0100Data)) (product q0124Data r0005Data)) (product q0126Data r0003Data)) (product q0127Data r0002Data)) (product q0128Data r0001Data)) (product q0129Data r0000Data)) (product q0419Data v0110Data)) (product q0420Data v0109Data)) (product q0421Data v0108Data)) (product q0422Data v0107Data)) (product q0423Data v0106Data)) (product q0424Data v0105Data)) (product q0518Data v0011Data)) (product q0519Data v0010Data)) (product q0520Data v0009Data)) (product q0521Data v0008Data)) (product q0522Data v0007Data)) (product q0523Data v0006Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0027Data r0103Data) (product q0028Data r0102Data)) (product q0029Data r0101Data)) (product q0030Data r0100Data)) (product q0125Data r0005Data)) (product q0127Data r0003Data)) (product q0128Data r0002Data)) (product q0129Data r0001Data)) (product q0420Data v0110Data)) (product q0421Data v0109Data)) (product q0422Data v0108Data)) (product q0423Data v0107Data)) (product q0424Data v0106Data)) (product q0519Data v0011Data)) (product q0520Data v0010Data)) (product q0521Data v0009Data)) (product q0522Data v0008Data)) (product q0523Data v0007Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0028Data r0103Data) (product q0029Data r0102Data)) (product q0030Data r0101Data)) (product q0126Data r0005Data)) (product q0128Data r0003Data)) (product q0129Data r0002Data)) (product q0421Data v0110Data)) (product q0422Data v0109Data)) (product q0423Data v0108Data)) (product q0424Data v0107Data)) (product q0520Data v0011Data)) (product q0521Data v0010Data)) (product q0522Data v0009Data)) (product q0523Data v0008Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0029Data r0103Data) (product q0030Data r0102Data)) (product q0127Data r0005Data)) (product q0129Data r0003Data)) (product q0422Data v0110Data)) (product q0423Data v0109Data)) (product q0424Data v0108Data)) (product q0521Data v0011Data)) (product q0522Data v0010Data)) (product q0523Data v0009Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (product q0030Data r0103Data) (product q0128Data r0005Data)) (product q0423Data v0110Data)) (product q0424Data v0109Data)) (product q0522Data v0011Data)) (product q0523Data v0010Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0030, q0128, q0423, q0424, q0522, q0523, r0005, r0103, v0010, v0011, v0109, v0110] using he

#print axioms row1_x33

compact_certificate theorem row1_x34 (y z w : ℂ) :
    q0129 y z w*r0005 y z w +
    q0424 y z w*v0110 y z w +
    q0523 y z w*v0011 y z w=0 := by
  have h : (merge (merge (product q0129Data r0005Data) (product q0424Data v0110Data)) (product q0523Data v0011Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0129, q0424, q0523, r0005, v0011, v0110] using he

#print axioms row1_x34

compact_certificate theorem row2_x00 (y z w : ℂ) :
    q0000 y z w*r0200 y z w +
    q0100 y z w*r0100 y z w +
    q0400 y z w*v0200 y z w +
    q0500 y z w*v0100 y z w +
    q0600 y z w*v0000 y z w=0 := by
  have h : (merge (merge (merge (merge (product q0000Data r0200Data) (product q0100Data r0100Data)) (product q0400Data v0200Data)) (product q0500Data v0100Data)) (product q0600Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0201Data) (product q0001Data r0200Data)) (product q0100Data r0101Data)) (product q0101Data r0100Data)) (product q0201Data r0000Data)) (product q0400Data v0201Data)) (product q0401Data v0200Data)) (product q0500Data v0101Data)) (product q0501Data v0100Data)) (product q0600Data v0001Data)) (product q0601Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0202Data) (product q0001Data r0201Data)) (product q0002Data r0200Data)) (product q0100Data r0102Data)) (product q0101Data r0101Data)) (product q0102Data r0100Data)) (product q0201Data r0001Data)) (product q0202Data r0000Data)) (product q0400Data v0202Data)) (product q0401Data v0201Data)) (product q0402Data v0200Data)) (product q0500Data v0102Data)) (product q0501Data v0101Data)) (product q0502Data v0100Data)) (product q0600Data v0002Data)) (product q0601Data v0001Data)) (product q0602Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0001Data r0202Data) (product q0002Data r0201Data)) (product q0003Data r0200Data)) (product q0100Data r0103Data)) (product q0101Data r0102Data)) (product q0102Data r0101Data)) (product q0103Data r0100Data)) (product q0201Data r0002Data)) (product q0202Data r0001Data)) (product q0203Data r0000Data)) (product q0400Data v0203Data)) (product q0401Data v0202Data)) (product q0402Data v0201Data)) (product q0403Data v0200Data)) (product q0500Data v0103Data)) (product q0501Data v0102Data)) (product q0502Data v0101Data)) (product q0503Data v0100Data)) (product q0600Data v0003Data)) (product q0601Data v0002Data)) (product q0602Data v0001Data)) (product q0603Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0002Data r0202Data) (product q0003Data r0201Data)) (product q0004Data r0200Data)) (product q0101Data r0103Data)) (product q0102Data r0102Data)) (product q0103Data r0101Data)) (product q0104Data r0100Data)) (product q0201Data r0003Data)) (product q0202Data r0002Data)) (product q0203Data r0001Data)) (product q0204Data r0000Data)) (product q0400Data v0204Data)) (product q0401Data v0203Data)) (product q0402Data v0202Data)) (product q0403Data v0201Data)) (product q0404Data v0200Data)) (product q0500Data v0104Data)) (product q0501Data v0103Data)) (product q0502Data v0102Data)) (product q0503Data v0101Data)) (product q0504Data v0100Data)) (product q0600Data v0004Data)) (product q0601Data v0003Data)) (product q0602Data v0002Data)) (product q0603Data v0001Data)) (product q0604Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0003Data r0202Data) (product q0004Data r0201Data)) (product q0005Data r0200Data)) (product q0102Data r0103Data)) (product q0103Data r0102Data)) (product q0104Data r0101Data)) (product q0105Data r0100Data)) (product q0202Data r0003Data)) (product q0203Data r0002Data)) (product q0204Data r0001Data)) (product q0205Data r0000Data)) (product q0400Data v0205Data)) (product q0401Data v0204Data)) (product q0402Data v0203Data)) (product q0403Data v0202Data)) (product q0404Data v0201Data)) (product q0405Data v0200Data)) (product q0500Data v0105Data)) (product q0501Data v0104Data)) (product q0502Data v0103Data)) (product q0503Data v0102Data)) (product q0504Data v0101Data)) (product q0505Data v0100Data)) (product q0600Data v0005Data)) (product q0601Data v0004Data)) (product q0602Data v0003Data)) (product q0603Data v0002Data)) (product q0604Data v0001Data)) (product q0605Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0004Data r0202Data) (product q0005Data r0201Data)) (product q0006Data r0200Data)) (product q0103Data r0103Data)) (product q0104Data r0102Data)) (product q0105Data r0101Data)) (product q0106Data r0100Data)) (product q0201Data r0005Data)) (product q0203Data r0003Data)) (product q0204Data r0002Data)) (product q0205Data r0001Data)) (product q0206Data r0000Data)) (product q0400Data v0206Data)) (product q0401Data v0205Data)) (product q0402Data v0204Data)) (product q0403Data v0203Data)) (product q0404Data v0202Data)) (product q0405Data v0201Data)) (product q0406Data v0200Data)) (product q0500Data v0106Data)) (product q0501Data v0105Data)) (product q0502Data v0104Data)) (product q0503Data v0103Data)) (product q0504Data v0102Data)) (product q0505Data v0101Data)) (product q0506Data v0100Data)) (product q0600Data v0006Data)) (product q0601Data v0005Data)) (product q0602Data v0004Data)) (product q0603Data v0003Data)) (product q0604Data v0002Data)) (product q0605Data v0001Data)) (product q0606Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0005Data r0202Data) (product q0006Data r0201Data)) (product q0007Data r0200Data)) (product q0104Data r0103Data)) (product q0105Data r0102Data)) (product q0106Data r0101Data)) (product q0107Data r0100Data)) (product q0202Data r0005Data)) (product q0204Data r0003Data)) (product q0205Data r0002Data)) (product q0206Data r0001Data)) (product q0207Data r0000Data)) (product q0400Data v0207Data)) (product q0401Data v0206Data)) (product q0402Data v0205Data)) (product q0403Data v0204Data)) (product q0404Data v0203Data)) (product q0405Data v0202Data)) (product q0406Data v0201Data)) (product q0407Data v0200Data)) (product q0500Data v0107Data)) (product q0501Data v0106Data)) (product q0502Data v0105Data)) (product q0503Data v0104Data)) (product q0504Data v0103Data)) (product q0505Data v0102Data)) (product q0506Data v0101Data)) (product q0507Data v0100Data)) (product q0600Data v0007Data)) (product q0601Data v0006Data)) (product q0602Data v0005Data)) (product q0603Data v0004Data)) (product q0604Data v0003Data)) (product q0605Data v0002Data)) (product q0606Data v0001Data)) (product q0607Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0006Data r0202Data) (product q0007Data r0201Data)) (product q0008Data r0200Data)) (product q0105Data r0103Data)) (product q0106Data r0102Data)) (product q0107Data r0101Data)) (product q0108Data r0100Data)) (product q0203Data r0005Data)) (product q0205Data r0003Data)) (product q0206Data r0002Data)) (product q0207Data r0001Data)) (product q0208Data r0000Data)) (product q0400Data v0208Data)) (product q0401Data v0207Data)) (product q0402Data v0206Data)) (product q0403Data v0205Data)) (product q0404Data v0204Data)) (product q0405Data v0203Data)) (product q0406Data v0202Data)) (product q0407Data v0201Data)) (product q0408Data v0200Data)) (product q0500Data v0108Data)) (product q0501Data v0107Data)) (product q0502Data v0106Data)) (product q0503Data v0105Data)) (product q0504Data v0104Data)) (product q0505Data v0103Data)) (product q0506Data v0102Data)) (product q0507Data v0101Data)) (product q0508Data v0100Data)) (product q0600Data v0008Data)) (product q0601Data v0007Data)) (product q0602Data v0006Data)) (product q0603Data v0005Data)) (product q0604Data v0004Data)) (product q0605Data v0003Data)) (product q0606Data v0002Data)) (product q0607Data v0001Data)) (product q0608Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0007Data r0202Data) (product q0008Data r0201Data)) (product q0009Data r0200Data)) (product q0106Data r0103Data)) (product q0107Data r0102Data)) (product q0108Data r0101Data)) (product q0109Data r0100Data)) (product q0204Data r0005Data)) (product q0206Data r0003Data)) (product q0207Data r0002Data)) (product q0208Data r0001Data)) (product q0209Data r0000Data)) (product q0401Data v0208Data)) (product q0402Data v0207Data)) (product q0403Data v0206Data)) (product q0404Data v0205Data)) (product q0405Data v0204Data)) (product q0406Data v0203Data)) (product q0407Data v0202Data)) (product q0408Data v0201Data)) (product q0409Data v0200Data)) (product q0500Data v0109Data)) (product q0501Data v0108Data)) (product q0502Data v0107Data)) (product q0503Data v0106Data)) (product q0504Data v0105Data)) (product q0505Data v0104Data)) (product q0506Data v0103Data)) (product q0507Data v0102Data)) (product q0508Data v0101Data)) (product q0509Data v0100Data)) (product q0600Data v0009Data)) (product q0601Data v0008Data)) (product q0602Data v0007Data)) (product q0603Data v0006Data)) (product q0604Data v0005Data)) (product q0605Data v0004Data)) (product q0606Data v0003Data)) (product q0607Data v0002Data)) (product q0608Data v0001Data)) (product q0609Data v0000Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0007, q0008, q0009, q0106, q0107, q0108, q0109, q0204, q0206, q0207, q0208, q0209, q0401, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he

#print axioms row2_x09

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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0009Data r0202Data) (product q0010Data r0201Data)) (product q0011Data r0200Data)) (product q0108Data r0103Data)) (product q0109Data r0102Data)) (product q0110Data r0101Data)) (product q0111Data r0100Data)) (product q0206Data r0005Data)) (product q0208Data r0003Data)) (product q0209Data r0002Data)) (product q0210Data r0001Data)) (product q0211Data r0000Data)) (product q0403Data v0208Data)) (product q0404Data v0207Data)) (product q0405Data v0206Data)) (product q0406Data v0205Data)) (product q0407Data v0204Data)) (product q0408Data v0203Data)) (product q0409Data v0202Data)) (product q0410Data v0201Data)) (product q0411Data v0200Data)) (product q0501Data v0110Data)) (product q0502Data v0109Data)) (product q0503Data v0108Data)) (product q0504Data v0107Data)) (product q0505Data v0106Data)) (product q0506Data v0105Data)) (product q0507Data v0104Data)) (product q0508Data v0103Data)) (product q0509Data v0102Data)) (product q0510Data v0101Data)) (product q0511Data v0100Data)) (product q0600Data v0011Data)) (product q0601Data v0010Data)) (product q0602Data v0009Data)) (product q0603Data v0008Data)) (product q0604Data v0007Data)) (product q0605Data v0006Data)) (product q0606Data v0005Data)) (product q0607Data v0004Data)) (product q0608Data v0003Data)) (product q0609Data v0002Data)) (product q0610Data v0001Data)) (product q0611Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0010Data r0202Data) (product q0011Data r0201Data)) (product q0012Data r0200Data)) (product q0109Data r0103Data)) (product q0110Data r0102Data)) (product q0111Data r0101Data)) (product q0112Data r0100Data)) (product q0207Data r0005Data)) (product q0209Data r0003Data)) (product q0210Data r0002Data)) (product q0211Data r0001Data)) (product q0212Data r0000Data)) (product q0404Data v0208Data)) (product q0405Data v0207Data)) (product q0406Data v0206Data)) (product q0407Data v0205Data)) (product q0408Data v0204Data)) (product q0409Data v0203Data)) (product q0410Data v0202Data)) (product q0411Data v0201Data)) (product q0412Data v0200Data)) (product q0502Data v0110Data)) (product q0503Data v0109Data)) (product q0504Data v0108Data)) (product q0505Data v0107Data)) (product q0506Data v0106Data)) (product q0507Data v0105Data)) (product q0508Data v0104Data)) (product q0509Data v0103Data)) (product q0510Data v0102Data)) (product q0511Data v0101Data)) (product q0512Data v0100Data)) (product q0601Data v0011Data)) (product q0602Data v0010Data)) (product q0603Data v0009Data)) (product q0604Data v0008Data)) (product q0605Data v0007Data)) (product q0606Data v0006Data)) (product q0607Data v0005Data)) (product q0608Data v0004Data)) (product q0609Data v0003Data)) (product q0610Data v0002Data)) (product q0611Data v0001Data)) (product q0612Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0011Data r0202Data) (product q0012Data r0201Data)) (product q0013Data r0200Data)) (product q0110Data r0103Data)) (product q0111Data r0102Data)) (product q0112Data r0101Data)) (product q0113Data r0100Data)) (product q0208Data r0005Data)) (product q0210Data r0003Data)) (product q0211Data r0002Data)) (product q0212Data r0001Data)) (product q0213Data r0000Data)) (product q0405Data v0208Data)) (product q0406Data v0207Data)) (product q0407Data v0206Data)) (product q0408Data v0205Data)) (product q0409Data v0204Data)) (product q0410Data v0203Data)) (product q0411Data v0202Data)) (product q0412Data v0201Data)) (product q0413Data v0200Data)) (product q0503Data v0110Data)) (product q0504Data v0109Data)) (product q0505Data v0108Data)) (product q0506Data v0107Data)) (product q0507Data v0106Data)) (product q0508Data v0105Data)) (product q0509Data v0104Data)) (product q0510Data v0103Data)) (product q0511Data v0102Data)) (product q0512Data v0101Data)) (product q0513Data v0100Data)) (product q0602Data v0011Data)) (product q0603Data v0010Data)) (product q0604Data v0009Data)) (product q0605Data v0008Data)) (product q0606Data v0007Data)) (product q0607Data v0006Data)) (product q0608Data v0005Data)) (product q0609Data v0004Data)) (product q0610Data v0003Data)) (product q0611Data v0002Data)) (product q0612Data v0001Data)) (product q0613Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0012Data r0202Data) (product q0013Data r0201Data)) (product q0014Data r0200Data)) (product q0111Data r0103Data)) (product q0112Data r0102Data)) (product q0113Data r0101Data)) (product q0114Data r0100Data)) (product q0209Data r0005Data)) (product q0211Data r0003Data)) (product q0212Data r0002Data)) (product q0213Data r0001Data)) (product q0214Data r0000Data)) (product q0406Data v0208Data)) (product q0407Data v0207Data)) (product q0408Data v0206Data)) (product q0409Data v0205Data)) (product q0410Data v0204Data)) (product q0411Data v0203Data)) (product q0412Data v0202Data)) (product q0413Data v0201Data)) (product q0414Data v0200Data)) (product q0504Data v0110Data)) (product q0505Data v0109Data)) (product q0506Data v0108Data)) (product q0507Data v0107Data)) (product q0508Data v0106Data)) (product q0509Data v0105Data)) (product q0510Data v0104Data)) (product q0511Data v0103Data)) (product q0512Data v0102Data)) (product q0513Data v0101Data)) (product q0514Data v0100Data)) (product q0603Data v0011Data)) (product q0604Data v0010Data)) (product q0605Data v0009Data)) (product q0606Data v0008Data)) (product q0607Data v0007Data)) (product q0608Data v0006Data)) (product q0609Data v0005Data)) (product q0610Data v0004Data)) (product q0611Data v0003Data)) (product q0612Data v0002Data)) (product q0613Data v0001Data)) (product q0614Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0013Data r0202Data) (product q0014Data r0201Data)) (product q0015Data r0200Data)) (product q0112Data r0103Data)) (product q0113Data r0102Data)) (product q0114Data r0101Data)) (product q0115Data r0100Data)) (product q0210Data r0005Data)) (product q0212Data r0003Data)) (product q0213Data r0002Data)) (product q0214Data r0001Data)) (product q0215Data r0000Data)) (product q0407Data v0208Data)) (product q0408Data v0207Data)) (product q0409Data v0206Data)) (product q0410Data v0205Data)) (product q0411Data v0204Data)) (product q0412Data v0203Data)) (product q0413Data v0202Data)) (product q0414Data v0201Data)) (product q0415Data v0200Data)) (product q0505Data v0110Data)) (product q0506Data v0109Data)) (product q0507Data v0108Data)) (product q0508Data v0107Data)) (product q0509Data v0106Data)) (product q0510Data v0105Data)) (product q0511Data v0104Data)) (product q0512Data v0103Data)) (product q0513Data v0102Data)) (product q0514Data v0101Data)) (product q0515Data v0100Data)) (product q0604Data v0011Data)) (product q0605Data v0010Data)) (product q0606Data v0009Data)) (product q0607Data v0008Data)) (product q0608Data v0007Data)) (product q0609Data v0006Data)) (product q0610Data v0005Data)) (product q0611Data v0004Data)) (product q0612Data v0003Data)) (product q0613Data v0002Data)) (product q0614Data v0001Data)) (product q0615Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0014Data r0202Data) (product q0015Data r0201Data)) (product q0016Data r0200Data)) (product q0113Data r0103Data)) (product q0114Data r0102Data)) (product q0115Data r0101Data)) (product q0116Data r0100Data)) (product q0211Data r0005Data)) (product q0213Data r0003Data)) (product q0214Data r0002Data)) (product q0215Data r0001Data)) (product q0216Data r0000Data)) (product q0408Data v0208Data)) (product q0409Data v0207Data)) (product q0410Data v0206Data)) (product q0411Data v0205Data)) (product q0412Data v0204Data)) (product q0413Data v0203Data)) (product q0414Data v0202Data)) (product q0415Data v0201Data)) (product q0416Data v0200Data)) (product q0506Data v0110Data)) (product q0507Data v0109Data)) (product q0508Data v0108Data)) (product q0509Data v0107Data)) (product q0510Data v0106Data)) (product q0511Data v0105Data)) (product q0512Data v0104Data)) (product q0513Data v0103Data)) (product q0514Data v0102Data)) (product q0515Data v0101Data)) (product q0516Data v0100Data)) (product q0605Data v0011Data)) (product q0606Data v0010Data)) (product q0607Data v0009Data)) (product q0608Data v0008Data)) (product q0609Data v0007Data)) (product q0610Data v0006Data)) (product q0611Data v0005Data)) (product q0612Data v0004Data)) (product q0613Data v0003Data)) (product q0614Data v0002Data)) (product q0615Data v0001Data)) (product q0616Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0015Data r0202Data) (product q0016Data r0201Data)) (product q0017Data r0200Data)) (product q0114Data r0103Data)) (product q0115Data r0102Data)) (product q0116Data r0101Data)) (product q0117Data r0100Data)) (product q0212Data r0005Data)) (product q0214Data r0003Data)) (product q0215Data r0002Data)) (product q0216Data r0001Data)) (product q0217Data r0000Data)) (product q0409Data v0208Data)) (product q0410Data v0207Data)) (product q0411Data v0206Data)) (product q0412Data v0205Data)) (product q0413Data v0204Data)) (product q0414Data v0203Data)) (product q0415Data v0202Data)) (product q0416Data v0201Data)) (product q0417Data v0200Data)) (product q0507Data v0110Data)) (product q0508Data v0109Data)) (product q0509Data v0108Data)) (product q0510Data v0107Data)) (product q0511Data v0106Data)) (product q0512Data v0105Data)) (product q0513Data v0104Data)) (product q0514Data v0103Data)) (product q0515Data v0102Data)) (product q0516Data v0101Data)) (product q0517Data v0100Data)) (product q0606Data v0011Data)) (product q0607Data v0010Data)) (product q0608Data v0009Data)) (product q0609Data v0008Data)) (product q0610Data v0007Data)) (product q0611Data v0006Data)) (product q0612Data v0005Data)) (product q0613Data v0004Data)) (product q0614Data v0003Data)) (product q0615Data v0002Data)) (product q0616Data v0001Data)) (product q0617Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0016Data r0202Data) (product q0017Data r0201Data)) (product q0018Data r0200Data)) (product q0115Data r0103Data)) (product q0116Data r0102Data)) (product q0117Data r0101Data)) (product q0118Data r0100Data)) (product q0213Data r0005Data)) (product q0215Data r0003Data)) (product q0216Data r0002Data)) (product q0217Data r0001Data)) (product q0218Data r0000Data)) (product q0410Data v0208Data)) (product q0411Data v0207Data)) (product q0412Data v0206Data)) (product q0413Data v0205Data)) (product q0414Data v0204Data)) (product q0415Data v0203Data)) (product q0416Data v0202Data)) (product q0417Data v0201Data)) (product q0418Data v0200Data)) (product q0508Data v0110Data)) (product q0509Data v0109Data)) (product q0510Data v0108Data)) (product q0511Data v0107Data)) (product q0512Data v0106Data)) (product q0513Data v0105Data)) (product q0514Data v0104Data)) (product q0515Data v0103Data)) (product q0516Data v0102Data)) (product q0517Data v0101Data)) (product q0518Data v0100Data)) (product q0607Data v0011Data)) (product q0608Data v0010Data)) (product q0609Data v0009Data)) (product q0610Data v0008Data)) (product q0611Data v0007Data)) (product q0612Data v0006Data)) (product q0613Data v0005Data)) (product q0614Data v0004Data)) (product q0615Data v0003Data)) (product q0616Data v0002Data)) (product q0617Data v0001Data)) (product q0618Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0017Data r0202Data) (product q0018Data r0201Data)) (product q0019Data r0200Data)) (product q0116Data r0103Data)) (product q0117Data r0102Data)) (product q0118Data r0101Data)) (product q0119Data r0100Data)) (product q0214Data r0005Data)) (product q0216Data r0003Data)) (product q0217Data r0002Data)) (product q0218Data r0001Data)) (product q0219Data r0000Data)) (product q0411Data v0208Data)) (product q0412Data v0207Data)) (product q0413Data v0206Data)) (product q0414Data v0205Data)) (product q0415Data v0204Data)) (product q0416Data v0203Data)) (product q0417Data v0202Data)) (product q0418Data v0201Data)) (product q0419Data v0200Data)) (product q0509Data v0110Data)) (product q0510Data v0109Data)) (product q0511Data v0108Data)) (product q0512Data v0107Data)) (product q0513Data v0106Data)) (product q0514Data v0105Data)) (product q0515Data v0104Data)) (product q0516Data v0103Data)) (product q0517Data v0102Data)) (product q0518Data v0101Data)) (product q0519Data v0100Data)) (product q0608Data v0011Data)) (product q0609Data v0010Data)) (product q0610Data v0009Data)) (product q0611Data v0008Data)) (product q0612Data v0007Data)) (product q0613Data v0006Data)) (product q0614Data v0005Data)) (product q0615Data v0004Data)) (product q0616Data v0003Data)) (product q0617Data v0002Data)) (product q0618Data v0001Data)) (product q0619Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0018Data r0202Data) (product q0019Data r0201Data)) (product q0020Data r0200Data)) (product q0117Data r0103Data)) (product q0118Data r0102Data)) (product q0119Data r0101Data)) (product q0120Data r0100Data)) (product q0215Data r0005Data)) (product q0217Data r0003Data)) (product q0218Data r0002Data)) (product q0219Data r0001Data)) (product q0220Data r0000Data)) (product q0412Data v0208Data)) (product q0413Data v0207Data)) (product q0414Data v0206Data)) (product q0415Data v0205Data)) (product q0416Data v0204Data)) (product q0417Data v0203Data)) (product q0418Data v0202Data)) (product q0419Data v0201Data)) (product q0420Data v0200Data)) (product q0510Data v0110Data)) (product q0511Data v0109Data)) (product q0512Data v0108Data)) (product q0513Data v0107Data)) (product q0514Data v0106Data)) (product q0515Data v0105Data)) (product q0516Data v0104Data)) (product q0517Data v0103Data)) (product q0518Data v0102Data)) (product q0519Data v0101Data)) (product q0520Data v0100Data)) (product q0609Data v0011Data)) (product q0610Data v0010Data)) (product q0611Data v0009Data)) (product q0612Data v0008Data)) (product q0613Data v0007Data)) (product q0614Data v0006Data)) (product q0615Data v0005Data)) (product q0616Data v0004Data)) (product q0617Data v0003Data)) (product q0618Data v0002Data)) (product q0619Data v0001Data)) (product q0620Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0019Data r0202Data) (product q0020Data r0201Data)) (product q0021Data r0200Data)) (product q0118Data r0103Data)) (product q0119Data r0102Data)) (product q0120Data r0101Data)) (product q0121Data r0100Data)) (product q0216Data r0005Data)) (product q0218Data r0003Data)) (product q0219Data r0002Data)) (product q0220Data r0001Data)) (product q0221Data r0000Data)) (product q0413Data v0208Data)) (product q0414Data v0207Data)) (product q0415Data v0206Data)) (product q0416Data v0205Data)) (product q0417Data v0204Data)) (product q0418Data v0203Data)) (product q0419Data v0202Data)) (product q0420Data v0201Data)) (product q0421Data v0200Data)) (product q0511Data v0110Data)) (product q0512Data v0109Data)) (product q0513Data v0108Data)) (product q0514Data v0107Data)) (product q0515Data v0106Data)) (product q0516Data v0105Data)) (product q0517Data v0104Data)) (product q0518Data v0103Data)) (product q0519Data v0102Data)) (product q0520Data v0101Data)) (product q0521Data v0100Data)) (product q0610Data v0011Data)) (product q0611Data v0010Data)) (product q0612Data v0009Data)) (product q0613Data v0008Data)) (product q0614Data v0007Data)) (product q0615Data v0006Data)) (product q0616Data v0005Data)) (product q0617Data v0004Data)) (product q0618Data v0003Data)) (product q0619Data v0002Data)) (product q0620Data v0001Data)) (product q0621Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0020Data r0202Data) (product q0021Data r0201Data)) (product q0022Data r0200Data)) (product q0119Data r0103Data)) (product q0120Data r0102Data)) (product q0121Data r0101Data)) (product q0122Data r0100Data)) (product q0217Data r0005Data)) (product q0219Data r0003Data)) (product q0220Data r0002Data)) (product q0221Data r0001Data)) (product q0222Data r0000Data)) (product q0414Data v0208Data)) (product q0415Data v0207Data)) (product q0416Data v0206Data)) (product q0417Data v0205Data)) (product q0418Data v0204Data)) (product q0419Data v0203Data)) (product q0420Data v0202Data)) (product q0421Data v0201Data)) (product q0422Data v0200Data)) (product q0512Data v0110Data)) (product q0513Data v0109Data)) (product q0514Data v0108Data)) (product q0515Data v0107Data)) (product q0516Data v0106Data)) (product q0517Data v0105Data)) (product q0518Data v0104Data)) (product q0519Data v0103Data)) (product q0520Data v0102Data)) (product q0521Data v0101Data)) (product q0522Data v0100Data)) (product q0611Data v0011Data)) (product q0612Data v0010Data)) (product q0613Data v0009Data)) (product q0614Data v0008Data)) (product q0615Data v0007Data)) (product q0616Data v0006Data)) (product q0617Data v0005Data)) (product q0618Data v0004Data)) (product q0619Data v0003Data)) (product q0620Data v0002Data)) (product q0621Data v0001Data)) (product q0622Data v0000Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0021Data r0202Data) (product q0022Data r0201Data)) (product q0023Data r0200Data)) (product q0120Data r0103Data)) (product q0121Data r0102Data)) (product q0122Data r0101Data)) (product q0123Data r0100Data)) (product q0218Data r0005Data)) (product q0220Data r0003Data)) (product q0221Data r0002Data)) (product q0222Data r0001Data)) (product q0223Data r0000Data)) (product q0415Data v0208Data)) (product q0416Data v0207Data)) (product q0417Data v0206Data)) (product q0418Data v0205Data)) (product q0419Data v0204Data)) (product q0420Data v0203Data)) (product q0421Data v0202Data)) (product q0422Data v0201Data)) (product q0423Data v0200Data)) (product q0513Data v0110Data)) (product q0514Data v0109Data)) (product q0515Data v0108Data)) (product q0516Data v0107Data)) (product q0517Data v0106Data)) (product q0518Data v0105Data)) (product q0519Data v0104Data)) (product q0520Data v0103Data)) (product q0521Data v0102Data)) (product q0522Data v0101Data)) (product q0523Data v0100Data)) (product q0612Data v0011Data)) (product q0613Data v0010Data)) (product q0614Data v0009Data)) (product q0615Data v0008Data)) (product q0616Data v0007Data)) (product q0617Data v0006Data)) (product q0618Data v0005Data)) (product q0619Data v0004Data)) (product q0620Data v0003Data)) (product q0621Data v0002Data)) (product q0622Data v0001Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0022Data r0202Data) (product q0023Data r0201Data)) (product q0024Data r0200Data)) (product q0121Data r0103Data)) (product q0122Data r0102Data)) (product q0123Data r0101Data)) (product q0124Data r0100Data)) (product q0219Data r0005Data)) (product q0221Data r0003Data)) (product q0222Data r0002Data)) (product q0223Data r0001Data)) (product q0224Data r0000Data)) (product q0416Data v0208Data)) (product q0417Data v0207Data)) (product q0418Data v0206Data)) (product q0419Data v0205Data)) (product q0420Data v0204Data)) (product q0421Data v0203Data)) (product q0422Data v0202Data)) (product q0423Data v0201Data)) (product q0424Data v0200Data)) (product q0514Data v0110Data)) (product q0515Data v0109Data)) (product q0516Data v0108Data)) (product q0517Data v0107Data)) (product q0518Data v0106Data)) (product q0519Data v0105Data)) (product q0520Data v0104Data)) (product q0521Data v0103Data)) (product q0522Data v0102Data)) (product q0523Data v0101Data)) (product q0613Data v0011Data)) (product q0614Data v0010Data)) (product q0615Data v0009Data)) (product q0616Data v0008Data)) (product q0617Data v0007Data)) (product q0618Data v0006Data)) (product q0619Data v0005Data)) (product q0620Data v0004Data)) (product q0621Data v0003Data)) (product q0622Data v0002Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0023Data r0202Data) (product q0024Data r0201Data)) (product q0025Data r0200Data)) (product q0122Data r0103Data)) (product q0123Data r0102Data)) (product q0124Data r0101Data)) (product q0125Data r0100Data)) (product q0220Data r0005Data)) (product q0222Data r0003Data)) (product q0223Data r0002Data)) (product q0224Data r0001Data)) (product q0225Data r0000Data)) (product q0417Data v0208Data)) (product q0418Data v0207Data)) (product q0419Data v0206Data)) (product q0420Data v0205Data)) (product q0421Data v0204Data)) (product q0422Data v0203Data)) (product q0423Data v0202Data)) (product q0424Data v0201Data)) (product q0515Data v0110Data)) (product q0516Data v0109Data)) (product q0517Data v0108Data)) (product q0518Data v0107Data)) (product q0519Data v0106Data)) (product q0520Data v0105Data)) (product q0521Data v0104Data)) (product q0522Data v0103Data)) (product q0523Data v0102Data)) (product q0614Data v0011Data)) (product q0615Data v0010Data)) (product q0616Data v0009Data)) (product q0617Data v0008Data)) (product q0618Data v0007Data)) (product q0619Data v0006Data)) (product q0620Data v0005Data)) (product q0621Data v0004Data)) (product q0622Data v0003Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0024Data r0202Data) (product q0025Data r0201Data)) (product q0026Data r0200Data)) (product q0123Data r0103Data)) (product q0124Data r0102Data)) (product q0125Data r0101Data)) (product q0126Data r0100Data)) (product q0221Data r0005Data)) (product q0223Data r0003Data)) (product q0224Data r0002Data)) (product q0225Data r0001Data)) (product q0226Data r0000Data)) (product q0418Data v0208Data)) (product q0419Data v0207Data)) (product q0420Data v0206Data)) (product q0421Data v0205Data)) (product q0422Data v0204Data)) (product q0423Data v0203Data)) (product q0424Data v0202Data)) (product q0516Data v0110Data)) (product q0517Data v0109Data)) (product q0518Data v0108Data)) (product q0519Data v0107Data)) (product q0520Data v0106Data)) (product q0521Data v0105Data)) (product q0522Data v0104Data)) (product q0523Data v0103Data)) (product q0615Data v0011Data)) (product q0616Data v0010Data)) (product q0617Data v0009Data)) (product q0618Data v0008Data)) (product q0619Data v0007Data)) (product q0620Data v0006Data)) (product q0621Data v0005Data)) (product q0622Data v0004Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0025Data r0202Data) (product q0026Data r0201Data)) (product q0027Data r0200Data)) (product q0124Data r0103Data)) (product q0125Data r0102Data)) (product q0126Data r0101Data)) (product q0127Data r0100Data)) (product q0222Data r0005Data)) (product q0224Data r0003Data)) (product q0225Data r0002Data)) (product q0226Data r0001Data)) (product q0227Data r0000Data)) (product q0419Data v0208Data)) (product q0420Data v0207Data)) (product q0421Data v0206Data)) (product q0422Data v0205Data)) (product q0423Data v0204Data)) (product q0424Data v0203Data)) (product q0517Data v0110Data)) (product q0518Data v0109Data)) (product q0519Data v0108Data)) (product q0520Data v0107Data)) (product q0521Data v0106Data)) (product q0522Data v0105Data)) (product q0523Data v0104Data)) (product q0616Data v0011Data)) (product q0617Data v0010Data)) (product q0618Data v0009Data)) (product q0619Data v0008Data)) (product q0620Data v0007Data)) (product q0621Data v0006Data)) (product q0622Data v0005Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0026Data r0202Data) (product q0027Data r0201Data)) (product q0028Data r0200Data)) (product q0125Data r0103Data)) (product q0126Data r0102Data)) (product q0127Data r0101Data)) (product q0128Data r0100Data)) (product q0223Data r0005Data)) (product q0225Data r0003Data)) (product q0226Data r0002Data)) (product q0227Data r0001Data)) (product q0228Data r0000Data)) (product q0420Data v0208Data)) (product q0421Data v0207Data)) (product q0422Data v0206Data)) (product q0423Data v0205Data)) (product q0424Data v0204Data)) (product q0518Data v0110Data)) (product q0519Data v0109Data)) (product q0520Data v0108Data)) (product q0521Data v0107Data)) (product q0522Data v0106Data)) (product q0523Data v0105Data)) (product q0617Data v0011Data)) (product q0618Data v0010Data)) (product q0619Data v0009Data)) (product q0620Data v0008Data)) (product q0621Data v0007Data)) (product q0622Data v0006Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0027Data r0202Data) (product q0028Data r0201Data)) (product q0029Data r0200Data)) (product q0126Data r0103Data)) (product q0127Data r0102Data)) (product q0128Data r0101Data)) (product q0129Data r0100Data)) (product q0224Data r0005Data)) (product q0226Data r0003Data)) (product q0227Data r0002Data)) (product q0228Data r0001Data)) (product q0421Data v0208Data)) (product q0422Data v0207Data)) (product q0423Data v0206Data)) (product q0424Data v0205Data)) (product q0519Data v0110Data)) (product q0520Data v0109Data)) (product q0521Data v0108Data)) (product q0522Data v0107Data)) (product q0523Data v0106Data)) (product q0618Data v0011Data)) (product q0619Data v0010Data)) (product q0620Data v0009Data)) (product q0621Data v0008Data)) (product q0622Data v0007Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0028Data r0202Data) (product q0029Data r0201Data)) (product q0030Data r0200Data)) (product q0127Data r0103Data)) (product q0128Data r0102Data)) (product q0129Data r0101Data)) (product q0225Data r0005Data)) (product q0227Data r0003Data)) (product q0228Data r0002Data)) (product q0422Data v0208Data)) (product q0423Data v0207Data)) (product q0424Data v0206Data)) (product q0520Data v0110Data)) (product q0521Data v0109Data)) (product q0522Data v0108Data)) (product q0523Data v0107Data)) (product q0619Data v0011Data)) (product q0620Data v0010Data)) (product q0621Data v0009Data)) (product q0622Data v0008Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0029Data r0202Data) (product q0030Data r0201Data)) (product q0128Data r0103Data)) (product q0129Data r0102Data)) (product q0226Data r0005Data)) (product q0228Data r0003Data)) (product q0423Data v0208Data)) (product q0424Data v0207Data)) (product q0521Data v0110Data)) (product q0522Data v0109Data)) (product q0523Data v0108Data)) (product q0620Data v0011Data)) (product q0621Data v0010Data)) (product q0622Data v0009Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0030Data r0202Data) (product q0129Data r0103Data)) (product q0227Data r0005Data)) (product q0424Data v0208Data)) (product q0522Data v0110Data)) (product q0523Data v0109Data)) (product q0621Data v0011Data)) (product q0622Data v0010Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0030, q0129, q0227, q0424, q0522, q0523, q0621, q0622, r0005, r0103, r0202, v0010, v0011, v0109, v0110, v0208] using he

#print axioms row2_x32

compact_certificate theorem row2_x33 (y z w : ℂ) :
    q0228 y z w*r0005 y z w +
    q0523 y z w*v0110 y z w +
    q0622 y z w*v0011 y z w=0 := by
  have h : (merge (merge (product q0228Data r0005Data) (product q0523Data v0110Data)) (product q0622Data v0011Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0228, q0523, q0622, r0005, v0011, v0110] using he

#print axioms row2_x33

compact_certificate theorem row3_x00 (y z w : ℂ) :
    q0000 y z w*r0300 y z w +
    q0100 y z w*r0200 y z w +
    q0500 y z w*v0200 y z w +
    q0600 y z w*v0100 y z w=0 := by
  have h : (merge (merge (merge (product q0000Data r0300Data) (product q0100Data r0200Data)) (product q0500Data v0200Data)) (product q0600Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0000Data r0301Data) (product q0001Data r0300Data)) (product q0100Data r0201Data)) (product q0101Data r0200Data)) (product q0201Data r0100Data)) (product q0301Data r0000Data)) (product q0400Data v0301Data)) (product q0500Data v0201Data)) (product q0501Data v0200Data)) (product q0600Data v0101Data)) (product q0601Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0001Data r0301Data) (product q0002Data r0300Data)) (product q0100Data r0202Data)) (product q0101Data r0201Data)) (product q0102Data r0200Data)) (product q0201Data r0101Data)) (product q0202Data r0100Data)) (product q0301Data r0001Data)) (product q0302Data r0000Data)) (product q0400Data v0302Data)) (product q0401Data v0301Data)) (product q0500Data v0202Data)) (product q0501Data v0201Data)) (product q0502Data v0200Data)) (product q0600Data v0102Data)) (product q0601Data v0101Data)) (product q0602Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0002Data r0301Data) (product q0003Data r0300Data)) (product q0101Data r0202Data)) (product q0102Data r0201Data)) (product q0103Data r0200Data)) (product q0201Data r0102Data)) (product q0202Data r0101Data)) (product q0203Data r0100Data)) (product q0301Data r0002Data)) (product q0302Data r0001Data)) (product q0303Data r0000Data)) (product q0400Data v0303Data)) (product q0401Data v0302Data)) (product q0402Data v0301Data)) (product q0500Data v0203Data)) (product q0501Data v0202Data)) (product q0502Data v0201Data)) (product q0503Data v0200Data)) (product q0600Data v0103Data)) (product q0601Data v0102Data)) (product q0602Data v0101Data)) (product q0603Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0003Data r0301Data) (product q0004Data r0300Data)) (product q0102Data r0202Data)) (product q0103Data r0201Data)) (product q0104Data r0200Data)) (product q0201Data r0103Data)) (product q0202Data r0102Data)) (product q0203Data r0101Data)) (product q0204Data r0100Data)) (product q0301Data r0003Data)) (product q0302Data r0002Data)) (product q0303Data r0001Data)) (product q0304Data r0000Data)) (product q0400Data v0304Data)) (product q0401Data v0303Data)) (product q0402Data v0302Data)) (product q0403Data v0301Data)) (product q0500Data v0204Data)) (product q0501Data v0203Data)) (product q0502Data v0202Data)) (product q0503Data v0201Data)) (product q0504Data v0200Data)) (product q0600Data v0104Data)) (product q0601Data v0103Data)) (product q0602Data v0102Data)) (product q0603Data v0101Data)) (product q0604Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0004Data r0301Data) (product q0005Data r0300Data)) (product q0103Data r0202Data)) (product q0104Data r0201Data)) (product q0105Data r0200Data)) (product q0202Data r0103Data)) (product q0203Data r0102Data)) (product q0204Data r0101Data)) (product q0205Data r0100Data)) (product q0302Data r0003Data)) (product q0303Data r0002Data)) (product q0304Data r0001Data)) (product q0305Data r0000Data)) (product q0400Data v0305Data)) (product q0401Data v0304Data)) (product q0402Data v0303Data)) (product q0403Data v0302Data)) (product q0404Data v0301Data)) (product q0500Data v0205Data)) (product q0501Data v0204Data)) (product q0502Data v0203Data)) (product q0503Data v0202Data)) (product q0504Data v0201Data)) (product q0505Data v0200Data)) (product q0600Data v0105Data)) (product q0601Data v0104Data)) (product q0602Data v0103Data)) (product q0603Data v0102Data)) (product q0604Data v0101Data)) (product q0605Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0005Data r0301Data) (product q0006Data r0300Data)) (product q0104Data r0202Data)) (product q0105Data r0201Data)) (product q0106Data r0200Data)) (product q0203Data r0103Data)) (product q0204Data r0102Data)) (product q0205Data r0101Data)) (product q0206Data r0100Data)) (product q0301Data r0005Data)) (product q0303Data r0003Data)) (product q0304Data r0002Data)) (product q0305Data r0001Data)) (product q0306Data r0000Data)) (product q0400Data v0306Data)) (product q0401Data v0305Data)) (product q0402Data v0304Data)) (product q0403Data v0303Data)) (product q0404Data v0302Data)) (product q0405Data v0301Data)) (product q0500Data v0206Data)) (product q0501Data v0205Data)) (product q0502Data v0204Data)) (product q0503Data v0203Data)) (product q0504Data v0202Data)) (product q0505Data v0201Data)) (product q0506Data v0200Data)) (product q0600Data v0106Data)) (product q0601Data v0105Data)) (product q0602Data v0104Data)) (product q0603Data v0103Data)) (product q0604Data v0102Data)) (product q0605Data v0101Data)) (product q0606Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0006Data r0301Data) (product q0007Data r0300Data)) (product q0105Data r0202Data)) (product q0106Data r0201Data)) (product q0107Data r0200Data)) (product q0204Data r0103Data)) (product q0205Data r0102Data)) (product q0206Data r0101Data)) (product q0207Data r0100Data)) (product q0302Data r0005Data)) (product q0304Data r0003Data)) (product q0305Data r0002Data)) (product q0306Data r0001Data)) (product q0307Data r0000Data)) (product q0400Data v0307Data)) (product q0401Data v0306Data)) (product q0402Data v0305Data)) (product q0403Data v0304Data)) (product q0404Data v0303Data)) (product q0405Data v0302Data)) (product q0406Data v0301Data)) (product q0500Data v0207Data)) (product q0501Data v0206Data)) (product q0502Data v0205Data)) (product q0503Data v0204Data)) (product q0504Data v0203Data)) (product q0505Data v0202Data)) (product q0506Data v0201Data)) (product q0507Data v0200Data)) (product q0600Data v0107Data)) (product q0601Data v0106Data)) (product q0602Data v0105Data)) (product q0603Data v0104Data)) (product q0604Data v0103Data)) (product q0605Data v0102Data)) (product q0606Data v0101Data)) (product q0607Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0007Data r0301Data) (product q0008Data r0300Data)) (product q0106Data r0202Data)) (product q0107Data r0201Data)) (product q0108Data r0200Data)) (product q0205Data r0103Data)) (product q0206Data r0102Data)) (product q0207Data r0101Data)) (product q0208Data r0100Data)) (product q0303Data r0005Data)) (product q0305Data r0003Data)) (product q0306Data r0002Data)) (product q0307Data r0001Data)) (product q0308Data r0000Data)) (product q0401Data v0307Data)) (product q0402Data v0306Data)) (product q0403Data v0305Data)) (product q0404Data v0304Data)) (product q0405Data v0303Data)) (product q0406Data v0302Data)) (product q0407Data v0301Data)) (product q0500Data v0208Data)) (product q0501Data v0207Data)) (product q0502Data v0206Data)) (product q0503Data v0205Data)) (product q0504Data v0204Data)) (product q0505Data v0203Data)) (product q0506Data v0202Data)) (product q0507Data v0201Data)) (product q0508Data v0200Data)) (product q0600Data v0108Data)) (product q0601Data v0107Data)) (product q0602Data v0106Data)) (product q0603Data v0105Data)) (product q0604Data v0104Data)) (product q0605Data v0103Data)) (product q0606Data v0102Data)) (product q0607Data v0101Data)) (product q0608Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0008Data r0301Data) (product q0009Data r0300Data)) (product q0107Data r0202Data)) (product q0108Data r0201Data)) (product q0109Data r0200Data)) (product q0206Data r0103Data)) (product q0207Data r0102Data)) (product q0208Data r0101Data)) (product q0209Data r0100Data)) (product q0304Data r0005Data)) (product q0306Data r0003Data)) (product q0307Data r0002Data)) (product q0308Data r0001Data)) (product q0309Data r0000Data)) (product q0402Data v0307Data)) (product q0403Data v0306Data)) (product q0404Data v0305Data)) (product q0405Data v0304Data)) (product q0406Data v0303Data)) (product q0407Data v0302Data)) (product q0408Data v0301Data)) (product q0501Data v0208Data)) (product q0502Data v0207Data)) (product q0503Data v0206Data)) (product q0504Data v0205Data)) (product q0505Data v0204Data)) (product q0506Data v0203Data)) (product q0507Data v0202Data)) (product q0508Data v0201Data)) (product q0509Data v0200Data)) (product q0600Data v0109Data)) (product q0601Data v0108Data)) (product q0602Data v0107Data)) (product q0603Data v0106Data)) (product q0604Data v0105Data)) (product q0605Data v0104Data)) (product q0606Data v0103Data)) (product q0607Data v0102Data)) (product q0608Data v0101Data)) (product q0609Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0009Data r0301Data) (product q0010Data r0300Data)) (product q0108Data r0202Data)) (product q0109Data r0201Data)) (product q0110Data r0200Data)) (product q0207Data r0103Data)) (product q0208Data r0102Data)) (product q0209Data r0101Data)) (product q0210Data r0100Data)) (product q0305Data r0005Data)) (product q0307Data r0003Data)) (product q0308Data r0002Data)) (product q0309Data r0001Data)) (product q0310Data r0000Data)) (product q0403Data v0307Data)) (product q0404Data v0306Data)) (product q0405Data v0305Data)) (product q0406Data v0304Data)) (product q0407Data v0303Data)) (product q0408Data v0302Data)) (product q0409Data v0301Data)) (product q0502Data v0208Data)) (product q0503Data v0207Data)) (product q0504Data v0206Data)) (product q0505Data v0205Data)) (product q0506Data v0204Data)) (product q0507Data v0203Data)) (product q0508Data v0202Data)) (product q0509Data v0201Data)) (product q0510Data v0200Data)) (product q0600Data v0110Data)) (product q0601Data v0109Data)) (product q0602Data v0108Data)) (product q0603Data v0107Data)) (product q0604Data v0106Data)) (product q0605Data v0105Data)) (product q0606Data v0104Data)) (product q0607Data v0103Data)) (product q0608Data v0102Data)) (product q0609Data v0101Data)) (product q0610Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0010Data r0301Data) (product q0011Data r0300Data)) (product q0109Data r0202Data)) (product q0110Data r0201Data)) (product q0111Data r0200Data)) (product q0208Data r0103Data)) (product q0209Data r0102Data)) (product q0210Data r0101Data)) (product q0211Data r0100Data)) (product q0306Data r0005Data)) (product q0308Data r0003Data)) (product q0309Data r0002Data)) (product q0310Data r0001Data)) (product q0311Data r0000Data)) (product q0404Data v0307Data)) (product q0405Data v0306Data)) (product q0406Data v0305Data)) (product q0407Data v0304Data)) (product q0408Data v0303Data)) (product q0409Data v0302Data)) (product q0410Data v0301Data)) (product q0503Data v0208Data)) (product q0504Data v0207Data)) (product q0505Data v0206Data)) (product q0506Data v0205Data)) (product q0507Data v0204Data)) (product q0508Data v0203Data)) (product q0509Data v0202Data)) (product q0510Data v0201Data)) (product q0511Data v0200Data)) (product q0601Data v0110Data)) (product q0602Data v0109Data)) (product q0603Data v0108Data)) (product q0604Data v0107Data)) (product q0605Data v0106Data)) (product q0606Data v0105Data)) (product q0607Data v0104Data)) (product q0608Data v0103Data)) (product q0609Data v0102Data)) (product q0610Data v0101Data)) (product q0611Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0011Data r0301Data) (product q0012Data r0300Data)) (product q0110Data r0202Data)) (product q0111Data r0201Data)) (product q0112Data r0200Data)) (product q0209Data r0103Data)) (product q0210Data r0102Data)) (product q0211Data r0101Data)) (product q0212Data r0100Data)) (product q0307Data r0005Data)) (product q0309Data r0003Data)) (product q0310Data r0002Data)) (product q0311Data r0001Data)) (product q0312Data r0000Data)) (product q0405Data v0307Data)) (product q0406Data v0306Data)) (product q0407Data v0305Data)) (product q0408Data v0304Data)) (product q0409Data v0303Data)) (product q0410Data v0302Data)) (product q0411Data v0301Data)) (product q0504Data v0208Data)) (product q0505Data v0207Data)) (product q0506Data v0206Data)) (product q0507Data v0205Data)) (product q0508Data v0204Data)) (product q0509Data v0203Data)) (product q0510Data v0202Data)) (product q0511Data v0201Data)) (product q0512Data v0200Data)) (product q0602Data v0110Data)) (product q0603Data v0109Data)) (product q0604Data v0108Data)) (product q0605Data v0107Data)) (product q0606Data v0106Data)) (product q0607Data v0105Data)) (product q0608Data v0104Data)) (product q0609Data v0103Data)) (product q0610Data v0102Data)) (product q0611Data v0101Data)) (product q0612Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0012Data r0301Data) (product q0013Data r0300Data)) (product q0111Data r0202Data)) (product q0112Data r0201Data)) (product q0113Data r0200Data)) (product q0210Data r0103Data)) (product q0211Data r0102Data)) (product q0212Data r0101Data)) (product q0213Data r0100Data)) (product q0308Data r0005Data)) (product q0310Data r0003Data)) (product q0311Data r0002Data)) (product q0312Data r0001Data)) (product q0313Data r0000Data)) (product q0406Data v0307Data)) (product q0407Data v0306Data)) (product q0408Data v0305Data)) (product q0409Data v0304Data)) (product q0410Data v0303Data)) (product q0411Data v0302Data)) (product q0412Data v0301Data)) (product q0505Data v0208Data)) (product q0506Data v0207Data)) (product q0507Data v0206Data)) (product q0508Data v0205Data)) (product q0509Data v0204Data)) (product q0510Data v0203Data)) (product q0511Data v0202Data)) (product q0512Data v0201Data)) (product q0513Data v0200Data)) (product q0603Data v0110Data)) (product q0604Data v0109Data)) (product q0605Data v0108Data)) (product q0606Data v0107Data)) (product q0607Data v0106Data)) (product q0608Data v0105Data)) (product q0609Data v0104Data)) (product q0610Data v0103Data)) (product q0611Data v0102Data)) (product q0612Data v0101Data)) (product q0613Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0013Data r0301Data) (product q0014Data r0300Data)) (product q0112Data r0202Data)) (product q0113Data r0201Data)) (product q0114Data r0200Data)) (product q0211Data r0103Data)) (product q0212Data r0102Data)) (product q0213Data r0101Data)) (product q0214Data r0100Data)) (product q0309Data r0005Data)) (product q0311Data r0003Data)) (product q0312Data r0002Data)) (product q0313Data r0001Data)) (product q0314Data r0000Data)) (product q0407Data v0307Data)) (product q0408Data v0306Data)) (product q0409Data v0305Data)) (product q0410Data v0304Data)) (product q0411Data v0303Data)) (product q0412Data v0302Data)) (product q0413Data v0301Data)) (product q0506Data v0208Data)) (product q0507Data v0207Data)) (product q0508Data v0206Data)) (product q0509Data v0205Data)) (product q0510Data v0204Data)) (product q0511Data v0203Data)) (product q0512Data v0202Data)) (product q0513Data v0201Data)) (product q0514Data v0200Data)) (product q0604Data v0110Data)) (product q0605Data v0109Data)) (product q0606Data v0108Data)) (product q0607Data v0107Data)) (product q0608Data v0106Data)) (product q0609Data v0105Data)) (product q0610Data v0104Data)) (product q0611Data v0103Data)) (product q0612Data v0102Data)) (product q0613Data v0101Data)) (product q0614Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0014Data r0301Data) (product q0015Data r0300Data)) (product q0113Data r0202Data)) (product q0114Data r0201Data)) (product q0115Data r0200Data)) (product q0212Data r0103Data)) (product q0213Data r0102Data)) (product q0214Data r0101Data)) (product q0215Data r0100Data)) (product q0310Data r0005Data)) (product q0312Data r0003Data)) (product q0313Data r0002Data)) (product q0314Data r0001Data)) (product q0315Data r0000Data)) (product q0408Data v0307Data)) (product q0409Data v0306Data)) (product q0410Data v0305Data)) (product q0411Data v0304Data)) (product q0412Data v0303Data)) (product q0413Data v0302Data)) (product q0414Data v0301Data)) (product q0507Data v0208Data)) (product q0508Data v0207Data)) (product q0509Data v0206Data)) (product q0510Data v0205Data)) (product q0511Data v0204Data)) (product q0512Data v0203Data)) (product q0513Data v0202Data)) (product q0514Data v0201Data)) (product q0515Data v0200Data)) (product q0605Data v0110Data)) (product q0606Data v0109Data)) (product q0607Data v0108Data)) (product q0608Data v0107Data)) (product q0609Data v0106Data)) (product q0610Data v0105Data)) (product q0611Data v0104Data)) (product q0612Data v0103Data)) (product q0613Data v0102Data)) (product q0614Data v0101Data)) (product q0615Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0015Data r0301Data) (product q0016Data r0300Data)) (product q0114Data r0202Data)) (product q0115Data r0201Data)) (product q0116Data r0200Data)) (product q0213Data r0103Data)) (product q0214Data r0102Data)) (product q0215Data r0101Data)) (product q0216Data r0100Data)) (product q0311Data r0005Data)) (product q0313Data r0003Data)) (product q0314Data r0002Data)) (product q0315Data r0001Data)) (product q0316Data r0000Data)) (product q0409Data v0307Data)) (product q0410Data v0306Data)) (product q0411Data v0305Data)) (product q0412Data v0304Data)) (product q0413Data v0303Data)) (product q0414Data v0302Data)) (product q0415Data v0301Data)) (product q0508Data v0208Data)) (product q0509Data v0207Data)) (product q0510Data v0206Data)) (product q0511Data v0205Data)) (product q0512Data v0204Data)) (product q0513Data v0203Data)) (product q0514Data v0202Data)) (product q0515Data v0201Data)) (product q0516Data v0200Data)) (product q0606Data v0110Data)) (product q0607Data v0109Data)) (product q0608Data v0108Data)) (product q0609Data v0107Data)) (product q0610Data v0106Data)) (product q0611Data v0105Data)) (product q0612Data v0104Data)) (product q0613Data v0103Data)) (product q0614Data v0102Data)) (product q0615Data v0101Data)) (product q0616Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0016Data r0301Data) (product q0017Data r0300Data)) (product q0115Data r0202Data)) (product q0116Data r0201Data)) (product q0117Data r0200Data)) (product q0214Data r0103Data)) (product q0215Data r0102Data)) (product q0216Data r0101Data)) (product q0217Data r0100Data)) (product q0312Data r0005Data)) (product q0314Data r0003Data)) (product q0315Data r0002Data)) (product q0316Data r0001Data)) (product q0317Data r0000Data)) (product q0410Data v0307Data)) (product q0411Data v0306Data)) (product q0412Data v0305Data)) (product q0413Data v0304Data)) (product q0414Data v0303Data)) (product q0415Data v0302Data)) (product q0416Data v0301Data)) (product q0509Data v0208Data)) (product q0510Data v0207Data)) (product q0511Data v0206Data)) (product q0512Data v0205Data)) (product q0513Data v0204Data)) (product q0514Data v0203Data)) (product q0515Data v0202Data)) (product q0516Data v0201Data)) (product q0517Data v0200Data)) (product q0607Data v0110Data)) (product q0608Data v0109Data)) (product q0609Data v0108Data)) (product q0610Data v0107Data)) (product q0611Data v0106Data)) (product q0612Data v0105Data)) (product q0613Data v0104Data)) (product q0614Data v0103Data)) (product q0615Data v0102Data)) (product q0616Data v0101Data)) (product q0617Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0017Data r0301Data) (product q0018Data r0300Data)) (product q0116Data r0202Data)) (product q0117Data r0201Data)) (product q0118Data r0200Data)) (product q0215Data r0103Data)) (product q0216Data r0102Data)) (product q0217Data r0101Data)) (product q0218Data r0100Data)) (product q0313Data r0005Data)) (product q0315Data r0003Data)) (product q0316Data r0002Data)) (product q0317Data r0001Data)) (product q0318Data r0000Data)) (product q0411Data v0307Data)) (product q0412Data v0306Data)) (product q0413Data v0305Data)) (product q0414Data v0304Data)) (product q0415Data v0303Data)) (product q0416Data v0302Data)) (product q0417Data v0301Data)) (product q0510Data v0208Data)) (product q0511Data v0207Data)) (product q0512Data v0206Data)) (product q0513Data v0205Data)) (product q0514Data v0204Data)) (product q0515Data v0203Data)) (product q0516Data v0202Data)) (product q0517Data v0201Data)) (product q0518Data v0200Data)) (product q0608Data v0110Data)) (product q0609Data v0109Data)) (product q0610Data v0108Data)) (product q0611Data v0107Data)) (product q0612Data v0106Data)) (product q0613Data v0105Data)) (product q0614Data v0104Data)) (product q0615Data v0103Data)) (product q0616Data v0102Data)) (product q0617Data v0101Data)) (product q0618Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0018Data r0301Data) (product q0019Data r0300Data)) (product q0117Data r0202Data)) (product q0118Data r0201Data)) (product q0119Data r0200Data)) (product q0216Data r0103Data)) (product q0217Data r0102Data)) (product q0218Data r0101Data)) (product q0219Data r0100Data)) (product q0314Data r0005Data)) (product q0316Data r0003Data)) (product q0317Data r0002Data)) (product q0318Data r0001Data)) (product q0319Data r0000Data)) (product q0412Data v0307Data)) (product q0413Data v0306Data)) (product q0414Data v0305Data)) (product q0415Data v0304Data)) (product q0416Data v0303Data)) (product q0417Data v0302Data)) (product q0418Data v0301Data)) (product q0511Data v0208Data)) (product q0512Data v0207Data)) (product q0513Data v0206Data)) (product q0514Data v0205Data)) (product q0515Data v0204Data)) (product q0516Data v0203Data)) (product q0517Data v0202Data)) (product q0518Data v0201Data)) (product q0519Data v0200Data)) (product q0609Data v0110Data)) (product q0610Data v0109Data)) (product q0611Data v0108Data)) (product q0612Data v0107Data)) (product q0613Data v0106Data)) (product q0614Data v0105Data)) (product q0615Data v0104Data)) (product q0616Data v0103Data)) (product q0617Data v0102Data)) (product q0618Data v0101Data)) (product q0619Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0019Data r0301Data) (product q0020Data r0300Data)) (product q0118Data r0202Data)) (product q0119Data r0201Data)) (product q0120Data r0200Data)) (product q0217Data r0103Data)) (product q0218Data r0102Data)) (product q0219Data r0101Data)) (product q0220Data r0100Data)) (product q0315Data r0005Data)) (product q0317Data r0003Data)) (product q0318Data r0002Data)) (product q0319Data r0001Data)) (product q0320Data r0000Data)) (product q0413Data v0307Data)) (product q0414Data v0306Data)) (product q0415Data v0305Data)) (product q0416Data v0304Data)) (product q0417Data v0303Data)) (product q0418Data v0302Data)) (product q0419Data v0301Data)) (product q0512Data v0208Data)) (product q0513Data v0207Data)) (product q0514Data v0206Data)) (product q0515Data v0205Data)) (product q0516Data v0204Data)) (product q0517Data v0203Data)) (product q0518Data v0202Data)) (product q0519Data v0201Data)) (product q0520Data v0200Data)) (product q0610Data v0110Data)) (product q0611Data v0109Data)) (product q0612Data v0108Data)) (product q0613Data v0107Data)) (product q0614Data v0106Data)) (product q0615Data v0105Data)) (product q0616Data v0104Data)) (product q0617Data v0103Data)) (product q0618Data v0102Data)) (product q0619Data v0101Data)) (product q0620Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0020Data r0301Data) (product q0021Data r0300Data)) (product q0119Data r0202Data)) (product q0120Data r0201Data)) (product q0121Data r0200Data)) (product q0218Data r0103Data)) (product q0219Data r0102Data)) (product q0220Data r0101Data)) (product q0221Data r0100Data)) (product q0316Data r0005Data)) (product q0318Data r0003Data)) (product q0319Data r0002Data)) (product q0320Data r0001Data)) (product q0321Data r0000Data)) (product q0414Data v0307Data)) (product q0415Data v0306Data)) (product q0416Data v0305Data)) (product q0417Data v0304Data)) (product q0418Data v0303Data)) (product q0419Data v0302Data)) (product q0420Data v0301Data)) (product q0513Data v0208Data)) (product q0514Data v0207Data)) (product q0515Data v0206Data)) (product q0516Data v0205Data)) (product q0517Data v0204Data)) (product q0518Data v0203Data)) (product q0519Data v0202Data)) (product q0520Data v0201Data)) (product q0521Data v0200Data)) (product q0611Data v0110Data)) (product q0612Data v0109Data)) (product q0613Data v0108Data)) (product q0614Data v0107Data)) (product q0615Data v0106Data)) (product q0616Data v0105Data)) (product q0617Data v0104Data)) (product q0618Data v0103Data)) (product q0619Data v0102Data)) (product q0620Data v0101Data)) (product q0621Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0021Data r0301Data) (product q0022Data r0300Data)) (product q0120Data r0202Data)) (product q0121Data r0201Data)) (product q0122Data r0200Data)) (product q0219Data r0103Data)) (product q0220Data r0102Data)) (product q0221Data r0101Data)) (product q0222Data r0100Data)) (product q0317Data r0005Data)) (product q0319Data r0003Data)) (product q0320Data r0002Data)) (product q0321Data r0001Data)) (product q0322Data r0000Data)) (product q0415Data v0307Data)) (product q0416Data v0306Data)) (product q0417Data v0305Data)) (product q0418Data v0304Data)) (product q0419Data v0303Data)) (product q0420Data v0302Data)) (product q0421Data v0301Data)) (product q0514Data v0208Data)) (product q0515Data v0207Data)) (product q0516Data v0206Data)) (product q0517Data v0205Data)) (product q0518Data v0204Data)) (product q0519Data v0203Data)) (product q0520Data v0202Data)) (product q0521Data v0201Data)) (product q0522Data v0200Data)) (product q0612Data v0110Data)) (product q0613Data v0109Data)) (product q0614Data v0108Data)) (product q0615Data v0107Data)) (product q0616Data v0106Data)) (product q0617Data v0105Data)) (product q0618Data v0104Data)) (product q0619Data v0103Data)) (product q0620Data v0102Data)) (product q0621Data v0101Data)) (product q0622Data v0100Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0022Data r0301Data) (product q0023Data r0300Data)) (product q0121Data r0202Data)) (product q0122Data r0201Data)) (product q0123Data r0200Data)) (product q0220Data r0103Data)) (product q0221Data r0102Data)) (product q0222Data r0101Data)) (product q0223Data r0100Data)) (product q0318Data r0005Data)) (product q0320Data r0003Data)) (product q0321Data r0002Data)) (product q0322Data r0001Data)) (product q0323Data r0000Data)) (product q0416Data v0307Data)) (product q0417Data v0306Data)) (product q0418Data v0305Data)) (product q0419Data v0304Data)) (product q0420Data v0303Data)) (product q0421Data v0302Data)) (product q0422Data v0301Data)) (product q0515Data v0208Data)) (product q0516Data v0207Data)) (product q0517Data v0206Data)) (product q0518Data v0205Data)) (product q0519Data v0204Data)) (product q0520Data v0203Data)) (product q0521Data v0202Data)) (product q0522Data v0201Data)) (product q0523Data v0200Data)) (product q0613Data v0110Data)) (product q0614Data v0109Data)) (product q0615Data v0108Data)) (product q0616Data v0107Data)) (product q0617Data v0106Data)) (product q0618Data v0105Data)) (product q0619Data v0104Data)) (product q0620Data v0103Data)) (product q0621Data v0102Data)) (product q0622Data v0101Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0023Data r0301Data) (product q0024Data r0300Data)) (product q0122Data r0202Data)) (product q0123Data r0201Data)) (product q0124Data r0200Data)) (product q0221Data r0103Data)) (product q0222Data r0102Data)) (product q0223Data r0101Data)) (product q0224Data r0100Data)) (product q0319Data r0005Data)) (product q0321Data r0003Data)) (product q0322Data r0002Data)) (product q0323Data r0001Data)) (product q0324Data r0000Data)) (product q0417Data v0307Data)) (product q0418Data v0306Data)) (product q0419Data v0305Data)) (product q0420Data v0304Data)) (product q0421Data v0303Data)) (product q0422Data v0302Data)) (product q0423Data v0301Data)) (product q0516Data v0208Data)) (product q0517Data v0207Data)) (product q0518Data v0206Data)) (product q0519Data v0205Data)) (product q0520Data v0204Data)) (product q0521Data v0203Data)) (product q0522Data v0202Data)) (product q0523Data v0201Data)) (product q0614Data v0110Data)) (product q0615Data v0109Data)) (product q0616Data v0108Data)) (product q0617Data v0107Data)) (product q0618Data v0106Data)) (product q0619Data v0105Data)) (product q0620Data v0104Data)) (product q0621Data v0103Data)) (product q0622Data v0102Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0024Data r0301Data) (product q0025Data r0300Data)) (product q0123Data r0202Data)) (product q0124Data r0201Data)) (product q0125Data r0200Data)) (product q0222Data r0103Data)) (product q0223Data r0102Data)) (product q0224Data r0101Data)) (product q0225Data r0100Data)) (product q0320Data r0005Data)) (product q0322Data r0003Data)) (product q0323Data r0002Data)) (product q0324Data r0001Data)) (product q0325Data r0000Data)) (product q0418Data v0307Data)) (product q0419Data v0306Data)) (product q0420Data v0305Data)) (product q0421Data v0304Data)) (product q0422Data v0303Data)) (product q0423Data v0302Data)) (product q0424Data v0301Data)) (product q0517Data v0208Data)) (product q0518Data v0207Data)) (product q0519Data v0206Data)) (product q0520Data v0205Data)) (product q0521Data v0204Data)) (product q0522Data v0203Data)) (product q0523Data v0202Data)) (product q0615Data v0110Data)) (product q0616Data v0109Data)) (product q0617Data v0108Data)) (product q0618Data v0107Data)) (product q0619Data v0106Data)) (product q0620Data v0105Data)) (product q0621Data v0104Data)) (product q0622Data v0103Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0025Data r0301Data) (product q0026Data r0300Data)) (product q0124Data r0202Data)) (product q0125Data r0201Data)) (product q0126Data r0200Data)) (product q0223Data r0103Data)) (product q0224Data r0102Data)) (product q0225Data r0101Data)) (product q0226Data r0100Data)) (product q0321Data r0005Data)) (product q0323Data r0003Data)) (product q0324Data r0002Data)) (product q0325Data r0001Data)) (product q0326Data r0000Data)) (product q0419Data v0307Data)) (product q0420Data v0306Data)) (product q0421Data v0305Data)) (product q0422Data v0304Data)) (product q0423Data v0303Data)) (product q0424Data v0302Data)) (product q0518Data v0208Data)) (product q0519Data v0207Data)) (product q0520Data v0206Data)) (product q0521Data v0205Data)) (product q0522Data v0204Data)) (product q0523Data v0203Data)) (product q0616Data v0110Data)) (product q0617Data v0109Data)) (product q0618Data v0108Data)) (product q0619Data v0107Data)) (product q0620Data v0106Data)) (product q0621Data v0105Data)) (product q0622Data v0104Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0026Data r0301Data) (product q0027Data r0300Data)) (product q0125Data r0202Data)) (product q0126Data r0201Data)) (product q0127Data r0200Data)) (product q0224Data r0103Data)) (product q0225Data r0102Data)) (product q0226Data r0101Data)) (product q0227Data r0100Data)) (product q0322Data r0005Data)) (product q0324Data r0003Data)) (product q0325Data r0002Data)) (product q0326Data r0001Data)) (product q0327Data r0000Data)) (product q0420Data v0307Data)) (product q0421Data v0306Data)) (product q0422Data v0305Data)) (product q0423Data v0304Data)) (product q0424Data v0303Data)) (product q0519Data v0208Data)) (product q0520Data v0207Data)) (product q0521Data v0206Data)) (product q0522Data v0205Data)) (product q0523Data v0204Data)) (product q0617Data v0110Data)) (product q0618Data v0109Data)) (product q0619Data v0108Data)) (product q0620Data v0107Data)) (product q0621Data v0106Data)) (product q0622Data v0105Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0027Data r0301Data) (product q0028Data r0300Data)) (product q0126Data r0202Data)) (product q0127Data r0201Data)) (product q0128Data r0200Data)) (product q0225Data r0103Data)) (product q0226Data r0102Data)) (product q0227Data r0101Data)) (product q0228Data r0100Data)) (product q0323Data r0005Data)) (product q0325Data r0003Data)) (product q0326Data r0002Data)) (product q0327Data r0001Data)) (product q0421Data v0307Data)) (product q0422Data v0306Data)) (product q0423Data v0305Data)) (product q0424Data v0304Data)) (product q0520Data v0208Data)) (product q0521Data v0207Data)) (product q0522Data v0206Data)) (product q0523Data v0205Data)) (product q0618Data v0110Data)) (product q0619Data v0109Data)) (product q0620Data v0108Data)) (product q0621Data v0107Data)) (product q0622Data v0106Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0028Data r0301Data) (product q0029Data r0300Data)) (product q0127Data r0202Data)) (product q0128Data r0201Data)) (product q0129Data r0200Data)) (product q0226Data r0103Data)) (product q0227Data r0102Data)) (product q0228Data r0101Data)) (product q0324Data r0005Data)) (product q0326Data r0003Data)) (product q0327Data r0002Data)) (product q0422Data v0307Data)) (product q0423Data v0306Data)) (product q0424Data v0305Data)) (product q0521Data v0208Data)) (product q0522Data v0207Data)) (product q0523Data v0206Data)) (product q0619Data v0110Data)) (product q0620Data v0109Data)) (product q0621Data v0108Data)) (product q0622Data v0107Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0029Data r0301Data) (product q0030Data r0300Data)) (product q0128Data r0202Data)) (product q0129Data r0201Data)) (product q0227Data r0103Data)) (product q0228Data r0102Data)) (product q0325Data r0005Data)) (product q0327Data r0003Data)) (product q0423Data v0307Data)) (product q0424Data v0306Data)) (product q0522Data v0208Data)) (product q0523Data v0207Data)) (product q0620Data v0110Data)) (product q0621Data v0109Data)) (product q0622Data v0108Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0030Data r0301Data) (product q0129Data r0202Data)) (product q0228Data r0103Data)) (product q0326Data r0005Data)) (product q0424Data v0307Data)) (product q0523Data v0208Data)) (product q0621Data v0110Data)) (product q0622Data v0109Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0030, q0129, q0228, q0326, q0424, q0523, q0621, q0622, r0005, r0103, r0202, r0301, v0109, v0110, v0208, v0307] using he

#print axioms row3_x31

compact_certificate theorem row3_x32 (y z w : ℂ) :
    q0327 y z w*r0005 y z w +
    q0622 y z w*v0110 y z w=0 := by
  have h : (merge (product q0327Data r0005Data) (product q0622Data v0110Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0327, q0622, r0005, v0110] using he

#print axioms row3_x32

compact_certificate theorem row4_x00 (y z w : ℂ) :
    q0100 y z w*r0300 y z w +
    q0600 y z w*v0200 y z w=0 := by
  have h : (merge (product q0100Data r0300Data) (product q0600Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0100Data r0301Data) (product q0101Data r0300Data)) (product q0201Data r0200Data)) (product q0301Data r0100Data)) (product q0400Data v0401Data)) (product q0500Data v0301Data)) (product q0600Data v0201Data)) (product q0601Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0101Data r0301Data) (product q0102Data r0300Data)) (product q0201Data r0201Data)) (product q0202Data r0200Data)) (product q0301Data r0101Data)) (product q0302Data r0100Data)) (product q0400Data v0402Data)) (product q0401Data v0401Data)) (product q0500Data v0302Data)) (product q0501Data v0301Data)) (product q0600Data v0202Data)) (product q0601Data v0201Data)) (product q0602Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0102Data r0301Data) (product q0103Data r0300Data)) (product q0201Data r0202Data)) (product q0202Data r0201Data)) (product q0203Data r0200Data)) (product q0301Data r0102Data)) (product q0302Data r0101Data)) (product q0303Data r0100Data)) (product q0400Data v0403Data)) (product q0401Data v0402Data)) (product q0402Data v0401Data)) (product q0500Data v0303Data)) (product q0501Data v0302Data)) (product q0502Data v0301Data)) (product q0600Data v0203Data)) (product q0601Data v0202Data)) (product q0602Data v0201Data)) (product q0603Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0103Data r0301Data) (product q0104Data r0300Data)) (product q0202Data r0202Data)) (product q0203Data r0201Data)) (product q0204Data r0200Data)) (product q0301Data r0103Data)) (product q0302Data r0102Data)) (product q0303Data r0101Data)) (product q0304Data r0100Data)) (product q0400Data v0404Data)) (product q0401Data v0403Data)) (product q0402Data v0402Data)) (product q0403Data v0401Data)) (product q0500Data v0304Data)) (product q0501Data v0303Data)) (product q0502Data v0302Data)) (product q0503Data v0301Data)) (product q0600Data v0204Data)) (product q0601Data v0203Data)) (product q0602Data v0202Data)) (product q0603Data v0201Data)) (product q0604Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0104Data r0301Data) (product q0105Data r0300Data)) (product q0203Data r0202Data)) (product q0204Data r0201Data)) (product q0205Data r0200Data)) (product q0302Data r0103Data)) (product q0303Data r0102Data)) (product q0304Data r0101Data)) (product q0305Data r0100Data)) (product q0400Data v0405Data)) (product q0401Data v0404Data)) (product q0402Data v0403Data)) (product q0403Data v0402Data)) (product q0404Data v0401Data)) (product q0500Data v0305Data)) (product q0501Data v0304Data)) (product q0502Data v0303Data)) (product q0503Data v0302Data)) (product q0504Data v0301Data)) (product q0600Data v0205Data)) (product q0601Data v0204Data)) (product q0602Data v0203Data)) (product q0603Data v0202Data)) (product q0604Data v0201Data)) (product q0605Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0105Data r0301Data) (product q0106Data r0300Data)) (product q0204Data r0202Data)) (product q0205Data r0201Data)) (product q0206Data r0200Data)) (product q0303Data r0103Data)) (product q0304Data r0102Data)) (product q0305Data r0101Data)) (product q0306Data r0100Data)) (product q0400Data v0406Data)) (product q0401Data v0405Data)) (product q0402Data v0404Data)) (product q0403Data v0403Data)) (product q0404Data v0402Data)) (product q0405Data v0401Data)) (product q0500Data v0306Data)) (product q0501Data v0305Data)) (product q0502Data v0304Data)) (product q0503Data v0303Data)) (product q0504Data v0302Data)) (product q0505Data v0301Data)) (product q0600Data v0206Data)) (product q0601Data v0205Data)) (product q0602Data v0204Data)) (product q0603Data v0203Data)) (product q0604Data v0202Data)) (product q0605Data v0201Data)) (product q0606Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0106Data r0301Data) (product q0107Data r0300Data)) (product q0205Data r0202Data)) (product q0206Data r0201Data)) (product q0207Data r0200Data)) (product q0304Data r0103Data)) (product q0305Data r0102Data)) (product q0306Data r0101Data)) (product q0307Data r0100Data)) (product q0401Data v0406Data)) (product q0402Data v0405Data)) (product q0403Data v0404Data)) (product q0404Data v0403Data)) (product q0405Data v0402Data)) (product q0406Data v0401Data)) (product q0500Data v0307Data)) (product q0501Data v0306Data)) (product q0502Data v0305Data)) (product q0503Data v0304Data)) (product q0504Data v0303Data)) (product q0505Data v0302Data)) (product q0506Data v0301Data)) (product q0600Data v0207Data)) (product q0601Data v0206Data)) (product q0602Data v0205Data)) (product q0603Data v0204Data)) (product q0604Data v0203Data)) (product q0605Data v0202Data)) (product q0606Data v0201Data)) (product q0607Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0107Data r0301Data) (product q0108Data r0300Data)) (product q0206Data r0202Data)) (product q0207Data r0201Data)) (product q0208Data r0200Data)) (product q0305Data r0103Data)) (product q0306Data r0102Data)) (product q0307Data r0101Data)) (product q0308Data r0100Data)) (product q0402Data v0406Data)) (product q0403Data v0405Data)) (product q0404Data v0404Data)) (product q0405Data v0403Data)) (product q0406Data v0402Data)) (product q0407Data v0401Data)) (product q0501Data v0307Data)) (product q0502Data v0306Data)) (product q0503Data v0305Data)) (product q0504Data v0304Data)) (product q0505Data v0303Data)) (product q0506Data v0302Data)) (product q0507Data v0301Data)) (product q0600Data v0208Data)) (product q0601Data v0207Data)) (product q0602Data v0206Data)) (product q0603Data v0205Data)) (product q0604Data v0204Data)) (product q0605Data v0203Data)) (product q0606Data v0202Data)) (product q0607Data v0201Data)) (product q0608Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0108Data r0301Data) (product q0109Data r0300Data)) (product q0207Data r0202Data)) (product q0208Data r0201Data)) (product q0209Data r0200Data)) (product q0306Data r0103Data)) (product q0307Data r0102Data)) (product q0308Data r0101Data)) (product q0309Data r0100Data)) (product q0403Data v0406Data)) (product q0404Data v0405Data)) (product q0405Data v0404Data)) (product q0406Data v0403Data)) (product q0407Data v0402Data)) (product q0408Data v0401Data)) (product q0502Data v0307Data)) (product q0503Data v0306Data)) (product q0504Data v0305Data)) (product q0505Data v0304Data)) (product q0506Data v0303Data)) (product q0507Data v0302Data)) (product q0508Data v0301Data)) (product q0601Data v0208Data)) (product q0602Data v0207Data)) (product q0603Data v0206Data)) (product q0604Data v0205Data)) (product q0605Data v0204Data)) (product q0606Data v0203Data)) (product q0607Data v0202Data)) (product q0608Data v0201Data)) (product q0609Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0109Data r0301Data) (product q0110Data r0300Data)) (product q0208Data r0202Data)) (product q0209Data r0201Data)) (product q0210Data r0200Data)) (product q0307Data r0103Data)) (product q0308Data r0102Data)) (product q0309Data r0101Data)) (product q0310Data r0100Data)) (product q0404Data v0406Data)) (product q0405Data v0405Data)) (product q0406Data v0404Data)) (product q0407Data v0403Data)) (product q0408Data v0402Data)) (product q0409Data v0401Data)) (product q0503Data v0307Data)) (product q0504Data v0306Data)) (product q0505Data v0305Data)) (product q0506Data v0304Data)) (product q0507Data v0303Data)) (product q0508Data v0302Data)) (product q0509Data v0301Data)) (product q0602Data v0208Data)) (product q0603Data v0207Data)) (product q0604Data v0206Data)) (product q0605Data v0205Data)) (product q0606Data v0204Data)) (product q0607Data v0203Data)) (product q0608Data v0202Data)) (product q0609Data v0201Data)) (product q0610Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0110Data r0301Data) (product q0111Data r0300Data)) (product q0209Data r0202Data)) (product q0210Data r0201Data)) (product q0211Data r0200Data)) (product q0308Data r0103Data)) (product q0309Data r0102Data)) (product q0310Data r0101Data)) (product q0311Data r0100Data)) (product q0405Data v0406Data)) (product q0406Data v0405Data)) (product q0407Data v0404Data)) (product q0408Data v0403Data)) (product q0409Data v0402Data)) (product q0410Data v0401Data)) (product q0504Data v0307Data)) (product q0505Data v0306Data)) (product q0506Data v0305Data)) (product q0507Data v0304Data)) (product q0508Data v0303Data)) (product q0509Data v0302Data)) (product q0510Data v0301Data)) (product q0603Data v0208Data)) (product q0604Data v0207Data)) (product q0605Data v0206Data)) (product q0606Data v0205Data)) (product q0607Data v0204Data)) (product q0608Data v0203Data)) (product q0609Data v0202Data)) (product q0610Data v0201Data)) (product q0611Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0111Data r0301Data) (product q0112Data r0300Data)) (product q0210Data r0202Data)) (product q0211Data r0201Data)) (product q0212Data r0200Data)) (product q0309Data r0103Data)) (product q0310Data r0102Data)) (product q0311Data r0101Data)) (product q0312Data r0100Data)) (product q0406Data v0406Data)) (product q0407Data v0405Data)) (product q0408Data v0404Data)) (product q0409Data v0403Data)) (product q0410Data v0402Data)) (product q0411Data v0401Data)) (product q0505Data v0307Data)) (product q0506Data v0306Data)) (product q0507Data v0305Data)) (product q0508Data v0304Data)) (product q0509Data v0303Data)) (product q0510Data v0302Data)) (product q0511Data v0301Data)) (product q0604Data v0208Data)) (product q0605Data v0207Data)) (product q0606Data v0206Data)) (product q0607Data v0205Data)) (product q0608Data v0204Data)) (product q0609Data v0203Data)) (product q0610Data v0202Data)) (product q0611Data v0201Data)) (product q0612Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0112Data r0301Data) (product q0113Data r0300Data)) (product q0211Data r0202Data)) (product q0212Data r0201Data)) (product q0213Data r0200Data)) (product q0310Data r0103Data)) (product q0311Data r0102Data)) (product q0312Data r0101Data)) (product q0313Data r0100Data)) (product q0407Data v0406Data)) (product q0408Data v0405Data)) (product q0409Data v0404Data)) (product q0410Data v0403Data)) (product q0411Data v0402Data)) (product q0412Data v0401Data)) (product q0506Data v0307Data)) (product q0507Data v0306Data)) (product q0508Data v0305Data)) (product q0509Data v0304Data)) (product q0510Data v0303Data)) (product q0511Data v0302Data)) (product q0512Data v0301Data)) (product q0605Data v0208Data)) (product q0606Data v0207Data)) (product q0607Data v0206Data)) (product q0608Data v0205Data)) (product q0609Data v0204Data)) (product q0610Data v0203Data)) (product q0611Data v0202Data)) (product q0612Data v0201Data)) (product q0613Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0113Data r0301Data) (product q0114Data r0300Data)) (product q0212Data r0202Data)) (product q0213Data r0201Data)) (product q0214Data r0200Data)) (product q0311Data r0103Data)) (product q0312Data r0102Data)) (product q0313Data r0101Data)) (product q0314Data r0100Data)) (product q0408Data v0406Data)) (product q0409Data v0405Data)) (product q0410Data v0404Data)) (product q0411Data v0403Data)) (product q0412Data v0402Data)) (product q0413Data v0401Data)) (product q0507Data v0307Data)) (product q0508Data v0306Data)) (product q0509Data v0305Data)) (product q0510Data v0304Data)) (product q0511Data v0303Data)) (product q0512Data v0302Data)) (product q0513Data v0301Data)) (product q0606Data v0208Data)) (product q0607Data v0207Data)) (product q0608Data v0206Data)) (product q0609Data v0205Data)) (product q0610Data v0204Data)) (product q0611Data v0203Data)) (product q0612Data v0202Data)) (product q0613Data v0201Data)) (product q0614Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0114Data r0301Data) (product q0115Data r0300Data)) (product q0213Data r0202Data)) (product q0214Data r0201Data)) (product q0215Data r0200Data)) (product q0312Data r0103Data)) (product q0313Data r0102Data)) (product q0314Data r0101Data)) (product q0315Data r0100Data)) (product q0409Data v0406Data)) (product q0410Data v0405Data)) (product q0411Data v0404Data)) (product q0412Data v0403Data)) (product q0413Data v0402Data)) (product q0414Data v0401Data)) (product q0508Data v0307Data)) (product q0509Data v0306Data)) (product q0510Data v0305Data)) (product q0511Data v0304Data)) (product q0512Data v0303Data)) (product q0513Data v0302Data)) (product q0514Data v0301Data)) (product q0607Data v0208Data)) (product q0608Data v0207Data)) (product q0609Data v0206Data)) (product q0610Data v0205Data)) (product q0611Data v0204Data)) (product q0612Data v0203Data)) (product q0613Data v0202Data)) (product q0614Data v0201Data)) (product q0615Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0115Data r0301Data) (product q0116Data r0300Data)) (product q0214Data r0202Data)) (product q0215Data r0201Data)) (product q0216Data r0200Data)) (product q0313Data r0103Data)) (product q0314Data r0102Data)) (product q0315Data r0101Data)) (product q0316Data r0100Data)) (product q0410Data v0406Data)) (product q0411Data v0405Data)) (product q0412Data v0404Data)) (product q0413Data v0403Data)) (product q0414Data v0402Data)) (product q0415Data v0401Data)) (product q0509Data v0307Data)) (product q0510Data v0306Data)) (product q0511Data v0305Data)) (product q0512Data v0304Data)) (product q0513Data v0303Data)) (product q0514Data v0302Data)) (product q0515Data v0301Data)) (product q0608Data v0208Data)) (product q0609Data v0207Data)) (product q0610Data v0206Data)) (product q0611Data v0205Data)) (product q0612Data v0204Data)) (product q0613Data v0203Data)) (product q0614Data v0202Data)) (product q0615Data v0201Data)) (product q0616Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0116Data r0301Data) (product q0117Data r0300Data)) (product q0215Data r0202Data)) (product q0216Data r0201Data)) (product q0217Data r0200Data)) (product q0314Data r0103Data)) (product q0315Data r0102Data)) (product q0316Data r0101Data)) (product q0317Data r0100Data)) (product q0411Data v0406Data)) (product q0412Data v0405Data)) (product q0413Data v0404Data)) (product q0414Data v0403Data)) (product q0415Data v0402Data)) (product q0416Data v0401Data)) (product q0510Data v0307Data)) (product q0511Data v0306Data)) (product q0512Data v0305Data)) (product q0513Data v0304Data)) (product q0514Data v0303Data)) (product q0515Data v0302Data)) (product q0516Data v0301Data)) (product q0609Data v0208Data)) (product q0610Data v0207Data)) (product q0611Data v0206Data)) (product q0612Data v0205Data)) (product q0613Data v0204Data)) (product q0614Data v0203Data)) (product q0615Data v0202Data)) (product q0616Data v0201Data)) (product q0617Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0117Data r0301Data) (product q0118Data r0300Data)) (product q0216Data r0202Data)) (product q0217Data r0201Data)) (product q0218Data r0200Data)) (product q0315Data r0103Data)) (product q0316Data r0102Data)) (product q0317Data r0101Data)) (product q0318Data r0100Data)) (product q0412Data v0406Data)) (product q0413Data v0405Data)) (product q0414Data v0404Data)) (product q0415Data v0403Data)) (product q0416Data v0402Data)) (product q0417Data v0401Data)) (product q0511Data v0307Data)) (product q0512Data v0306Data)) (product q0513Data v0305Data)) (product q0514Data v0304Data)) (product q0515Data v0303Data)) (product q0516Data v0302Data)) (product q0517Data v0301Data)) (product q0610Data v0208Data)) (product q0611Data v0207Data)) (product q0612Data v0206Data)) (product q0613Data v0205Data)) (product q0614Data v0204Data)) (product q0615Data v0203Data)) (product q0616Data v0202Data)) (product q0617Data v0201Data)) (product q0618Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0118Data r0301Data) (product q0119Data r0300Data)) (product q0217Data r0202Data)) (product q0218Data r0201Data)) (product q0219Data r0200Data)) (product q0316Data r0103Data)) (product q0317Data r0102Data)) (product q0318Data r0101Data)) (product q0319Data r0100Data)) (product q0413Data v0406Data)) (product q0414Data v0405Data)) (product q0415Data v0404Data)) (product q0416Data v0403Data)) (product q0417Data v0402Data)) (product q0418Data v0401Data)) (product q0512Data v0307Data)) (product q0513Data v0306Data)) (product q0514Data v0305Data)) (product q0515Data v0304Data)) (product q0516Data v0303Data)) (product q0517Data v0302Data)) (product q0518Data v0301Data)) (product q0611Data v0208Data)) (product q0612Data v0207Data)) (product q0613Data v0206Data)) (product q0614Data v0205Data)) (product q0615Data v0204Data)) (product q0616Data v0203Data)) (product q0617Data v0202Data)) (product q0618Data v0201Data)) (product q0619Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0119Data r0301Data) (product q0120Data r0300Data)) (product q0218Data r0202Data)) (product q0219Data r0201Data)) (product q0220Data r0200Data)) (product q0317Data r0103Data)) (product q0318Data r0102Data)) (product q0319Data r0101Data)) (product q0320Data r0100Data)) (product q0414Data v0406Data)) (product q0415Data v0405Data)) (product q0416Data v0404Data)) (product q0417Data v0403Data)) (product q0418Data v0402Data)) (product q0419Data v0401Data)) (product q0513Data v0307Data)) (product q0514Data v0306Data)) (product q0515Data v0305Data)) (product q0516Data v0304Data)) (product q0517Data v0303Data)) (product q0518Data v0302Data)) (product q0519Data v0301Data)) (product q0612Data v0208Data)) (product q0613Data v0207Data)) (product q0614Data v0206Data)) (product q0615Data v0205Data)) (product q0616Data v0204Data)) (product q0617Data v0203Data)) (product q0618Data v0202Data)) (product q0619Data v0201Data)) (product q0620Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0120Data r0301Data) (product q0121Data r0300Data)) (product q0219Data r0202Data)) (product q0220Data r0201Data)) (product q0221Data r0200Data)) (product q0318Data r0103Data)) (product q0319Data r0102Data)) (product q0320Data r0101Data)) (product q0321Data r0100Data)) (product q0415Data v0406Data)) (product q0416Data v0405Data)) (product q0417Data v0404Data)) (product q0418Data v0403Data)) (product q0419Data v0402Data)) (product q0420Data v0401Data)) (product q0514Data v0307Data)) (product q0515Data v0306Data)) (product q0516Data v0305Data)) (product q0517Data v0304Data)) (product q0518Data v0303Data)) (product q0519Data v0302Data)) (product q0520Data v0301Data)) (product q0613Data v0208Data)) (product q0614Data v0207Data)) (product q0615Data v0206Data)) (product q0616Data v0205Data)) (product q0617Data v0204Data)) (product q0618Data v0203Data)) (product q0619Data v0202Data)) (product q0620Data v0201Data)) (product q0621Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0121Data r0301Data) (product q0122Data r0300Data)) (product q0220Data r0202Data)) (product q0221Data r0201Data)) (product q0222Data r0200Data)) (product q0319Data r0103Data)) (product q0320Data r0102Data)) (product q0321Data r0101Data)) (product q0322Data r0100Data)) (product q0416Data v0406Data)) (product q0417Data v0405Data)) (product q0418Data v0404Data)) (product q0419Data v0403Data)) (product q0420Data v0402Data)) (product q0421Data v0401Data)) (product q0515Data v0307Data)) (product q0516Data v0306Data)) (product q0517Data v0305Data)) (product q0518Data v0304Data)) (product q0519Data v0303Data)) (product q0520Data v0302Data)) (product q0521Data v0301Data)) (product q0614Data v0208Data)) (product q0615Data v0207Data)) (product q0616Data v0206Data)) (product q0617Data v0205Data)) (product q0618Data v0204Data)) (product q0619Data v0203Data)) (product q0620Data v0202Data)) (product q0621Data v0201Data)) (product q0622Data v0200Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0122Data r0301Data) (product q0123Data r0300Data)) (product q0221Data r0202Data)) (product q0222Data r0201Data)) (product q0223Data r0200Data)) (product q0320Data r0103Data)) (product q0321Data r0102Data)) (product q0322Data r0101Data)) (product q0323Data r0100Data)) (product q0417Data v0406Data)) (product q0418Data v0405Data)) (product q0419Data v0404Data)) (product q0420Data v0403Data)) (product q0421Data v0402Data)) (product q0422Data v0401Data)) (product q0516Data v0307Data)) (product q0517Data v0306Data)) (product q0518Data v0305Data)) (product q0519Data v0304Data)) (product q0520Data v0303Data)) (product q0521Data v0302Data)) (product q0522Data v0301Data)) (product q0615Data v0208Data)) (product q0616Data v0207Data)) (product q0617Data v0206Data)) (product q0618Data v0205Data)) (product q0619Data v0204Data)) (product q0620Data v0203Data)) (product q0621Data v0202Data)) (product q0622Data v0201Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0123Data r0301Data) (product q0124Data r0300Data)) (product q0222Data r0202Data)) (product q0223Data r0201Data)) (product q0224Data r0200Data)) (product q0321Data r0103Data)) (product q0322Data r0102Data)) (product q0323Data r0101Data)) (product q0324Data r0100Data)) (product q0418Data v0406Data)) (product q0419Data v0405Data)) (product q0420Data v0404Data)) (product q0421Data v0403Data)) (product q0422Data v0402Data)) (product q0423Data v0401Data)) (product q0517Data v0307Data)) (product q0518Data v0306Data)) (product q0519Data v0305Data)) (product q0520Data v0304Data)) (product q0521Data v0303Data)) (product q0522Data v0302Data)) (product q0523Data v0301Data)) (product q0616Data v0208Data)) (product q0617Data v0207Data)) (product q0618Data v0206Data)) (product q0619Data v0205Data)) (product q0620Data v0204Data)) (product q0621Data v0203Data)) (product q0622Data v0202Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0124Data r0301Data) (product q0125Data r0300Data)) (product q0223Data r0202Data)) (product q0224Data r0201Data)) (product q0225Data r0200Data)) (product q0322Data r0103Data)) (product q0323Data r0102Data)) (product q0324Data r0101Data)) (product q0325Data r0100Data)) (product q0419Data v0406Data)) (product q0420Data v0405Data)) (product q0421Data v0404Data)) (product q0422Data v0403Data)) (product q0423Data v0402Data)) (product q0424Data v0401Data)) (product q0518Data v0307Data)) (product q0519Data v0306Data)) (product q0520Data v0305Data)) (product q0521Data v0304Data)) (product q0522Data v0303Data)) (product q0523Data v0302Data)) (product q0617Data v0208Data)) (product q0618Data v0207Data)) (product q0619Data v0206Data)) (product q0620Data v0205Data)) (product q0621Data v0204Data)) (product q0622Data v0203Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0125Data r0301Data) (product q0126Data r0300Data)) (product q0224Data r0202Data)) (product q0225Data r0201Data)) (product q0226Data r0200Data)) (product q0323Data r0103Data)) (product q0324Data r0102Data)) (product q0325Data r0101Data)) (product q0326Data r0100Data)) (product q0420Data v0406Data)) (product q0421Data v0405Data)) (product q0422Data v0404Data)) (product q0423Data v0403Data)) (product q0424Data v0402Data)) (product q0519Data v0307Data)) (product q0520Data v0306Data)) (product q0521Data v0305Data)) (product q0522Data v0304Data)) (product q0523Data v0303Data)) (product q0618Data v0208Data)) (product q0619Data v0207Data)) (product q0620Data v0206Data)) (product q0621Data v0205Data)) (product q0622Data v0204Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0126Data r0301Data) (product q0127Data r0300Data)) (product q0225Data r0202Data)) (product q0226Data r0201Data)) (product q0227Data r0200Data)) (product q0324Data r0103Data)) (product q0325Data r0102Data)) (product q0326Data r0101Data)) (product q0327Data r0100Data)) (product q0421Data v0406Data)) (product q0422Data v0405Data)) (product q0423Data v0404Data)) (product q0424Data v0403Data)) (product q0520Data v0307Data)) (product q0521Data v0306Data)) (product q0522Data v0305Data)) (product q0523Data v0304Data)) (product q0619Data v0208Data)) (product q0620Data v0207Data)) (product q0621Data v0206Data)) (product q0622Data v0205Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0127Data r0301Data) (product q0128Data r0300Data)) (product q0226Data r0202Data)) (product q0227Data r0201Data)) (product q0228Data r0200Data)) (product q0325Data r0103Data)) (product q0326Data r0102Data)) (product q0327Data r0101Data)) (product q0422Data v0406Data)) (product q0423Data v0405Data)) (product q0424Data v0404Data)) (product q0521Data v0307Data)) (product q0522Data v0306Data)) (product q0523Data v0305Data)) (product q0620Data v0208Data)) (product q0621Data v0207Data)) (product q0622Data v0206Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0128Data r0301Data) (product q0129Data r0300Data)) (product q0227Data r0202Data)) (product q0228Data r0201Data)) (product q0326Data r0103Data)) (product q0327Data r0102Data)) (product q0423Data v0406Data)) (product q0424Data v0405Data)) (product q0522Data v0307Data)) (product q0523Data v0306Data)) (product q0621Data v0208Data)) (product q0622Data v0207Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (product q0129Data r0301Data) (product q0228Data r0202Data)) (product q0327Data r0103Data)) (product q0424Data v0406Data)) (product q0523Data v0307Data)) (product q0622Data v0208Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0129, q0228, q0327, q0424, q0523, q0622, r0103, r0202, r0301, v0208, v0307, v0406] using he

#print axioms row4_x30

compact_certificate theorem row5_x01 (y z w : ℂ) :
    q0201 y z w*r0300 y z w +
    q0301 y z w*r0200 y z w +
    q0500 y z w*v0401 y z w +
    q0600 y z w*v0301 y z w=0 := by
  have h : (merge (merge (merge (product q0201Data r0300Data) (product q0301Data r0200Data)) (product q0500Data v0401Data)) (product q0600Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0201Data r0301Data) (product q0202Data r0300Data)) (product q0301Data r0201Data)) (product q0302Data r0200Data)) (product q0500Data v0402Data)) (product q0501Data v0401Data)) (product q0600Data v0302Data)) (product q0601Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0202Data r0301Data) (product q0203Data r0300Data)) (product q0301Data r0202Data)) (product q0302Data r0201Data)) (product q0303Data r0200Data)) (product q0500Data v0403Data)) (product q0501Data v0402Data)) (product q0502Data v0401Data)) (product q0600Data v0303Data)) (product q0601Data v0302Data)) (product q0602Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0203Data r0301Data) (product q0204Data r0300Data)) (product q0302Data r0202Data)) (product q0303Data r0201Data)) (product q0304Data r0200Data)) (product q0500Data v0404Data)) (product q0501Data v0403Data)) (product q0502Data v0402Data)) (product q0503Data v0401Data)) (product q0600Data v0304Data)) (product q0601Data v0303Data)) (product q0602Data v0302Data)) (product q0603Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0204Data r0301Data) (product q0205Data r0300Data)) (product q0303Data r0202Data)) (product q0304Data r0201Data)) (product q0305Data r0200Data)) (product q0500Data v0405Data)) (product q0501Data v0404Data)) (product q0502Data v0403Data)) (product q0503Data v0402Data)) (product q0504Data v0401Data)) (product q0600Data v0305Data)) (product q0601Data v0304Data)) (product q0602Data v0303Data)) (product q0603Data v0302Data)) (product q0604Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0205Data r0301Data) (product q0206Data r0300Data)) (product q0304Data r0202Data)) (product q0305Data r0201Data)) (product q0306Data r0200Data)) (product q0500Data v0406Data)) (product q0501Data v0405Data)) (product q0502Data v0404Data)) (product q0503Data v0403Data)) (product q0504Data v0402Data)) (product q0505Data v0401Data)) (product q0600Data v0306Data)) (product q0601Data v0305Data)) (product q0602Data v0304Data)) (product q0603Data v0303Data)) (product q0604Data v0302Data)) (product q0605Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0206Data r0301Data) (product q0207Data r0300Data)) (product q0305Data r0202Data)) (product q0306Data r0201Data)) (product q0307Data r0200Data)) (product q0501Data v0406Data)) (product q0502Data v0405Data)) (product q0503Data v0404Data)) (product q0504Data v0403Data)) (product q0505Data v0402Data)) (product q0506Data v0401Data)) (product q0600Data v0307Data)) (product q0601Data v0306Data)) (product q0602Data v0305Data)) (product q0603Data v0304Data)) (product q0604Data v0303Data)) (product q0605Data v0302Data)) (product q0606Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0207Data r0301Data) (product q0208Data r0300Data)) (product q0306Data r0202Data)) (product q0307Data r0201Data)) (product q0308Data r0200Data)) (product q0502Data v0406Data)) (product q0503Data v0405Data)) (product q0504Data v0404Data)) (product q0505Data v0403Data)) (product q0506Data v0402Data)) (product q0507Data v0401Data)) (product q0601Data v0307Data)) (product q0602Data v0306Data)) (product q0603Data v0305Data)) (product q0604Data v0304Data)) (product q0605Data v0303Data)) (product q0606Data v0302Data)) (product q0607Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0208Data r0301Data) (product q0209Data r0300Data)) (product q0307Data r0202Data)) (product q0308Data r0201Data)) (product q0309Data r0200Data)) (product q0503Data v0406Data)) (product q0504Data v0405Data)) (product q0505Data v0404Data)) (product q0506Data v0403Data)) (product q0507Data v0402Data)) (product q0508Data v0401Data)) (product q0602Data v0307Data)) (product q0603Data v0306Data)) (product q0604Data v0305Data)) (product q0605Data v0304Data)) (product q0606Data v0303Data)) (product q0607Data v0302Data)) (product q0608Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0209Data r0301Data) (product q0210Data r0300Data)) (product q0308Data r0202Data)) (product q0309Data r0201Data)) (product q0310Data r0200Data)) (product q0504Data v0406Data)) (product q0505Data v0405Data)) (product q0506Data v0404Data)) (product q0507Data v0403Data)) (product q0508Data v0402Data)) (product q0509Data v0401Data)) (product q0603Data v0307Data)) (product q0604Data v0306Data)) (product q0605Data v0305Data)) (product q0606Data v0304Data)) (product q0607Data v0303Data)) (product q0608Data v0302Data)) (product q0609Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0210Data r0301Data) (product q0211Data r0300Data)) (product q0309Data r0202Data)) (product q0310Data r0201Data)) (product q0311Data r0200Data)) (product q0505Data v0406Data)) (product q0506Data v0405Data)) (product q0507Data v0404Data)) (product q0508Data v0403Data)) (product q0509Data v0402Data)) (product q0510Data v0401Data)) (product q0604Data v0307Data)) (product q0605Data v0306Data)) (product q0606Data v0305Data)) (product q0607Data v0304Data)) (product q0608Data v0303Data)) (product q0609Data v0302Data)) (product q0610Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0211Data r0301Data) (product q0212Data r0300Data)) (product q0310Data r0202Data)) (product q0311Data r0201Data)) (product q0312Data r0200Data)) (product q0506Data v0406Data)) (product q0507Data v0405Data)) (product q0508Data v0404Data)) (product q0509Data v0403Data)) (product q0510Data v0402Data)) (product q0511Data v0401Data)) (product q0605Data v0307Data)) (product q0606Data v0306Data)) (product q0607Data v0305Data)) (product q0608Data v0304Data)) (product q0609Data v0303Data)) (product q0610Data v0302Data)) (product q0611Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0212Data r0301Data) (product q0213Data r0300Data)) (product q0311Data r0202Data)) (product q0312Data r0201Data)) (product q0313Data r0200Data)) (product q0507Data v0406Data)) (product q0508Data v0405Data)) (product q0509Data v0404Data)) (product q0510Data v0403Data)) (product q0511Data v0402Data)) (product q0512Data v0401Data)) (product q0606Data v0307Data)) (product q0607Data v0306Data)) (product q0608Data v0305Data)) (product q0609Data v0304Data)) (product q0610Data v0303Data)) (product q0611Data v0302Data)) (product q0612Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0213Data r0301Data) (product q0214Data r0300Data)) (product q0312Data r0202Data)) (product q0313Data r0201Data)) (product q0314Data r0200Data)) (product q0508Data v0406Data)) (product q0509Data v0405Data)) (product q0510Data v0404Data)) (product q0511Data v0403Data)) (product q0512Data v0402Data)) (product q0513Data v0401Data)) (product q0607Data v0307Data)) (product q0608Data v0306Data)) (product q0609Data v0305Data)) (product q0610Data v0304Data)) (product q0611Data v0303Data)) (product q0612Data v0302Data)) (product q0613Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0214Data r0301Data) (product q0215Data r0300Data)) (product q0313Data r0202Data)) (product q0314Data r0201Data)) (product q0315Data r0200Data)) (product q0509Data v0406Data)) (product q0510Data v0405Data)) (product q0511Data v0404Data)) (product q0512Data v0403Data)) (product q0513Data v0402Data)) (product q0514Data v0401Data)) (product q0608Data v0307Data)) (product q0609Data v0306Data)) (product q0610Data v0305Data)) (product q0611Data v0304Data)) (product q0612Data v0303Data)) (product q0613Data v0302Data)) (product q0614Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0215Data r0301Data) (product q0216Data r0300Data)) (product q0314Data r0202Data)) (product q0315Data r0201Data)) (product q0316Data r0200Data)) (product q0510Data v0406Data)) (product q0511Data v0405Data)) (product q0512Data v0404Data)) (product q0513Data v0403Data)) (product q0514Data v0402Data)) (product q0515Data v0401Data)) (product q0609Data v0307Data)) (product q0610Data v0306Data)) (product q0611Data v0305Data)) (product q0612Data v0304Data)) (product q0613Data v0303Data)) (product q0614Data v0302Data)) (product q0615Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0216Data r0301Data) (product q0217Data r0300Data)) (product q0315Data r0202Data)) (product q0316Data r0201Data)) (product q0317Data r0200Data)) (product q0511Data v0406Data)) (product q0512Data v0405Data)) (product q0513Data v0404Data)) (product q0514Data v0403Data)) (product q0515Data v0402Data)) (product q0516Data v0401Data)) (product q0610Data v0307Data)) (product q0611Data v0306Data)) (product q0612Data v0305Data)) (product q0613Data v0304Data)) (product q0614Data v0303Data)) (product q0615Data v0302Data)) (product q0616Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0217Data r0301Data) (product q0218Data r0300Data)) (product q0316Data r0202Data)) (product q0317Data r0201Data)) (product q0318Data r0200Data)) (product q0512Data v0406Data)) (product q0513Data v0405Data)) (product q0514Data v0404Data)) (product q0515Data v0403Data)) (product q0516Data v0402Data)) (product q0517Data v0401Data)) (product q0611Data v0307Data)) (product q0612Data v0306Data)) (product q0613Data v0305Data)) (product q0614Data v0304Data)) (product q0615Data v0303Data)) (product q0616Data v0302Data)) (product q0617Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0218Data r0301Data) (product q0219Data r0300Data)) (product q0317Data r0202Data)) (product q0318Data r0201Data)) (product q0319Data r0200Data)) (product q0513Data v0406Data)) (product q0514Data v0405Data)) (product q0515Data v0404Data)) (product q0516Data v0403Data)) (product q0517Data v0402Data)) (product q0518Data v0401Data)) (product q0612Data v0307Data)) (product q0613Data v0306Data)) (product q0614Data v0305Data)) (product q0615Data v0304Data)) (product q0616Data v0303Data)) (product q0617Data v0302Data)) (product q0618Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0219Data r0301Data) (product q0220Data r0300Data)) (product q0318Data r0202Data)) (product q0319Data r0201Data)) (product q0320Data r0200Data)) (product q0514Data v0406Data)) (product q0515Data v0405Data)) (product q0516Data v0404Data)) (product q0517Data v0403Data)) (product q0518Data v0402Data)) (product q0519Data v0401Data)) (product q0613Data v0307Data)) (product q0614Data v0306Data)) (product q0615Data v0305Data)) (product q0616Data v0304Data)) (product q0617Data v0303Data)) (product q0618Data v0302Data)) (product q0619Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0220Data r0301Data) (product q0221Data r0300Data)) (product q0319Data r0202Data)) (product q0320Data r0201Data)) (product q0321Data r0200Data)) (product q0515Data v0406Data)) (product q0516Data v0405Data)) (product q0517Data v0404Data)) (product q0518Data v0403Data)) (product q0519Data v0402Data)) (product q0520Data v0401Data)) (product q0614Data v0307Data)) (product q0615Data v0306Data)) (product q0616Data v0305Data)) (product q0617Data v0304Data)) (product q0618Data v0303Data)) (product q0619Data v0302Data)) (product q0620Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0221Data r0301Data) (product q0222Data r0300Data)) (product q0320Data r0202Data)) (product q0321Data r0201Data)) (product q0322Data r0200Data)) (product q0516Data v0406Data)) (product q0517Data v0405Data)) (product q0518Data v0404Data)) (product q0519Data v0403Data)) (product q0520Data v0402Data)) (product q0521Data v0401Data)) (product q0615Data v0307Data)) (product q0616Data v0306Data)) (product q0617Data v0305Data)) (product q0618Data v0304Data)) (product q0619Data v0303Data)) (product q0620Data v0302Data)) (product q0621Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0222Data r0301Data) (product q0223Data r0300Data)) (product q0321Data r0202Data)) (product q0322Data r0201Data)) (product q0323Data r0200Data)) (product q0517Data v0406Data)) (product q0518Data v0405Data)) (product q0519Data v0404Data)) (product q0520Data v0403Data)) (product q0521Data v0402Data)) (product q0522Data v0401Data)) (product q0616Data v0307Data)) (product q0617Data v0306Data)) (product q0618Data v0305Data)) (product q0619Data v0304Data)) (product q0620Data v0303Data)) (product q0621Data v0302Data)) (product q0622Data v0301Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0223Data r0301Data) (product q0224Data r0300Data)) (product q0322Data r0202Data)) (product q0323Data r0201Data)) (product q0324Data r0200Data)) (product q0518Data v0406Data)) (product q0519Data v0405Data)) (product q0520Data v0404Data)) (product q0521Data v0403Data)) (product q0522Data v0402Data)) (product q0523Data v0401Data)) (product q0617Data v0307Data)) (product q0618Data v0306Data)) (product q0619Data v0305Data)) (product q0620Data v0304Data)) (product q0621Data v0303Data)) (product q0622Data v0302Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0224Data r0301Data) (product q0225Data r0300Data)) (product q0323Data r0202Data)) (product q0324Data r0201Data)) (product q0325Data r0200Data)) (product q0519Data v0406Data)) (product q0520Data v0405Data)) (product q0521Data v0404Data)) (product q0522Data v0403Data)) (product q0523Data v0402Data)) (product q0618Data v0307Data)) (product q0619Data v0306Data)) (product q0620Data v0305Data)) (product q0621Data v0304Data)) (product q0622Data v0303Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0225Data r0301Data) (product q0226Data r0300Data)) (product q0324Data r0202Data)) (product q0325Data r0201Data)) (product q0326Data r0200Data)) (product q0520Data v0406Data)) (product q0521Data v0405Data)) (product q0522Data v0404Data)) (product q0523Data v0403Data)) (product q0619Data v0307Data)) (product q0620Data v0306Data)) (product q0621Data v0305Data)) (product q0622Data v0304Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0226Data r0301Data) (product q0227Data r0300Data)) (product q0325Data r0202Data)) (product q0326Data r0201Data)) (product q0327Data r0200Data)) (product q0521Data v0406Data)) (product q0522Data v0405Data)) (product q0523Data v0404Data)) (product q0620Data v0307Data)) (product q0621Data v0306Data)) (product q0622Data v0305Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0227Data r0301Data) (product q0228Data r0300Data)) (product q0326Data r0202Data)) (product q0327Data r0201Data)) (product q0522Data v0406Data)) (product q0523Data v0405Data)) (product q0621Data v0307Data)) (product q0622Data v0306Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0227, q0228, q0326, q0327, q0522, q0523, q0621, q0622, r0201, r0202, r0300, r0301, v0306, v0307, v0405, v0406] using he

#print axioms row5_x28

compact_certificate theorem row5_x29 (y z w : ℂ) :
    q0228 y z w*r0301 y z w +
    q0327 y z w*r0202 y z w +
    q0523 y z w*v0406 y z w +
    q0622 y z w*v0307 y z w=0 := by
  have h : (merge (merge (merge (product q0228Data r0301Data) (product q0327Data r0202Data)) (product q0523Data v0406Data)) (product q0622Data v0307Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0228, q0327, q0523, q0622, r0202, r0301, v0307, v0406] using he

#print axioms row5_x29

compact_certificate theorem row6_x01 (y z w : ℂ) :
    q0301 y z w*r0300 y z w +
    q0600 y z w*v0401 y z w=0 := by
  have h : (merge (product q0301Data r0300Data) (product q0600Data v0401Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0301, q0600, r0300, v0401] using he

#print axioms row6_x01

compact_certificate theorem row6_x02 (y z w : ℂ) :
    q0301 y z w*r0301 y z w +
    q0302 y z w*r0300 y z w +
    q0600 y z w*v0402 y z w +
    q0601 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (product q0301Data r0301Data) (product q0302Data r0300Data)) (product q0600Data v0402Data)) (product q0601Data v0401Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0301, q0302, q0600, q0601, r0300, r0301, v0401, v0402] using he

#print axioms row6_x02

compact_certificate theorem row6_x03 (y z w : ℂ) :
    q0302 y z w*r0301 y z w +
    q0303 y z w*r0300 y z w +
    q0600 y z w*v0403 y z w +
    q0601 y z w*v0402 y z w +
    q0602 y z w*v0401 y z w=0 := by
  have h : (merge (merge (merge (merge (product q0302Data r0301Data) (product q0303Data r0300Data)) (product q0600Data v0403Data)) (product q0601Data v0402Data)) (product q0602Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (product q0303Data r0301Data) (product q0304Data r0300Data)) (product q0600Data v0404Data)) (product q0601Data v0403Data)) (product q0602Data v0402Data)) (product q0603Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (product q0304Data r0301Data) (product q0305Data r0300Data)) (product q0600Data v0405Data)) (product q0601Data v0404Data)) (product q0602Data v0403Data)) (product q0603Data v0402Data)) (product q0604Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0305Data r0301Data) (product q0306Data r0300Data)) (product q0600Data v0406Data)) (product q0601Data v0405Data)) (product q0602Data v0404Data)) (product q0603Data v0403Data)) (product q0604Data v0402Data)) (product q0605Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0306Data r0301Data) (product q0307Data r0300Data)) (product q0601Data v0406Data)) (product q0602Data v0405Data)) (product q0603Data v0404Data)) (product q0604Data v0403Data)) (product q0605Data v0402Data)) (product q0606Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0307Data r0301Data) (product q0308Data r0300Data)) (product q0602Data v0406Data)) (product q0603Data v0405Data)) (product q0604Data v0404Data)) (product q0605Data v0403Data)) (product q0606Data v0402Data)) (product q0607Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0308Data r0301Data) (product q0309Data r0300Data)) (product q0603Data v0406Data)) (product q0604Data v0405Data)) (product q0605Data v0404Data)) (product q0606Data v0403Data)) (product q0607Data v0402Data)) (product q0608Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0309Data r0301Data) (product q0310Data r0300Data)) (product q0604Data v0406Data)) (product q0605Data v0405Data)) (product q0606Data v0404Data)) (product q0607Data v0403Data)) (product q0608Data v0402Data)) (product q0609Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0310Data r0301Data) (product q0311Data r0300Data)) (product q0605Data v0406Data)) (product q0606Data v0405Data)) (product q0607Data v0404Data)) (product q0608Data v0403Data)) (product q0609Data v0402Data)) (product q0610Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0311Data r0301Data) (product q0312Data r0300Data)) (product q0606Data v0406Data)) (product q0607Data v0405Data)) (product q0608Data v0404Data)) (product q0609Data v0403Data)) (product q0610Data v0402Data)) (product q0611Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0312Data r0301Data) (product q0313Data r0300Data)) (product q0607Data v0406Data)) (product q0608Data v0405Data)) (product q0609Data v0404Data)) (product q0610Data v0403Data)) (product q0611Data v0402Data)) (product q0612Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0313Data r0301Data) (product q0314Data r0300Data)) (product q0608Data v0406Data)) (product q0609Data v0405Data)) (product q0610Data v0404Data)) (product q0611Data v0403Data)) (product q0612Data v0402Data)) (product q0613Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0314Data r0301Data) (product q0315Data r0300Data)) (product q0609Data v0406Data)) (product q0610Data v0405Data)) (product q0611Data v0404Data)) (product q0612Data v0403Data)) (product q0613Data v0402Data)) (product q0614Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0315Data r0301Data) (product q0316Data r0300Data)) (product q0610Data v0406Data)) (product q0611Data v0405Data)) (product q0612Data v0404Data)) (product q0613Data v0403Data)) (product q0614Data v0402Data)) (product q0615Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0316Data r0301Data) (product q0317Data r0300Data)) (product q0611Data v0406Data)) (product q0612Data v0405Data)) (product q0613Data v0404Data)) (product q0614Data v0403Data)) (product q0615Data v0402Data)) (product q0616Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0317Data r0301Data) (product q0318Data r0300Data)) (product q0612Data v0406Data)) (product q0613Data v0405Data)) (product q0614Data v0404Data)) (product q0615Data v0403Data)) (product q0616Data v0402Data)) (product q0617Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0318Data r0301Data) (product q0319Data r0300Data)) (product q0613Data v0406Data)) (product q0614Data v0405Data)) (product q0615Data v0404Data)) (product q0616Data v0403Data)) (product q0617Data v0402Data)) (product q0618Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0319Data r0301Data) (product q0320Data r0300Data)) (product q0614Data v0406Data)) (product q0615Data v0405Data)) (product q0616Data v0404Data)) (product q0617Data v0403Data)) (product q0618Data v0402Data)) (product q0619Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0320Data r0301Data) (product q0321Data r0300Data)) (product q0615Data v0406Data)) (product q0616Data v0405Data)) (product q0617Data v0404Data)) (product q0618Data v0403Data)) (product q0619Data v0402Data)) (product q0620Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0321Data r0301Data) (product q0322Data r0300Data)) (product q0616Data v0406Data)) (product q0617Data v0405Data)) (product q0618Data v0404Data)) (product q0619Data v0403Data)) (product q0620Data v0402Data)) (product q0621Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (merge (product q0322Data r0301Data) (product q0323Data r0300Data)) (product q0617Data v0406Data)) (product q0618Data v0405Data)) (product q0619Data v0404Data)) (product q0620Data v0403Data)) (product q0621Data v0402Data)) (product q0622Data v0401Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (merge (product q0323Data r0301Data) (product q0324Data r0300Data)) (product q0618Data v0406Data)) (product q0619Data v0405Data)) (product q0620Data v0404Data)) (product q0621Data v0403Data)) (product q0622Data v0402Data)) = [] := by decide +kernel
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
  have h : (merge (merge (merge (merge (merge (product q0324Data r0301Data) (product q0325Data r0300Data)) (product q0619Data v0406Data)) (product q0620Data v0405Data)) (product q0621Data v0404Data)) (product q0622Data v0403Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0324, q0325, q0619, q0620, q0621, q0622, r0300, r0301, v0403, v0404, v0405, v0406] using he

#print axioms row6_x25

compact_certificate theorem row6_x26 (y z w : ℂ) :
    q0325 y z w*r0301 y z w +
    q0326 y z w*r0300 y z w +
    q0620 y z w*v0406 y z w +
    q0621 y z w*v0405 y z w +
    q0622 y z w*v0404 y z w=0 := by
  have h : (merge (merge (merge (merge (product q0325Data r0301Data) (product q0326Data r0300Data)) (product q0620Data v0406Data)) (product q0621Data v0405Data)) (product q0622Data v0404Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0325, q0326, q0620, q0621, q0622, r0300, r0301, v0404, v0405, v0406] using he

#print axioms row6_x26

compact_certificate theorem row6_x27 (y z w : ℂ) :
    q0326 y z w*r0301 y z w +
    q0327 y z w*r0300 y z w +
    q0621 y z w*v0406 y z w +
    q0622 y z w*v0405 y z w=0 := by
  have h : (merge (merge (merge (product q0326Data r0301Data) (product q0327Data r0300Data)) (product q0621Data v0406Data)) (product q0622Data v0405Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0326, q0327, q0621, q0622, r0300, r0301, v0405, v0406] using he

#print axioms row6_x27

compact_certificate theorem row6_x28 (y z w : ℂ) :
    q0327 y z w*r0301 y z w +
    q0622 y z w*v0406 y z w=0 := by
  have h : (merge (product q0327Data r0301Data) (product q0622Data v0406Data)) = [] := by decide +kernel
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0327, q0622, r0301, v0406] using he

#print axioms row6_x28

compact_certificate theorem row1_x35 (_y _z _w : ℂ) : (0:ℂ)=0 := rfl
#print axioms row1_x35

compact_certificate theorem row4_x35 (_y _z _w : ℂ) : (0:ℂ)=0 := rfl
#print axioms row4_x35

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

end SmallLevelTwentySixResultantBatchedMMM
end
end

/-! ## SmallLevelTwentySixResultantBatchedMMMRowIndexIdentitySeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixResultantBatchedMMM
open Complex Polynomial SmallLevelPolynomialCoefficientAssembly
open SmallLevelTwentySixResultantCoefficientsMMM
open scoped Classical
theorem row1_identity (y z w : ℂ) : rowPoly1 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly1_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using row1_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using row1_coefficient35 y z w

#print axioms row1_identity
end SmallLevelTwentySixResultantBatchedMMM
end

section
set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixResultantBatchedMMM
open Complex Polynomial SmallLevelPolynomialCoefficientAssembly
open SmallLevelTwentySixResultantCoefficientsMMM
open scoped Classical
theorem row2_identity (y z w : ℂ) : rowPoly2 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly2_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using row2_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using row2_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row2_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row2_coefficient35 y z w

#print axioms row2_identity
end SmallLevelTwentySixResultantBatchedMMM
end

section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixResultantBatchedMMM
open Complex Polynomial SmallLevelPolynomialCoefficientAssembly
open SmallLevelTwentySixResultantCoefficientsMMM
open scoped Classical
theorem row3_identity (y z w : ℂ) : rowPoly3 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly3_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using row3_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using row3_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row3_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row3_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row3_coefficient35 y z w

#print axioms row3_identity

theorem row4_identity (y z w : ℂ) : rowPoly4 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly4_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using row4_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row4_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row4_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row4_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row4_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using row4_coefficient35 y z w

#print axioms row4_identity

theorem row5_identity (y z w : ℂ) : rowPoly5 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly5_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using row5_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row5_coefficient35 y z w

#print axioms row5_identity

theorem row6_identity (y z w : ℂ) : rowPoly6 y z w=0 := by
  apply eq_of_bounded_coefficients _ _ 36
    (rowPoly6_bound y z w) (by norm_num)
  intro i
  fin_cases i
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient00 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient01 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient02 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient03 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient04 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient05 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient06 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient07 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient08 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient09 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient10 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient11 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient12 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient13 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient14 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient15 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient16 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient17 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient18 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient19 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient20 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient21 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient22 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient23 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient24 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient25 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient26 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient27 y z w
  · simpa only [Polynomial.coeff_zero] using row6_coefficient28 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient29 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient30 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient31 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient32 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient33 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient34 y z w
  · simpa only [Polynomial.coeff_zero] using SmallLevelTwentySixResultantBatchedMMMZeroGrouped.row6_coefficient35 y z w

#print axioms row6_identity
end SmallLevelTwentySixResultantBatchedMMM
end
end
end

/-! ## SmallLevelTwentySixResultantBatchedMMMCompleteV1 -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
@[expose] public noncomputable section
namespace SmallLevelTwentySixResultantBatchedMMM
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open SmallLevelTwentySixResultantCoefficientsMMM

theorem resultant_zero (x y z w a : ℂ)
    (hr : SmallLevelTwentySixUnitMMM.WeightResultants.r x y z w a 0 0=0)
    (hv : SmallLevelTwentySixUnitMMM.WeightResultants.v x y z w a 0 0=0) :
    eval x y z w 1 SmallLevelTwentySixWeightAbelMMM.terms=0 := by
  have h0 := congrArg (Polynomial.eval x) (row0_identity y z w)
  simp only [rowPoly0,Polynomial.eval_add,Polynomial.eval_mul] at h0
  have h1 := congrArg (Polynomial.eval x) (row1_identity y z w)
  simp only [rowPoly1,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h1
  have h2 := congrArg (Polynomial.eval x) (row2_identity y z w)
  simp only [rowPoly2,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h2
  have h3 := congrArg (Polynomial.eval x) (row3_identity y z w)
  simp only [rowPoly3,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h3
  have h4 := congrArg (Polynomial.eval x) (row4_identity y z w)
  simp only [rowPoly4,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h4
  have h5 := congrArg (Polynomial.eval x) (row5_identity y z w)
  simp only [rowPoly5,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h5
  have h6 := congrArg (Polynomial.eval x) (row6_identity y z w)
  simp only [rowPoly6,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_zero] at h6
  have hd := SmallLevelCubicQuarticSylvester.resultant_zero
    ((rPoly0 y z w).eval x) ((rPoly1 y z w).eval x) ((rPoly2 y z w).eval x) ((rPoly3 y z w).eval x)
    ((vPoly0 y z w).eval x) ((vPoly1 y z w).eval x) ((vPoly2 y z w).eval x) ((vPoly3 y z w).eval x)
    ((vPoly4 y z w).eval x) ((qPoly0 y z w).eval x) ((qPoly1 y z w).eval x) ((qPoly2 y z w).eval x)
    ((qPoly3 y z w).eval x) ((qPoly4 y z w).eval x) ((qPoly5 y z w).eval x) ((qPoly6 y z w).eval x)
    ((dPoly0 y z w).eval x) a
    h0 h1 h2 h3 h4 h5 h6
    ((r_evaluation x y z w a).trans hr) ((v_evaluation x y z w a).trans hv)
  rw [d_eval_eq_abel] at hd
  exact hd

#print axioms resultant_zero
end SmallLevelTwentySixResultantBatchedMMM
end
end
