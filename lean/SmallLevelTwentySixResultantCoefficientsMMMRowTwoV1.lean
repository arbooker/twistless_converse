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
  have h : (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (merge (product q0008Data r0202Data) (product q0009Data r0201Data)) (product q0010Data r0200Data)) (product q0107Data r0103Data)) (product q0108Data r0102Data)) (product q0109Data r0101Data)) (product q0110Data r0100Data)) (product q0205Data r0005Data)) (product q0207Data r0003Data)) (product q0208Data r0002Data)) (product q0209Data r0001Data)) (product q0210Data r0000Data)) (product q0402Data v0208Data)) (product q0403Data v0207Data)) (product q0404Data v0206Data)) (product q0405Data v0205Data)) (product q0406Data v0204Data)) (product q0407Data v0203Data)) (product q0408Data v0202Data)) (product q0409Data v0201Data)) (product q0410Data v0200Data)) (product q0500Data v0110Data)) (product q0501Data v0109Data)) (product q0502Data v0108Data)) (product q0503Data v0107Data)) (product q0504Data v0106Data)) (product q0505Data v0105Data)) (product q0506Data v0104Data)) (product q0507Data v0103Data)) (product q0508Data v0102Data)) (product q0509Data v0101Data)) (product q0510Data v0100Data)) (product q0600Data v0010Data)) (product q0601Data v0009Data)) (product q0602Data v0008Data)) (product q0603Data v0007Data)) (product q0604Data v0006Data)) (product q0605Data v0005Data)) (product q0606Data v0004Data)) (product q0607Data v0003Data)) (product q0608Data v0002Data)) (product q0609Data v0001Data)) (product q0610Data v0000Data)) = [] := by bounded_sparse_certificate
  have he := eval_of_eq y z w 1 1 _ _ h
  simpa only [eval_merge, eval_product, eval_nil, q0008, q0009, q0010, q0107, q0108, q0109, q0110, q0205, q0207, q0208, q0209, q0210, q0402, q0403, q0404, q0405, q0406, q0407, q0408, q0409, q0410, q0500, q0501, q0502, q0503, q0504, q0505, q0506, q0507, q0508, q0509, q0510, q0600, q0601, q0602, q0603, q0604, q0605, q0606, q0607, q0608, q0609, q0610, r0000, r0001, r0002, r0003, r0005, r0100, r0101, r0102, r0103, r0200, r0201, r0202, v0000, v0001, v0002, v0003, v0004, v0005, v0006, v0007, v0008, v0009, v0010, v0100, v0101, v0102, v0103, v0104, v0105, v0106, v0107, v0108, v0109, v0110, v0200, v0201, v0202, v0203, v0204, v0205, v0206, v0207, v0208] using he


end SmallLevelTwentySixResultantCoefficientsMMM
end
end

}
