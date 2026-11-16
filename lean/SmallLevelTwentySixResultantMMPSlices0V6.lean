module

public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import SmallLevelPolynomialCoefficientAssemblyV1
public import SmallLevelSparseCoefficientAssemblyV1
public import SmallLevelSparseCoefficientPartitionV1
public import SmallLevelTwentySixUnitMMPWeightResultantsTheoryV4
public import SmallLevelTwentySixWeightAbelMMPDataV1
public import SmallLevelTwentySixResultantMMPDataV6
public meta import QuantitativeArithmeticSparseCertificateComputeV5
public meta import SmallLevelCertificateBatchCommandV1
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
certificate_batch {
/-! ## SmallLevelTwentySixResultantCoefficientsMMPAbelBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 131072
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixResultantCoefficientsMMP
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open SmallLevelSparseCoefficientPartition SmallLevelSparsePolynomialNormalize

theorem slice00_checked : normalize 8 (slice 0 SmallLevelTwentySixWeightAbelMMP.terms)=d00Data := by sliced_sparse_certificate

theorem slice00_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 0 SmallLevelTwentySixWeightAbelMMP.terms)=d00 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 0 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d00 y z w := congrArg (eval y z w 1 1) slice00_checked

#print axioms slice00_eval

theorem slice01_checked : normalize 8 (slice 1 SmallLevelTwentySixWeightAbelMMP.terms)=d01Data := by sliced_sparse_certificate

theorem slice01_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 1 SmallLevelTwentySixWeightAbelMMP.terms)=d01 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 1 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d01 y z w := congrArg (eval y z w 1 1) slice01_checked

#print axioms slice01_eval

theorem slice02_checked : normalize 8 (slice 2 SmallLevelTwentySixWeightAbelMMP.terms)=d02Data := by sliced_sparse_certificate

theorem slice02_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 2 SmallLevelTwentySixWeightAbelMMP.terms)=d02 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 2 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d02 y z w := congrArg (eval y z w 1 1) slice02_checked

#print axioms slice02_eval

theorem slice03_checked : normalize 8 (slice 3 SmallLevelTwentySixWeightAbelMMP.terms)=d03Data := by sliced_sparse_certificate

theorem slice03_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 3 SmallLevelTwentySixWeightAbelMMP.terms)=d03 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 3 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d03 y z w := congrArg (eval y z w 1 1) slice03_checked

#print axioms slice03_eval

theorem slice04_checked : normalize 8 (slice 4 SmallLevelTwentySixWeightAbelMMP.terms)=d04Data := by sliced_sparse_certificate

theorem slice04_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 4 SmallLevelTwentySixWeightAbelMMP.terms)=d04 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 4 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d04 y z w := congrArg (eval y z w 1 1) slice04_checked

#print axioms slice04_eval

theorem slice05_checked : normalize 8 (slice 5 SmallLevelTwentySixWeightAbelMMP.terms)=d05Data := by sliced_sparse_certificate

theorem slice05_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 5 SmallLevelTwentySixWeightAbelMMP.terms)=d05 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 5 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d05 y z w := congrArg (eval y z w 1 1) slice05_checked

#print axioms slice05_eval

theorem slice06_checked : normalize 8 (slice 6 SmallLevelTwentySixWeightAbelMMP.terms)=d06Data := by sliced_sparse_certificate

theorem slice06_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 6 SmallLevelTwentySixWeightAbelMMP.terms)=d06 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 6 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d06 y z w := congrArg (eval y z w 1 1) slice06_checked

#print axioms slice06_eval

theorem slice07_checked : normalize 8 (slice 7 SmallLevelTwentySixWeightAbelMMP.terms)=d07Data := by sliced_sparse_certificate

theorem slice07_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 7 SmallLevelTwentySixWeightAbelMMP.terms)=d07 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 7 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d07 y z w := congrArg (eval y z w 1 1) slice07_checked

#print axioms slice07_eval

theorem slice08_checked : normalize 8 (slice 8 SmallLevelTwentySixWeightAbelMMP.terms)=d08Data := by sliced_sparse_certificate

theorem slice08_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 8 SmallLevelTwentySixWeightAbelMMP.terms)=d08 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 8 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d08 y z w := congrArg (eval y z w 1 1) slice08_checked

#print axioms slice08_eval

theorem slice09_checked : normalize 8 (slice 9 SmallLevelTwentySixWeightAbelMMP.terms)=d09Data := by sliced_sparse_certificate

theorem slice09_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 9 SmallLevelTwentySixWeightAbelMMP.terms)=d09 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 9 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d09 y z w := congrArg (eval y z w 1 1) slice09_checked

#print axioms slice09_eval

theorem slice10_checked : normalize 8 (slice 10 SmallLevelTwentySixWeightAbelMMP.terms)=d10Data := by sliced_sparse_certificate

theorem slice10_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 10 SmallLevelTwentySixWeightAbelMMP.terms)=d10 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 10 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d10 y z w := congrArg (eval y z w 1 1) slice10_checked

#print axioms slice10_eval

theorem slice11_checked : normalize 8 (slice 11 SmallLevelTwentySixWeightAbelMMP.terms)=d11Data := by sliced_sparse_certificate

theorem slice11_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 11 SmallLevelTwentySixWeightAbelMMP.terms)=d11 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 11 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d11 y z w := congrArg (eval y z w 1 1) slice11_checked

#print axioms slice11_eval

end SmallLevelTwentySixResultantCoefficientsMMP
end
end


}
