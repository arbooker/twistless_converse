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

theorem slice24_checked : normalize 8 (slice 24 SmallLevelTwentySixWeightAbelMMP.terms)=d24Data := by sliced_sparse_certificate

theorem slice24_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 24 SmallLevelTwentySixWeightAbelMMP.terms)=d24 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 24 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d24 y z w := congrArg (eval y z w 1 1) slice24_checked

#print axioms slice24_eval

theorem slice25_checked : normalize 8 (slice 25 SmallLevelTwentySixWeightAbelMMP.terms)=d25Data := by sliced_sparse_certificate

theorem slice25_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 25 SmallLevelTwentySixWeightAbelMMP.terms)=d25 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 25 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d25 y z w := congrArg (eval y z w 1 1) slice25_checked

#print axioms slice25_eval

theorem slice26_checked : normalize 8 (slice 26 SmallLevelTwentySixWeightAbelMMP.terms)=d26Data := by sliced_sparse_certificate

theorem slice26_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 26 SmallLevelTwentySixWeightAbelMMP.terms)=d26 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 26 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d26 y z w := congrArg (eval y z w 1 1) slice26_checked

#print axioms slice26_eval

theorem slice27_checked : normalize 8 (slice 27 SmallLevelTwentySixWeightAbelMMP.terms)=d27Data := by sliced_sparse_certificate

theorem slice27_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 27 SmallLevelTwentySixWeightAbelMMP.terms)=d27 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 27 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d27 y z w := congrArg (eval y z w 1 1) slice27_checked

#print axioms slice27_eval

theorem slice28_checked : normalize 8 (slice 28 SmallLevelTwentySixWeightAbelMMP.terms)=d28Data := by sliced_sparse_certificate

theorem slice28_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 28 SmallLevelTwentySixWeightAbelMMP.terms)=d28 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 28 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d28 y z w := congrArg (eval y z w 1 1) slice28_checked

#print axioms slice28_eval

theorem slice29_checked : normalize 8 (slice 29 SmallLevelTwentySixWeightAbelMMP.terms)=d29Data := by sliced_sparse_certificate

theorem slice29_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 29 SmallLevelTwentySixWeightAbelMMP.terms)=d29 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 29 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d29 y z w := congrArg (eval y z w 1 1) slice29_checked

#print axioms slice29_eval

theorem slice30_checked : normalize 8 (slice 30 SmallLevelTwentySixWeightAbelMMP.terms)=d30Data := by sliced_sparse_certificate

theorem slice30_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 30 SmallLevelTwentySixWeightAbelMMP.terms)=d30 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 30 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d30 y z w := congrArg (eval y z w 1 1) slice30_checked

#print axioms slice30_eval

theorem slice31_checked : normalize 8 (slice 31 SmallLevelTwentySixWeightAbelMMP.terms)=d31Data := by sliced_sparse_certificate

theorem slice31_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 31 SmallLevelTwentySixWeightAbelMMP.terms)=d31 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 31 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d31 y z w := congrArg (eval y z w 1 1) slice31_checked

#print axioms slice31_eval

theorem slice32_checked : normalize 8 (slice 32 SmallLevelTwentySixWeightAbelMMP.terms)=d32Data := by sliced_sparse_certificate

theorem slice32_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 32 SmallLevelTwentySixWeightAbelMMP.terms)=d32 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 32 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d32 y z w := congrArg (eval y z w 1 1) slice32_checked

#print axioms slice32_eval

theorem slice33_checked : normalize 8 (slice 33 SmallLevelTwentySixWeightAbelMMP.terms)=d33Data := by sliced_sparse_certificate

theorem slice33_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 33 SmallLevelTwentySixWeightAbelMMP.terms)=d33 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 33 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d33 y z w := congrArg (eval y z w 1 1) slice33_checked

#print axioms slice33_eval

theorem slice34_checked : normalize 8 (slice 34 SmallLevelTwentySixWeightAbelMMP.terms)=d34Data := by sliced_sparse_certificate

theorem slice34_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 34 SmallLevelTwentySixWeightAbelMMP.terms)=d34 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 34 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d34 y z w := congrArg (eval y z w 1 1) slice34_checked

#print axioms slice34_eval

theorem slice35_checked : normalize 8 (slice 35 SmallLevelTwentySixWeightAbelMMP.terms)=d35Data := by sliced_sparse_certificate

theorem slice35_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 35 SmallLevelTwentySixWeightAbelMMP.terms)=d35 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 35 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d35 y z w := congrArg (eval y z w 1 1) slice35_checked

#print axioms slice35_eval

end SmallLevelTwentySixResultantCoefficientsMMP
end
end


}
