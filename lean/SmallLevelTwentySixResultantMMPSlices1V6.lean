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

theorem slice12_checked : normalize 8 (slice 12 SmallLevelTwentySixWeightAbelMMP.terms)=d12Data := by sliced_sparse_certificate

theorem slice12_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 12 SmallLevelTwentySixWeightAbelMMP.terms)=d12 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 12 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d12 y z w := congrArg (eval y z w 1 1) slice12_checked

#print axioms slice12_eval

theorem slice13_checked : normalize 8 (slice 13 SmallLevelTwentySixWeightAbelMMP.terms)=d13Data := by sliced_sparse_certificate

theorem slice13_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 13 SmallLevelTwentySixWeightAbelMMP.terms)=d13 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 13 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d13 y z w := congrArg (eval y z w 1 1) slice13_checked

#print axioms slice13_eval

theorem slice14_checked : normalize 8 (slice 14 SmallLevelTwentySixWeightAbelMMP.terms)=d14Data := by sliced_sparse_certificate

theorem slice14_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 14 SmallLevelTwentySixWeightAbelMMP.terms)=d14 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 14 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d14 y z w := congrArg (eval y z w 1 1) slice14_checked

#print axioms slice14_eval

theorem slice15_checked : normalize 8 (slice 15 SmallLevelTwentySixWeightAbelMMP.terms)=d15Data := by sliced_sparse_certificate

theorem slice15_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 15 SmallLevelTwentySixWeightAbelMMP.terms)=d15 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 15 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d15 y z w := congrArg (eval y z w 1 1) slice15_checked

#print axioms slice15_eval

theorem slice16_checked : normalize 8 (slice 16 SmallLevelTwentySixWeightAbelMMP.terms)=d16Data := by sliced_sparse_certificate

theorem slice16_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 16 SmallLevelTwentySixWeightAbelMMP.terms)=d16 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 16 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d16 y z w := congrArg (eval y z w 1 1) slice16_checked

#print axioms slice16_eval

theorem slice17_checked : normalize 8 (slice 17 SmallLevelTwentySixWeightAbelMMP.terms)=d17Data := by sliced_sparse_certificate

theorem slice17_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 17 SmallLevelTwentySixWeightAbelMMP.terms)=d17 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 17 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d17 y z w := congrArg (eval y z w 1 1) slice17_checked

#print axioms slice17_eval

theorem slice18_checked : normalize 8 (slice 18 SmallLevelTwentySixWeightAbelMMP.terms)=d18Data := by sliced_sparse_certificate

theorem slice18_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 18 SmallLevelTwentySixWeightAbelMMP.terms)=d18 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 18 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d18 y z w := congrArg (eval y z w 1 1) slice18_checked

#print axioms slice18_eval

theorem slice19_checked : normalize 8 (slice 19 SmallLevelTwentySixWeightAbelMMP.terms)=d19Data := by sliced_sparse_certificate

theorem slice19_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 19 SmallLevelTwentySixWeightAbelMMP.terms)=d19 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 19 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d19 y z w := congrArg (eval y z w 1 1) slice19_checked

#print axioms slice19_eval

theorem slice20_checked : normalize 8 (slice 20 SmallLevelTwentySixWeightAbelMMP.terms)=d20Data := by sliced_sparse_certificate

theorem slice20_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 20 SmallLevelTwentySixWeightAbelMMP.terms)=d20 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 20 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d20 y z w := congrArg (eval y z w 1 1) slice20_checked

#print axioms slice20_eval

theorem slice21_checked : normalize 8 (slice 21 SmallLevelTwentySixWeightAbelMMP.terms)=d21Data := by sliced_sparse_certificate

theorem slice21_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 21 SmallLevelTwentySixWeightAbelMMP.terms)=d21 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 21 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d21 y z w := congrArg (eval y z w 1 1) slice21_checked

#print axioms slice21_eval

theorem slice22_checked : normalize 8 (slice 22 SmallLevelTwentySixWeightAbelMMP.terms)=d22Data := by sliced_sparse_certificate

theorem slice22_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 22 SmallLevelTwentySixWeightAbelMMP.terms)=d22 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 22 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d22 y z w := congrArg (eval y z w 1 1) slice22_checked

#print axioms slice22_eval

theorem slice23_checked : normalize 8 (slice 23 SmallLevelTwentySixWeightAbelMMP.terms)=d23Data := by sliced_sparse_certificate

theorem slice23_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 23 SmallLevelTwentySixWeightAbelMMP.terms)=d23 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 23 SmallLevelTwentySixWeightAbelMMP.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d23 y z w := congrArg (eval y z w 1 1) slice23_checked

#print axioms slice23_eval

end SmallLevelTwentySixResultantCoefficientsMMP
end
end


}
