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
/-! ## SmallLevelTwentySixResultantCoefficientsMMMAbelBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 131072
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixResultantCoefficientsMMM
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open SmallLevelSparseCoefficientPartition SmallLevelSparsePolynomialNormalize

theorem slice00_checked : normalize 8 (slice 0 SmallLevelTwentySixWeightAbelMMM.terms)=d00Data := by sliced_sparse_certificate

theorem slice00_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 0 SmallLevelTwentySixWeightAbelMMM.terms)=d00 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 0 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d00 y z w := congrArg (eval y z w 1 1) slice00_checked


theorem slice01_checked : normalize 8 (slice 1 SmallLevelTwentySixWeightAbelMMM.terms)=d01Data := by sliced_sparse_certificate

theorem slice01_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 1 SmallLevelTwentySixWeightAbelMMM.terms)=d01 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 1 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d01 y z w := congrArg (eval y z w 1 1) slice01_checked


theorem slice02_checked : normalize 8 (slice 2 SmallLevelTwentySixWeightAbelMMM.terms)=d02Data := by sliced_sparse_certificate

theorem slice02_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 2 SmallLevelTwentySixWeightAbelMMM.terms)=d02 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 2 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d02 y z w := congrArg (eval y z w 1 1) slice02_checked


theorem slice03_checked : normalize 8 (slice 3 SmallLevelTwentySixWeightAbelMMM.terms)=d03Data := by sliced_sparse_certificate

theorem slice03_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 3 SmallLevelTwentySixWeightAbelMMM.terms)=d03 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 3 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d03 y z w := congrArg (eval y z w 1 1) slice03_checked


theorem slice04_checked : normalize 8 (slice 4 SmallLevelTwentySixWeightAbelMMM.terms)=d04Data := by sliced_sparse_certificate

theorem slice04_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 4 SmallLevelTwentySixWeightAbelMMM.terms)=d04 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 4 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d04 y z w := congrArg (eval y z w 1 1) slice04_checked


theorem slice05_checked : normalize 8 (slice 5 SmallLevelTwentySixWeightAbelMMM.terms)=d05Data := by sliced_sparse_certificate

theorem slice05_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 5 SmallLevelTwentySixWeightAbelMMM.terms)=d05 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 5 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d05 y z w := congrArg (eval y z w 1 1) slice05_checked


theorem slice06_checked : normalize 8 (slice 6 SmallLevelTwentySixWeightAbelMMM.terms)=d06Data := by sliced_sparse_certificate

theorem slice06_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 6 SmallLevelTwentySixWeightAbelMMM.terms)=d06 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 6 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d06 y z w := congrArg (eval y z w 1 1) slice06_checked


theorem slice07_checked : normalize 8 (slice 7 SmallLevelTwentySixWeightAbelMMM.terms)=d07Data := by sliced_sparse_certificate

theorem slice07_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 7 SmallLevelTwentySixWeightAbelMMM.terms)=d07 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 7 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d07 y z w := congrArg (eval y z w 1 1) slice07_checked


theorem slice08_checked : normalize 8 (slice 8 SmallLevelTwentySixWeightAbelMMM.terms)=d08Data := by sliced_sparse_certificate

theorem slice08_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 8 SmallLevelTwentySixWeightAbelMMM.terms)=d08 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 8 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d08 y z w := congrArg (eval y z w 1 1) slice08_checked


theorem slice09_checked : normalize 8 (slice 9 SmallLevelTwentySixWeightAbelMMM.terms)=d09Data := by sliced_sparse_certificate

theorem slice09_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 9 SmallLevelTwentySixWeightAbelMMM.terms)=d09 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 9 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d09 y z w := congrArg (eval y z w 1 1) slice09_checked


theorem slice10_checked : normalize 8 (slice 10 SmallLevelTwentySixWeightAbelMMM.terms)=d10Data := by sliced_sparse_certificate

theorem slice10_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 10 SmallLevelTwentySixWeightAbelMMM.terms)=d10 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 10 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d10 y z w := congrArg (eval y z w 1 1) slice10_checked


theorem slice11_checked : normalize 8 (slice 11 SmallLevelTwentySixWeightAbelMMM.terms)=d11Data := by sliced_sparse_certificate

theorem slice11_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 11 SmallLevelTwentySixWeightAbelMMM.terms)=d11 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 11 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d11 y z w := congrArg (eval y z w 1 1) slice11_checked


theorem slice12_checked : normalize 8 (slice 12 SmallLevelTwentySixWeightAbelMMM.terms)=d12Data := by sliced_sparse_certificate

theorem slice12_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 12 SmallLevelTwentySixWeightAbelMMM.terms)=d12 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 12 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d12 y z w := congrArg (eval y z w 1 1) slice12_checked


theorem slice13_checked : normalize 8 (slice 13 SmallLevelTwentySixWeightAbelMMM.terms)=d13Data := by sliced_sparse_certificate

theorem slice13_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 13 SmallLevelTwentySixWeightAbelMMM.terms)=d13 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 13 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d13 y z w := congrArg (eval y z w 1 1) slice13_checked


theorem slice14_checked : normalize 8 (slice 14 SmallLevelTwentySixWeightAbelMMM.terms)=d14Data := by sliced_sparse_certificate

theorem slice14_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 14 SmallLevelTwentySixWeightAbelMMM.terms)=d14 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 14 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d14 y z w := congrArg (eval y z w 1 1) slice14_checked


theorem slice15_checked : normalize 8 (slice 15 SmallLevelTwentySixWeightAbelMMM.terms)=d15Data := by sliced_sparse_certificate

theorem slice15_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 15 SmallLevelTwentySixWeightAbelMMM.terms)=d15 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 15 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d15 y z w := congrArg (eval y z w 1 1) slice15_checked


theorem slice16_checked : normalize 8 (slice 16 SmallLevelTwentySixWeightAbelMMM.terms)=d16Data := by sliced_sparse_certificate

theorem slice16_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 16 SmallLevelTwentySixWeightAbelMMM.terms)=d16 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 16 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d16 y z w := congrArg (eval y z w 1 1) slice16_checked


theorem slice17_checked : normalize 8 (slice 17 SmallLevelTwentySixWeightAbelMMM.terms)=d17Data := by sliced_sparse_certificate

theorem slice17_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 17 SmallLevelTwentySixWeightAbelMMM.terms)=d17 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 17 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d17 y z w := congrArg (eval y z w 1 1) slice17_checked


theorem slice18_checked : normalize 8 (slice 18 SmallLevelTwentySixWeightAbelMMM.terms)=d18Data := by sliced_sparse_certificate

theorem slice18_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 18 SmallLevelTwentySixWeightAbelMMM.terms)=d18 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 18 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d18 y z w := congrArg (eval y z w 1 1) slice18_checked


theorem slice19_checked : normalize 8 (slice 19 SmallLevelTwentySixWeightAbelMMM.terms)=d19Data := by sliced_sparse_certificate

theorem slice19_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 19 SmallLevelTwentySixWeightAbelMMM.terms)=d19 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 19 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d19 y z w := congrArg (eval y z w 1 1) slice19_checked


theorem slice20_checked : normalize 8 (slice 20 SmallLevelTwentySixWeightAbelMMM.terms)=d20Data := by sliced_sparse_certificate

theorem slice20_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 20 SmallLevelTwentySixWeightAbelMMM.terms)=d20 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 20 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d20 y z w := congrArg (eval y z w 1 1) slice20_checked


theorem slice21_checked : normalize 8 (slice 21 SmallLevelTwentySixWeightAbelMMM.terms)=d21Data := by sliced_sparse_certificate

theorem slice21_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 21 SmallLevelTwentySixWeightAbelMMM.terms)=d21 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 21 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d21 y z w := congrArg (eval y z w 1 1) slice21_checked


theorem slice22_checked : normalize 8 (slice 22 SmallLevelTwentySixWeightAbelMMM.terms)=d22Data := by sliced_sparse_certificate

theorem slice22_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 22 SmallLevelTwentySixWeightAbelMMM.terms)=d22 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 22 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d22 y z w := congrArg (eval y z w 1 1) slice22_checked


theorem slice23_checked : normalize 8 (slice 23 SmallLevelTwentySixWeightAbelMMM.terms)=d23Data := by sliced_sparse_certificate

theorem slice23_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 23 SmallLevelTwentySixWeightAbelMMM.terms)=d23 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 23 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d23 y z w := congrArg (eval y z w 1 1) slice23_checked


theorem slice24_checked : normalize 8 (slice 24 SmallLevelTwentySixWeightAbelMMM.terms)=d24Data := by sliced_sparse_certificate

theorem slice24_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 24 SmallLevelTwentySixWeightAbelMMM.terms)=d24 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 24 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d24 y z w := congrArg (eval y z w 1 1) slice24_checked


theorem slice25_checked : normalize 8 (slice 25 SmallLevelTwentySixWeightAbelMMM.terms)=d25Data := by sliced_sparse_certificate

theorem slice25_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 25 SmallLevelTwentySixWeightAbelMMM.terms)=d25 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 25 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d25 y z w := congrArg (eval y z w 1 1) slice25_checked


theorem slice26_checked : normalize 8 (slice 26 SmallLevelTwentySixWeightAbelMMM.terms)=d26Data := by sliced_sparse_certificate

theorem slice26_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 26 SmallLevelTwentySixWeightAbelMMM.terms)=d26 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 26 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d26 y z w := congrArg (eval y z w 1 1) slice26_checked


theorem slice27_checked : normalize 8 (slice 27 SmallLevelTwentySixWeightAbelMMM.terms)=d27Data := by sliced_sparse_certificate

theorem slice27_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 27 SmallLevelTwentySixWeightAbelMMM.terms)=d27 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 27 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d27 y z w := congrArg (eval y z w 1 1) slice27_checked


theorem slice28_checked : normalize 8 (slice 28 SmallLevelTwentySixWeightAbelMMM.terms)=d28Data := by sliced_sparse_certificate

theorem slice28_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 28 SmallLevelTwentySixWeightAbelMMM.terms)=d28 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 28 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d28 y z w := congrArg (eval y z w 1 1) slice28_checked


theorem slice29_checked : normalize 8 (slice 29 SmallLevelTwentySixWeightAbelMMM.terms)=d29Data := by sliced_sparse_certificate

theorem slice29_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 29 SmallLevelTwentySixWeightAbelMMM.terms)=d29 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 29 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d29 y z w := congrArg (eval y z w 1 1) slice29_checked


theorem slice30_checked : normalize 8 (slice 30 SmallLevelTwentySixWeightAbelMMM.terms)=d30Data := by sliced_sparse_certificate

theorem slice30_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 30 SmallLevelTwentySixWeightAbelMMM.terms)=d30 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 30 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d30 y z w := congrArg (eval y z w 1 1) slice30_checked


theorem slice31_checked : normalize 8 (slice 31 SmallLevelTwentySixWeightAbelMMM.terms)=d31Data := by sliced_sparse_certificate

theorem slice31_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 31 SmallLevelTwentySixWeightAbelMMM.terms)=d31 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 31 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d31 y z w := congrArg (eval y z w 1 1) slice31_checked


theorem slice32_checked : normalize 8 (slice 32 SmallLevelTwentySixWeightAbelMMM.terms)=d32Data := by sliced_sparse_certificate

theorem slice32_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 32 SmallLevelTwentySixWeightAbelMMM.terms)=d32 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 32 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d32 y z w := congrArg (eval y z w 1 1) slice32_checked


theorem slice33_checked : normalize 8 (slice 33 SmallLevelTwentySixWeightAbelMMM.terms)=d33Data := by sliced_sparse_certificate

theorem slice33_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 33 SmallLevelTwentySixWeightAbelMMM.terms)=d33 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 33 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d33 y z w := congrArg (eval y z w 1 1) slice33_checked


theorem slice34_checked : normalize 8 (slice 34 SmallLevelTwentySixWeightAbelMMM.terms)=d34Data := by sliced_sparse_certificate

theorem slice34_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 34 SmallLevelTwentySixWeightAbelMMM.terms)=d34 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 34 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d34 y z w := congrArg (eval y z w 1 1) slice34_checked


theorem slice35_checked : normalize 8 (slice 35 SmallLevelTwentySixWeightAbelMMM.terms)=d35Data := by sliced_sparse_certificate

theorem slice35_eval (y z w : ℂ) :
    eval y z w 1 1 (slice 35 SmallLevelTwentySixWeightAbelMMM.terms)=d35 y z w := by
  calc
    _=eval y z w 1 1 (normalize 8 (slice 35 SmallLevelTwentySixWeightAbelMMM.terms)) :=
      (eval_normalize y z w 1 1 8 _).symm
    _=d35 y z w := congrArg (eval y z w 1 1) slice35_checked


end SmallLevelTwentySixResultantCoefficientsMMM
end
end


}
