module

public import SmallLevelTwentySixGermPrimitiveSparseMMMFamilyV4
public import SmallLevelTwentySixPariCompactInitialIndexBindingSeriesV4
public import SmallLevelTwentySixPariIdentityFamilyV4
public import SmallLevelTwentySixPariSourcePivotFamilyV4
public import SmallLevelTwentySixPariSourcePivotIndexDataSeriesV4
public import SmallLevelTwentySixPariSourcePivotsTheoryV4
public import SmallLevelTwentySixPariSourcePolynomial87V1
public import SmallLevelTwentySixPariSourcePolynomialIndexDataSeriesV4
public import SmallLevelTwentySixPariSourceW87TheoryV4
public import SmallLevelTwentySixSourceResultant87V1
public import SmallLevelTwentySixSourceResultantIndexDataSeriesV4

/-! Consolidated chapter: SmallLevelTwentySixPariSourceBridge. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixPariSourcePivotIndexFourBindingSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariSourceBridge
theorem pivot87Four_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariSourcePivot87.p0 x y z w a b u=SmallLevelTwentySixPariSourcePivots.source4 x y z w a b u := by
  simp only [SmallLevelTwentySixPariSourcePivot87.p0,SmallLevelTwentySixPariSourcePivot87.coefficients0,SmallLevelTwentySixPariSourcePivot87.c0_0,SmallLevelTwentySixPariSourcePivot87.c0_1,SmallLevelTwentySixPariSourcePivot87.c0_2,SmallLevelTwentySixPariSourcePivot87.c0_3,SmallLevelTwentySixPariSourcePivot87.c0_4,SmallLevelTwentySixPariSourcePivots.source4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  ring
#print axioms pivot87Four_binding

theorem pivot8Four_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariSourcePivot8.p0 x y z w a b u=SmallLevelTwentySixPariSourcePivots.source4 x y z w a b u := by
  simp only [SmallLevelTwentySixPariSourcePivot8.p0,SmallLevelTwentySixPariSourcePivot8.coefficients0,SmallLevelTwentySixPariSourcePivot8.c0_0,SmallLevelTwentySixPariSourcePivot8.c0_1,SmallLevelTwentySixPariSourcePivot8.c0_2,SmallLevelTwentySixPariSourcePivot8.c0_3,SmallLevelTwentySixPariSourcePivot8.c0_4,SmallLevelTwentySixPariSourcePivots.source4,SmallLevelPolynomialCoefficientCertificate.evaluate]
  ring
#print axioms pivot8Four_binding
end SmallLevelTwentySixPariSourceBridge
end
end
end

/-! ## SmallLevelTwentySixPariSourcePivotIndexRawBindingSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariSourceBridge
theorem pivot87Raw_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariSourcePivot87.p6 x y z w a b u=SmallLevelTwentySixPariSourcePolynomial87.polynomial x y z w a b u := by
  calc
    SmallLevelTwentySixPariSourcePivot87.p6 x y z w a b u=(((((((((((((((((SmallLevelTwentySixPariSourcePivot87.c6_16 y z w a b u)*x+(SmallLevelTwentySixPariSourcePivot87.c6_15 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_14 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_13 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_12 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_11 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_10 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_9 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_8 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_7 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_6 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_5 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_4 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_3 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_2 y z w a b u))*x+(SmallLevelTwentySixPariSourcePivot87.c6_1 y z w a b u))*x) := by
      simp only [SmallLevelTwentySixPariSourcePivot87.p6,SmallLevelTwentySixPariSourcePivot87.coefficients6,
        SmallLevelPolynomialCoefficientCertificate.evaluate,SmallLevelTwentySixPariSourcePivot87.c6_0]
      ring
    _=SmallLevelTwentySixPariSourcePolynomial87.polynomial x y z w a b u := by
      simp only [SmallLevelTwentySixPariSourcePolynomial87.polynomial,SmallLevelTwentySixPariSourcePivot87.c6_1,SmallLevelTwentySixPariSourcePivot87.c6_2,SmallLevelTwentySixPariSourcePivot87.c6_3,SmallLevelTwentySixPariSourcePivot87.c6_4,SmallLevelTwentySixPariSourcePivot87.c6_5,SmallLevelTwentySixPariSourcePivot87.c6_6,SmallLevelTwentySixPariSourcePivot87.c6_7,SmallLevelTwentySixPariSourcePivot87.c6_8,SmallLevelTwentySixPariSourcePivot87.c6_9,SmallLevelTwentySixPariSourcePivot87.c6_10,SmallLevelTwentySixPariSourcePivot87.c6_11,SmallLevelTwentySixPariSourcePivot87.c6_12,SmallLevelTwentySixPariSourcePivot87.c6_13,SmallLevelTwentySixPariSourcePivot87.c6_14,SmallLevelTwentySixPariSourcePivot87.c6_15,SmallLevelTwentySixPariSourcePivot87.c6_16]
#print axioms pivot87Raw_binding
end SmallLevelTwentySixPariSourceBridge
end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariSourceBridge
open QuantitativeArithmeticSevenLaurentRows
theorem pivot8Raw_binding (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.primitiveData=
      SmallLevelTwentySixPariSourcePivot8.p6 x y z w a b u := by
  norm_num [eval,monomial,SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.primitiveData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.primitiveData0,SmallLevelTwentySixPariSourcePivot8.p6,SmallLevelTwentySixPariSourcePivot8.coefficients6,SmallLevelTwentySixPariSourcePivot8.c6_0,SmallLevelTwentySixPariSourcePivot8.c6_1,SmallLevelTwentySixPariSourcePivot8.c6_2,SmallLevelTwentySixPariSourcePivot8.c6_3,SmallLevelTwentySixPariSourcePivot8.c6_4,SmallLevelTwentySixPariSourcePivot8.c6_5,SmallLevelPolynomialCoefficientCertificate.evaluate]
  ring
#print axioms pivot8Raw_binding
end SmallLevelTwentySixPariSourceBridge
end
end
end

/-! ## SmallLevelTwentySixPariSourcePivotIndexSixBindingSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariSourceBridge
theorem pivot87Six_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariSourcePivot87.p2 x y z w a b u=SmallLevelTwentySixPariSourcePivots.source6 x y z w a b u := by
  simp only [SmallLevelTwentySixPariSourcePivot87.p2,SmallLevelTwentySixPariSourcePivot87.coefficients2,SmallLevelTwentySixPariSourcePivot87.c2_0,SmallLevelTwentySixPariSourcePivot87.c2_1,SmallLevelTwentySixPariSourcePivot87.c2_2,SmallLevelTwentySixPariSourcePivot87.c2_3,SmallLevelTwentySixPariSourcePivot87.c2_4,SmallLevelTwentySixPariSourcePivots.source6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  ring
#print axioms pivot87Six_binding

theorem pivot8Six_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariSourcePivot8.p2 x y z w a b u=SmallLevelTwentySixPariSourcePivots.source6 x y z w a b u := by
  simp only [SmallLevelTwentySixPariSourcePivot8.p2,SmallLevelTwentySixPariSourcePivot8.coefficients2,SmallLevelTwentySixPariSourcePivot8.c2_0,SmallLevelTwentySixPariSourcePivot8.c2_1,SmallLevelTwentySixPariSourcePivot8.c2_2,SmallLevelTwentySixPariSourcePivot8.c2_3,SmallLevelTwentySixPariSourcePivot8.c2_4,SmallLevelTwentySixPariSourcePivots.source6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  ring
#print axioms pivot8Six_binding
end SmallLevelTwentySixPariSourceBridge
end
end
end

/-! ## SmallLevelTwentySixPariSourceBridgeTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentySixPariSourceBridge. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixPariSourceW87LeftBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariSourceBridge
theorem w87Left_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixPariSourceW87.p1 x y z w a b u=SmallLevelTwentySixPariSourcePivot87.p4 x y z w a b u := by
  unfold SmallLevelTwentySixPariSourceW87.p1 SmallLevelTwentySixPariSourcePivot87.p4
  apply congrArg (SmallLevelPolynomialCoefficientCertificate.evaluate x)
  rfl
#print axioms w87Left_binding
end SmallLevelTwentySixPariSourceBridge
end
end

/-! ## SmallLevelTwentySixPariSourceW87RightBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariSourceBridge
theorem w87Right_binding (x y z w a b u : ℂ) :
    x*(SmallLevelTwentySixPariSourceW87.p3 x y z w a b u)=SmallLevelTwentySixPariSourcePivot8.p4 x y z w a b u := by
  simp only [SmallLevelTwentySixPariSourceW87.p3,SmallLevelTwentySixPariSourceW87.coefficients3,SmallLevelTwentySixPariSourceW87.c3_0,SmallLevelTwentySixPariSourceW87.c3_1,SmallLevelTwentySixPariSourceW87.c3_2,SmallLevelTwentySixPariSourceW87.c3_3,SmallLevelTwentySixPariSourceW87.c3_4,SmallLevelTwentySixPariSourceW87.c3_5,SmallLevelTwentySixPariSourcePivot8.p4,SmallLevelTwentySixPariSourcePivot8.coefficients4,SmallLevelTwentySixPariSourcePivot8.c4_0,SmallLevelTwentySixPariSourcePivot8.c4_1,SmallLevelTwentySixPariSourcePivot8.c4_2,SmallLevelTwentySixPariSourcePivot8.c4_3,SmallLevelTwentySixPariSourcePivot8.c4_4,SmallLevelTwentySixPariSourcePivot8.c4_5,SmallLevelTwentySixPariSourcePivot8.c4_6,SmallLevelPolynomialCoefficientCertificate.evaluate]
  ring
#print axioms w87Right_binding
end SmallLevelTwentySixPariSourceBridge
end
end

/-! ## SmallLevelTwentySixPariSourceResultant87SourceBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariSourceBridge
theorem resultant87Source_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant87.p0 x y z w a b u=SmallLevelTwentySixPariIdentity004.p0 x y z w a b u := by
  simp only [SmallLevelTwentySixSourceResultant87.p0,SmallLevelTwentySixSourceResultant87.coefficients0,SmallLevelTwentySixSourceResultant87.c0_0,SmallLevelTwentySixSourceResultant87.c0_1,SmallLevelTwentySixSourceResultant87.c0_2,SmallLevelTwentySixSourceResultant87.c0_3,SmallLevelTwentySixPariIdentity004.p0,SmallLevelPolynomialCoefficientCertificate.evaluate]
  ring
#print axioms resultant87Source_binding
end SmallLevelTwentySixPariSourceBridge
end
end

/-! ## SmallLevelTwentySixPariSourceResultant87WBindingV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariSourceBridge
theorem resultant87W_binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant87.p2 x y z w a b u=SmallLevelTwentySixPariSourceW87.p4 x y z w a b u := by
  unfold SmallLevelTwentySixSourceResultant87.p2 SmallLevelTwentySixPariSourceW87.p4
  apply congrArg (SmallLevelPolynomialCoefficientCertificate.evaluate x)
  rfl
#print axioms resultant87W_binding
end SmallLevelTwentySixPariSourceBridge
end
end

/-! ## SmallLevelTwentySixPariSource87BridgeV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariSourceBridge
open QuantitativeArithmeticSevenLaurentRows SmallLevelPolynomialCoefficientCertificate

/-- The initial row87 resultant follows from the actual normalized rational
source rows. Only the nonzero prime parameter is cancelled. -/
theorem source87_resultant_zero (x y z w a b u : ℂ) (hx : x≠0)
    (h0 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0)
    (h4 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData=0)
    (h6 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData=0)
    (h8 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.primitiveData=0)
    (h87 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixPariRawSource87.rawData=0) :
    SmallLevelTwentySixPariIdentity001.p4 x y z w a b u=0 := by
  rw [SmallLevelTwentySixPariFirstChart.source0_binding] at h0
  rw [SmallLevelTwentySixPariSourcePivots.source4_binding] at h4
  rw [SmallLevelTwentySixPariSourcePivots.source6_binding] at h6
  rw [pivot8Raw_binding] at h8
  rw [SmallLevelTwentySixPariSourcePolynomial87.polynomial_binding] at h87
  have he8:=SmallLevelTwentySixPariSourcePivot8.identity x y z w a b u
  rw [pivot8Four_binding,pivot8Six_binding,h4,h6,h8] at he8
  have hg8 : SmallLevelTwentySixPariSourcePivot8.p4 x y z w a b u=0 := by
    simpa only [zero_mul,mul_zero,zero_add,add_zero] using he8.symm
  have he87:=SmallLevelTwentySixPariSourcePivot87.identity x y z w a b u
  rw [pivot87Four_binding,pivot87Six_binding,pivot87Raw_binding,h4,h6,h87] at he87
  have hg87 : SmallLevelTwentySixPariSourcePivot87.p4 x y z w a b u=0 := by
    simpa only [zero_mul,mul_zero,zero_add,add_zero] using he87.symm
  have hw1 : SmallLevelTwentySixPariSourceW87.p1 x y z w a b u=0 :=
    (w87Left_binding x y z w a b u).trans hg87
  have hw3 : SmallLevelTwentySixPariSourceW87.p3 x y z w a b u=0 :=
    (mul_eq_zero.mp ((w87Right_binding x y z w a b u).trans hg8)).resolve_left hx
  have hew:=SmallLevelTwentySixPariSourceW87.identity x y z w a b u
  rw [hw1,hw3] at hew
  have hw4 : SmallLevelTwentySixPariSourceW87.p4 x y z w a b u=0 := by
    simpa only [SmallLevelTwentySixPariSourceW87.p6,
      SmallLevelTwentySixPariSourceW87.coefficients6,evaluate,
      zero_mul,mul_zero,zero_add,add_zero] using hew.symm
  have hr0 : SmallLevelTwentySixSourceResultant87.p0 x y z w a b u=0 :=
    (resultant87Source_binding x y z w a b u).trans h0
  have hr2 : SmallLevelTwentySixSourceResultant87.p2 x y z w a b u=0 :=
    (resultant87W_binding x y z w a b u).trans hw4
  have her:=SmallLevelTwentySixSourceResultant87.identity x y z w a b u
  rw [hr0,hr2] at her
  have hr4 : SmallLevelTwentySixSourceResultant87.p4 x y z w a b u=0 := by
    simpa only [SmallLevelTwentySixSourceResultant87.p6,
      SmallLevelTwentySixSourceResultant87.coefficients6,evaluate,
      zero_mul,mul_zero,zero_add,add_zero] using her.symm
  exact (SmallLevelTwentySixPariCompactInitial87Binding.binding x y z w a b u).symm.trans hr4

#print axioms source87_resultant_zero
end SmallLevelTwentySixPariSourceBridge
end
end
end
