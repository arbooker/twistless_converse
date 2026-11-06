module
public import SmallLevelTwentySixPariSourcePivotFamilyV4
public import QuantitativeArithmeticSmallLevelTwentySixSourcePivot89TheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixSourceW89TheoryV4
public import SmallLevelTwentySixSourceResultant89SmallV1
public import SmallLevelTwentySixPariSourceBridgeTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixSourceBridgeTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89TheoryV4
public import SmallLevelTwentySixPariCompactInitialIndexBindingSeriesV4
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace SmallLevelTwentySixSource89SmallBridge
open QuantitativeArithmeticSmallLevelTwentySixSourceBridge
open QuantitativeArithmeticSevenLaurentRows SmallLevelPolynomialCoefficientCertificate
open SmallLevelTwentySixPariSourceBridge

/-- The initial row89 resultant follows from the actual normalized rational
source rows. Only the nonzero prime parameter is cancelled. -/
theorem source89_resultant_zero (x y z w a b u : ℂ) (hx : x≠0)
    (h0 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.primitiveData=0)
    (h4 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.primitiveData=0)
    (h6 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.primitiveData=0)
    (h8 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.primitiveData=0)
    (h89 : eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixPariRawSource89.rawData=0) :
    SmallLevelTwentySixPariIdentity003.p4 x y z w a b u=0 := by
  rw [SmallLevelTwentySixPariFirstChart.source0_binding] at h0
  rw [SmallLevelTwentySixPariSourcePivots.source4_binding] at h4
  rw [SmallLevelTwentySixPariSourcePivots.source6_binding] at h6
  rw [pivot8Raw_binding] at h8
  rw [QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89.polynomial_binding] at h89
  have he8:=SmallLevelTwentySixPariSourcePivot8.identity x y z w a b u
  rw [pivot8Four_binding,pivot8Six_binding,h4,h6,h8] at he8
  have hg8 : SmallLevelTwentySixPariSourcePivot8.p4 x y z w a b u=0 := by
    simpa only [zero_mul,mul_zero,zero_add,add_zero] using he8.symm
  have he89:=QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.identity x y z w a b u
  rw [pivot89Four_binding,pivot89Six_binding,pivot89Raw_binding,h4,h6,h89] at he89
  have hg89 : QuantitativeArithmeticSmallLevelTwentySixSourcePivot89.p4 x y z w a b u=0 := by
    simpa only [zero_mul,mul_zero,zero_add,add_zero] using he89.symm
  have hw1 : QuantitativeArithmeticSmallLevelTwentySixSourceW89.p1 x y z w a b u=0 :=
    (mul_eq_zero.mp ((w89Left_binding x y z w a b u).trans hg89)).resolve_left hx
  have hw3 : QuantitativeArithmeticSmallLevelTwentySixSourceW89.p3 x y z w a b u=0 :=
    (mul_eq_zero.mp ((w89Right_binding x y z w a b u).trans hg8)).resolve_left hx
  have hew:=QuantitativeArithmeticSmallLevelTwentySixSourceW89.identity x y z w a b u
  rw [hw1,hw3] at hew
  have hw4 : QuantitativeArithmeticSmallLevelTwentySixSourceW89.p4 x y z w a b u=0 := by
    simpa only [QuantitativeArithmeticSmallLevelTwentySixSourceW89.p6,
      QuantitativeArithmeticSmallLevelTwentySixSourceW89.coefficients6,evaluate,
      zero_mul,mul_zero,zero_add,add_zero] using hew.symm
  have hr0 : SmallLevelTwentySixSourceResultant89.p0 x y z w a b u=0 :=
    (resultant89Source_binding x y z w a b u).trans h0
  have hr2 : SmallLevelTwentySixSourceResultant89.p2 x y z w a b u=0 :=
    (resultant89W_binding x y z w a b u).trans hw4
  have her:=SmallLevelTwentySixSourceResultant89.identity_small x y z w a b u
  rw [hr0,hr2] at her
  have hr4 : SmallLevelTwentySixSourceResultant89.p4 x y z w a b u=0 := by
    simpa only [SmallLevelTwentySixSourceResultant89.p6,
      SmallLevelTwentySixSourceResultant89.coefficients6,evaluate,
      zero_mul,mul_zero,zero_add,add_zero] using her.symm
  exact (SmallLevelTwentySixPariCompactInitial89Binding.binding x y z w a b u).symm.trans hr4

#print axioms source89_resultant_zero
end SmallLevelTwentySixSource89SmallBridge
