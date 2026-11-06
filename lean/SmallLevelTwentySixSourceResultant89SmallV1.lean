module
public import SmallLevelTwentySixSourceResultantIndexCoefficientBundleSeriesV4
public import SmallLevelTwentySixSource89SplitFamilyV4
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace SmallLevelTwentySixSourceResultant89
open SmallLevelPolynomialCoefficientCertificate
theorem certificate_zero_small (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 30 (certificate_length y z w a b u)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b u
  · exact coefficient_1 y z w a b u
  · exact coefficient_2 y z w a b u
  · exact coefficient_3 y z w a b u
  · exact coefficient_4 y z w a b u
  · exact coefficient_5 y z w a b u
  · exact coefficient_6 y z w a b u
  · exact coefficient_7 y z w a b u
  · exact coefficient_8 y z w a b u
  · exact SmallLevelTwentySixSource89Split09.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split10.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split11.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split12.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split13.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split14.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split15.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split16.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split17.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split18.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split19.coefficient_split y z w a b u
  · exact SmallLevelTwentySixSource89Split20.coefficient_split y z w a b u
  · exact coefficient_21 y z w a b u
  · exact coefficient_22 y z w a b u
  · exact coefficient_23 y z w a b u
  · exact coefficient_24 y z w a b u
  · exact coefficient_25 y z w a b u
  · exact coefficient_26 y z w a b u
  · exact coefficient_27 y z w a b u
  · exact coefficient_28 y z w a b u
  · exact coefficient_29 y z w a b u

theorem identity_small (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero_small y z w a b u)
#print axioms identity_small

end SmallLevelTwentySixSourceResultant89
