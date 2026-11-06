module
public import SmallLevelTwentySixPariCompactInitialIndexBindingBundleSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariCompactInitial87Binding
open SmallLevelPolynomialCoefficientCertificate SmallLevelTwentySixPariLinkR87P4To001P4
theorem binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant87.p4 x y z w a b u=SmallLevelTwentySixPariIdentity001.p4 x y z w a b u := by
  have ho : SmallLevelTwentySixSourceResultant87.p4 x y z w a b u=evaluate x
      (List.ofFn (fun i => evaluate a (List.ofFn (matrix x y z w a b u i)))) := by
    change evaluate x (List.ofFn (oldCoefficients x y z w a b u))=_
    apply evaluate_ofFn_congr
    intro i
    fin_cases i
    · exact row_binding_0 x y z w a b u
    · exact row_binding_1 x y z w a b u
    · exact row_binding_2 x y z w a b u
    · exact row_binding_3 x y z w a b u
    · exact row_binding_4 x y z w a b u
    · exact row_binding_5 x y z w a b u
    · exact row_binding_6 x y z w a b u
    · exact row_binding_7 x y z w a b u
    · exact row_binding_8 x y z w a b u
    · exact row_binding_9 x y z w a b u
    · exact row_binding_10 x y z w a b u
    · exact row_binding_11 x y z w a b u
    · exact row_binding_12 x y z w a b u
    · exact row_binding_13 x y z w a b u
    · exact row_binding_14 x y z w a b u
    · exact row_binding_15 x y z w a b u
    · exact row_binding_16 x y z w a b u
    · exact row_binding_17 x y z w a b u
    · exact row_binding_18 x y z w a b u
    · exact row_binding_19 x y z w a b u
    · exact row_binding_20 x y z w a b u
    · exact row_binding_21 x y z w a b u
    · exact row_binding_22 x y z w a b u
    · exact row_binding_23 x y z w a b u
    · exact row_binding_24 x y z w a b u
    · exact row_binding_25 x y z w a b u
    · exact row_binding_26 x y z w a b u
    · exact row_binding_27 x y z w a b u
    · exact row_binding_28 x y z w a b u
  have hn : SmallLevelTwentySixPariIdentity001.p4 x y z w a b u=evaluate a
      (List.ofFn (fun j => evaluate x (List.ofFn (fun i => matrix x y z w a b u i j)))) := by
    change evaluate a (List.ofFn (newCoefficients x y z w a b u))=_
    apply evaluate_ofFn_congr
    intro j
    fin_cases j
    · exact column_binding_0 x y z w a b u
    · exact column_binding_1 x y z w a b u
    · exact column_binding_2 x y z w a b u
    · exact column_binding_3 x y z w a b u
    · exact column_binding_4 x y z w a b u
    · exact column_binding_5 x y z w a b u
    · exact column_binding_6 x y z w a b u
    · exact column_binding_7 x y z w a b u
    · exact column_binding_8 x y z w a b u
    · exact column_binding_9 x y z w a b u
    · exact column_binding_10 x y z w a b u
  exact ho.trans ((evaluate_transpose a x (matrix x y z w a b u)).trans hn.symm)
#print axioms binding

end SmallLevelTwentySixPariCompactInitial87Binding
end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariCompactInitial89Binding
open SmallLevelPolynomialCoefficientCertificate SmallLevelTwentySixPariLinkR89P4To003P4
theorem binding (x y z w a b u : ℂ) :
    SmallLevelTwentySixSourceResultant89.p4 x y z w a b u=SmallLevelTwentySixPariIdentity003.p4 x y z w a b u := by
  have ho : SmallLevelTwentySixSourceResultant89.p4 x y z w a b u=evaluate x
      (List.ofFn (fun i => evaluate a (List.ofFn (matrix x y z w a b u i)))) := by
    change evaluate x (List.ofFn (oldCoefficients x y z w a b u))=_
    apply evaluate_ofFn_congr
    intro i
    fin_cases i
    · exact row_binding_0 x y z w a b u
    · exact row_binding_1 x y z w a b u
    · exact row_binding_2 x y z w a b u
    · exact row_binding_3 x y z w a b u
    · exact row_binding_4 x y z w a b u
    · exact row_binding_5 x y z w a b u
    · exact row_binding_6 x y z w a b u
    · exact row_binding_7 x y z w a b u
    · exact row_binding_8 x y z w a b u
    · exact row_binding_9 x y z w a b u
    · exact row_binding_10 x y z w a b u
    · exact row_binding_11 x y z w a b u
    · exact row_binding_12 x y z w a b u
    · exact row_binding_13 x y z w a b u
    · exact row_binding_14 x y z w a b u
    · exact row_binding_15 x y z w a b u
    · exact row_binding_16 x y z w a b u
    · exact row_binding_17 x y z w a b u
    · exact row_binding_18 x y z w a b u
    · exact row_binding_19 x y z w a b u
    · exact row_binding_20 x y z w a b u
    · exact row_binding_21 x y z w a b u
    · exact row_binding_22 x y z w a b u
    · exact row_binding_23 x y z w a b u
    · exact row_binding_24 x y z w a b u
    · exact row_binding_25 x y z w a b u
    · exact row_binding_26 x y z w a b u
    · exact row_binding_27 x y z w a b u
    · exact row_binding_28 x y z w a b u
    · exact row_binding_29 x y z w a b u
  have hn : SmallLevelTwentySixPariIdentity003.p4 x y z w a b u=evaluate a
      (List.ofFn (fun j => evaluate x (List.ofFn (fun i => matrix x y z w a b u i j)))) := by
    change evaluate a (List.ofFn (newCoefficients x y z w a b u))=_
    apply evaluate_ofFn_congr
    intro j
    fin_cases j
    · exact column_binding_0 x y z w a b u
    · exact column_binding_1 x y z w a b u
    · exact column_binding_2 x y z w a b u
    · exact column_binding_3 x y z w a b u
    · exact column_binding_4 x y z w a b u
    · exact column_binding_5 x y z w a b u
    · exact column_binding_6 x y z w a b u
    · exact column_binding_7 x y z w a b u
    · exact column_binding_8 x y z w a b u
    · exact column_binding_9 x y z w a b u
    · exact column_binding_10 x y z w a b u
  exact ho.trans ((evaluate_transpose a x (matrix x y z w a b u)).trans hn.symm)
#print axioms binding

end SmallLevelTwentySixPariCompactInitial89Binding
end
