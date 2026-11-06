module

public import SmallLevelTwentySixPariSourcePolynomialIndexHornerSeriesV4
public import SmallLevelTwentySixPariSourcePolynomialIndexRawEvaluationSeriesV4
public import SmallLevelTwentySixPariSourcePolynomialIndexTransposeColumnBundleSeriesV4
public import SmallLevelTwentySixPariSourcePolynomialIndexTransposeDataSeriesV4
public import SmallLevelTwentySixPariSourcePolynomialIndexTransposeRowBundleSeriesV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89LastColumnsV1 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89
open SmallLevelTwentySixPariSourcePolynomial89
open QuantitativeArithmeticSevenLaurentRows SmallLevelPolynomialCoefficientCertificate
theorem part_column_16 (x y z w a b u : ℂ) :
    polynomialVector y z w a b u 16=evaluate 1 (List.ofFn (fun i => partMatrix y z w a b u i 16)) := by
  change polynomialCoefficient16 y z w a b u=evaluate 1 [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(-487701/1295686674939904000),((2349/20730986799038464)*y),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,((107163/518274669975961600)*u)]
  simp only [polynomialCoefficient16,evaluate,one_mul,zero_add,add_zero] <;> ring
#print axioms part_column_16
theorem part_column_17 (x y z w a b u : ℂ) :
    polynomialVector y z w a b u 17=evaluate 1 (List.ofFn (fun i => partMatrix y z w a b u i 17)) := by
  change polynomialCoefficient17 y z w a b u=evaluate 1 [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(729/12956866749399040),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  simp only [polynomialCoefficient17,evaluate,one_mul,zero_add,add_zero]
#print axioms part_column_17

end QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89V1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89
open SmallLevelTwentySixPariSourcePolynomial89
open QuantitativeArithmeticSevenLaurentRows SmallLevelPolynomialCoefficientCertificate
/-- Exact source binding, regrouped through a checked coefficient matrix. -/
theorem polynomial_binding (x y z w a b u : ℂ) :
    eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      SmallLevelTwentySixPariRawSource89.rawData=polynomial x y z w a b u := by
  rw [raw_evaluation,polynomial_evaluation]
  have hrows : evaluate 1 (List.ofFn (partVector x y z w a b u))=
      evaluate 1 (List.ofFn (fun i => evaluate x (List.ofFn (partMatrix y z w a b u i)))) := by
    apply evaluate_ofFn_congr
    intro i
    fin_cases i
    · exact part_row_0 x y z w a b u
    · exact part_row_1 x y z w a b u
    · exact part_row_2 x y z w a b u
    · exact part_row_3 x y z w a b u
    · exact part_row_4 x y z w a b u
    · exact part_row_5 x y z w a b u
    · exact part_row_6 x y z w a b u
    · exact part_row_7 x y z w a b u
    · exact part_row_8 x y z w a b u
    · exact part_row_9 x y z w a b u
    · exact part_row_10 x y z w a b u
    · exact part_row_11 x y z w a b u
    · exact part_row_12 x y z w a b u
    · exact part_row_13 x y z w a b u
    · exact part_row_14 x y z w a b u
    · exact part_row_15 x y z w a b u
    · exact part_row_16 x y z w a b u
    · exact part_row_17 x y z w a b u
    · exact part_row_18 x y z w a b u
    · exact part_row_19 x y z w a b u
    · exact part_row_20 x y z w a b u
    · exact part_row_21 x y z w a b u
    · exact part_row_22 x y z w a b u
    · exact part_row_23 x y z w a b u
    · exact part_row_24 x y z w a b u
    · exact part_row_25 x y z w a b u
    · exact part_row_26 x y z w a b u
    · exact part_row_27 x y z w a b u
    · exact part_row_28 x y z w a b u
    · exact part_row_29 x y z w a b u
    · exact part_row_30 x y z w a b u
    · exact part_row_31 x y z w a b u
    · exact part_row_32 x y z w a b u
    · exact part_row_33 x y z w a b u
    · exact part_row_34 x y z w a b u
    · exact part_row_35 x y z w a b u
    · exact part_row_36 x y z w a b u
    · exact part_row_37 x y z w a b u
    · exact part_row_38 x y z w a b u
    · exact part_row_39 x y z w a b u
    · exact part_row_40 x y z w a b u
    · exact part_row_41 x y z w a b u
    · exact part_row_42 x y z w a b u
    · exact part_row_43 x y z w a b u
    · exact part_row_44 x y z w a b u
    · exact part_row_45 x y z w a b u
    · exact part_row_46 x y z w a b u
    · exact part_row_47 x y z w a b u
    · exact part_row_48 x y z w a b u
    · exact part_row_49 x y z w a b u
    · exact part_row_50 x y z w a b u
    · exact part_row_51 x y z w a b u
    · exact part_row_52 x y z w a b u
    · exact part_row_53 x y z w a b u
    · exact part_row_54 x y z w a b u
    · exact part_row_55 x y z w a b u
    · exact part_row_56 x y z w a b u
    · exact part_row_57 x y z w a b u
    · exact part_row_58 x y z w a b u
    · exact part_row_59 x y z w a b u
    · exact part_row_60 x y z w a b u
    · exact part_row_61 x y z w a b u
    · exact part_row_62 x y z w a b u
    · exact part_row_63 x y z w a b u
    · exact part_row_64 x y z w a b u
    · exact part_row_65 x y z w a b u
    · exact part_row_66 x y z w a b u
    · exact part_row_67 x y z w a b u
    · exact part_row_68 x y z w a b u
    · exact part_row_69 x y z w a b u
    · exact part_row_70 x y z w a b u
    · exact part_row_71 x y z w a b u
    · exact part_row_72 x y z w a b u
    · exact part_row_73 x y z w a b u
  rw [hrows,evaluate_transpose]
  apply evaluate_ofFn_congr
  intro j
  fin_cases j
  · exact (part_column_0 x y z w a b u).symm
  · exact (part_column_1 x y z w a b u).symm
  · exact (part_column_2 x y z w a b u).symm
  · exact (part_column_3 x y z w a b u).symm
  · exact (part_column_4 x y z w a b u).symm
  · exact (part_column_5 x y z w a b u).symm
  · exact (part_column_6 x y z w a b u).symm
  · exact (part_column_7 x y z w a b u).symm
  · exact (part_column_8 x y z w a b u).symm
  · exact (part_column_9 x y z w a b u).symm
  · exact (part_column_10 x y z w a b u).symm
  · exact (part_column_11 x y z w a b u).symm
  · exact (part_column_12 x y z w a b u).symm
  · exact (part_column_13 x y z w a b u).symm
  · exact (part_column_14 x y z w a b u).symm
  · exact (part_column_15 x y z w a b u).symm
  · exact (part_column_16 x y z w a b u).symm
  · exact (part_column_17 x y z w a b u).symm
#print axioms polynomial_binding

end QuantitativeArithmeticSmallLevelTwentySixSourcePolynomial89
end
end
