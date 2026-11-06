module
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
public import SmallLevelTwentySixPariSourcePolynomialIndexTransposeDataSeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariSourcePolynomial87
open QuantitativeArithmeticSevenLaurentRows SmallLevelPolynomialCoefficientCertificate
theorem polynomial_evaluation (x y z w a b u : ℂ) :
    polynomial x y z w a b u=evaluate x (List.ofFn (polynomialVector y z w a b u)) := by
  calc
    polynomial x y z w a b u=(((((((((((((((((polynomialCoefficient16 y z w a b u)*x+(polynomialCoefficient15 y z w a b u))*x+(polynomialCoefficient14 y z w a b u))*x+(polynomialCoefficient13 y z w a b u))*x+(polynomialCoefficient12 y z w a b u))*x+(polynomialCoefficient11 y z w a b u))*x+(polynomialCoefficient10 y z w a b u))*x+(polynomialCoefficient09 y z w a b u))*x+(polynomialCoefficient08 y z w a b u))*x+(polynomialCoefficient07 y z w a b u))*x+(polynomialCoefficient06 y z w a b u))*x+(polynomialCoefficient05 y z w a b u))*x+(polynomialCoefficient04 y z w a b u))*x+(polynomialCoefficient03 y z w a b u))*x+(polynomialCoefficient02 y z w a b u))*x+(polynomialCoefficient01 y z w a b u))*x) := by
      simp only [polynomial,polynomialCoefficient01,polynomialCoefficient02,polynomialCoefficient03,polynomialCoefficient04,polynomialCoefficient05,polynomialCoefficient06,polynomialCoefficient07,polynomialCoefficient08,polynomialCoefficient09,polynomialCoefficient10,polynomialCoefficient11,polynomialCoefficient12,polynomialCoefficient13,polynomialCoefficient14,polynomialCoefficient15,polynomialCoefficient16]
    _=evaluate x (List.ofFn (polynomialVector y z w a b u)) := by
      change _=evaluate x [0,(polynomialCoefficient01 y z w a b u),(polynomialCoefficient02 y z w a b u),(polynomialCoefficient03 y z w a b u),(polynomialCoefficient04 y z w a b u),(polynomialCoefficient05 y z w a b u),(polynomialCoefficient06 y z w a b u),(polynomialCoefficient07 y z w a b u),(polynomialCoefficient08 y z w a b u),(polynomialCoefficient09 y z w a b u),(polynomialCoefficient10 y z w a b u),(polynomialCoefficient11 y z w a b u),(polynomialCoefficient12 y z w a b u),(polynomialCoefficient13 y z w a b u),(polynomialCoefficient14 y z w a b u),(polynomialCoefficient15 y z w a b u),(polynomialCoefficient16 y z w a b u)]
      exact (evaluate_positive_16 x (polynomialCoefficient01 y z w a b u) (polynomialCoefficient02 y z w a b u) (polynomialCoefficient03 y z w a b u) (polynomialCoefficient04 y z w a b u) (polynomialCoefficient05 y z w a b u) (polynomialCoefficient06 y z w a b u) (polynomialCoefficient07 y z w a b u) (polynomialCoefficient08 y z w a b u) (polynomialCoefficient09 y z w a b u) (polynomialCoefficient10 y z w a b u) (polynomialCoefficient11 y z w a b u) (polynomialCoefficient12 y z w a b u) (polynomialCoefficient13 y z w a b u) (polynomialCoefficient14 y z w a b u) (polynomialCoefficient15 y z w a b u) (polynomialCoefficient16 y z w a b u)).symm
#print axioms polynomial_evaluation

end SmallLevelTwentySixPariSourcePolynomial87
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SmallLevelTwentySixPariSourcePolynomial89
open QuantitativeArithmeticSevenLaurentRows SmallLevelPolynomialCoefficientCertificate
theorem polynomial_evaluation (x y z w a b u : ℂ) :
    polynomial x y z w a b u=evaluate x (List.ofFn (polynomialVector y z w a b u)) := by
  calc
    polynomial x y z w a b u=((((((((((((((((((polynomialCoefficient17 y z w a b u)*x+(polynomialCoefficient16 y z w a b u))*x+(polynomialCoefficient15 y z w a b u))*x+(polynomialCoefficient14 y z w a b u))*x+(polynomialCoefficient13 y z w a b u))*x+(polynomialCoefficient12 y z w a b u))*x+(polynomialCoefficient11 y z w a b u))*x+(polynomialCoefficient10 y z w a b u))*x+(polynomialCoefficient09 y z w a b u))*x+(polynomialCoefficient08 y z w a b u))*x+(polynomialCoefficient07 y z w a b u))*x+(polynomialCoefficient06 y z w a b u))*x+(polynomialCoefficient05 y z w a b u))*x+(polynomialCoefficient04 y z w a b u))*x+(polynomialCoefficient03 y z w a b u))*x+(polynomialCoefficient02 y z w a b u))*x+(polynomialCoefficient01 y z w a b u))*x) := by
      simp only [polynomial,polynomialCoefficient01,polynomialCoefficient02,polynomialCoefficient03,polynomialCoefficient04,polynomialCoefficient05,polynomialCoefficient06,polynomialCoefficient07,polynomialCoefficient08,polynomialCoefficient09,polynomialCoefficient10,polynomialCoefficient11,polynomialCoefficient12,polynomialCoefficient13,polynomialCoefficient14,polynomialCoefficient15,polynomialCoefficient16,polynomialCoefficient17]
    _=evaluate x (List.ofFn (polynomialVector y z w a b u)) := by
      change _=evaluate x [0,(polynomialCoefficient01 y z w a b u),(polynomialCoefficient02 y z w a b u),(polynomialCoefficient03 y z w a b u),(polynomialCoefficient04 y z w a b u),(polynomialCoefficient05 y z w a b u),(polynomialCoefficient06 y z w a b u),(polynomialCoefficient07 y z w a b u),(polynomialCoefficient08 y z w a b u),(polynomialCoefficient09 y z w a b u),(polynomialCoefficient10 y z w a b u),(polynomialCoefficient11 y z w a b u),(polynomialCoefficient12 y z w a b u),(polynomialCoefficient13 y z w a b u),(polynomialCoefficient14 y z w a b u),(polynomialCoefficient15 y z w a b u),(polynomialCoefficient16 y z w a b u),(polynomialCoefficient17 y z w a b u)]
      exact (evaluate_positive_17 x (polynomialCoefficient01 y z w a b u) (polynomialCoefficient02 y z w a b u) (polynomialCoefficient03 y z w a b u) (polynomialCoefficient04 y z w a b u) (polynomialCoefficient05 y z w a b u) (polynomialCoefficient06 y z w a b u) (polynomialCoefficient07 y z w a b u) (polynomialCoefficient08 y z w a b u) (polynomialCoefficient09 y z w a b u) (polynomialCoefficient10 y z w a b u) (polynomialCoefficient11 y z w a b u) (polynomialCoefficient12 y z w a b u) (polynomialCoefficient13 y z w a b u) (polynomialCoefficient14 y z w a b u) (polynomialCoefficient15 y z w a b u) (polynomialCoefficient16 y z w a b u) (polynomialCoefficient17 y z w a b u)).symm
#print axioms polynomial_evaluation

end SmallLevelTwentySixPariSourcePolynomial89
end
