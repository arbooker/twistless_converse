module
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticPolynomialHornerBridge
open SmallLevelPolynomialCoefficientCertificate

/-- The same coefficient list evaluated with multiplication on the right.
Keeping coefficients opaque avoids normalizing their internal polynomials. -/
def rightHorner (x : ℂ) : List ℂ → ℂ
  | [] => 0
  | c :: p => rightHorner x p * x + c

theorem evaluate_eq_rightHorner (x : ℂ) (p : List ℂ) :
    evaluate x p = rightHorner x p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [evaluate, rightHorner, ih]
    ring

#print axioms evaluate_eq_rightHorner
end QuantitativeArithmeticPolynomialHornerBridge
