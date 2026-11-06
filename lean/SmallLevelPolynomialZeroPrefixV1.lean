module
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelPolynomialZeroPrefix
open SmallLevelPolynomialCoefficientCertificate

theorem evaluate_zero_prefix (x : ℂ) (k : ℕ) (p : List ℂ) :
    evaluate x (List.replicate k 0 ++ p)=x^k*evaluate x p := by
  induction k with
  | zero => simp only [List.replicate_zero,List.nil_append,pow_zero,one_mul]
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,evaluate,zero_add,ih,pow_succ]
    ring
#print axioms evaluate_zero_prefix
end SmallLevelPolynomialZeroPrefix
