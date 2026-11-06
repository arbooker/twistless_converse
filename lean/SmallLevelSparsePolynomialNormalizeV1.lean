module
public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelSparsePolynomialNormalize
open Complex QuantitativeArithmeticSparsePolynomialCertificate

/-- Bounded sparse normalization. Insufficient fuel changes efficiency only;
every intermediate list has exactly the same polynomial evaluation. -/
def normalize : ℕ→Poly→Poly
  | 0,p => p
  | n+1,p =>
      if p.length≤1 then p else
        mergeFuel 100000 (normalize n (p.take (p.length/2)))
          (normalize n (p.drop (p.length/2)))

theorem eval_normalize (x y z w a : ℂ) (n : ℕ) (p : Poly) :
    eval x y z w a (normalize n p)=eval x y z w a p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [normalize]
    split
    · rfl
    · rw [eval_mergeFuel,ih,ih,← eval_append,List.take_append_drop]

#print axioms eval_normalize
end SmallLevelSparsePolynomialNormalize
