module
public import SmallLevelLaurentDerivationV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticLaurentNormalize
open QuantitativeArithmeticSevenLaurentRows

/-- Canonicalize sparse input lists, including zero coefficients. Soundness
is independent of ordering assumptions and of the merge fuel. -/
def normalize : Poly → Poly
  | [] => []
  | t::p => if t.1=0 then normalize p
      else mergeCompute 20000 [t] (normalize p)

theorem eval_normalize (X Y Z W a b c : ℂ) (v : ℕ→ℂ) (p : Poly) :
    eval X Y Z W a b c v (normalize p)=eval X Y Z W a b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    by_cases ht : t.1=0
    · simp only [normalize,ht,↓reduceIte,ih,eval_cons,Rat.cast_zero,zero_mul,zero_add]
    · simp only [normalize,ht,↓reduceIte,mergeCompute_eq,eval_mergeFuel,ih,
        eval_cons,eval_nil,add_zero]

#print axioms eval_normalize
end QuantitativeArithmeticLaurentNormalize
