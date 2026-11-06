module
public import QuantitativeArithmeticIntegerSevenLaurentRowsTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelIntegerLaurentExpansion
open QuantitativeArithmeticIntegerSevenLaurentRows

/-- A polynomial substitution checked through small monomial products
and separately checked additions. Every arithmetic identity is an input
proof, rather than an assertion about an external computation. -/
inductive Expansion (inputs : ℕ→Poly) : Poly→Poly→Prop where
  | nil : Expansion inputs [] []
  | term (r : ℤ) (i : ℕ) (e : Exponent) (out : Poly)
      (certificate : shift r e (inputs i)=out) : Expansion inputs [(r,i,e)] out
  | append (op₁ op₂ p q out : Poly) (fuel : ℕ)
      (left : Expansion inputs op₁ p) (right : Expansion inputs op₂ q)
      (certificate : mergeFuel fuel p q=out) : Expansion inputs (op₁++op₂) out

theorem Expansion.eval_eq {inputs : ℕ→Poly} {op out : Poly}
    (h : Expansion inputs op out) (x y z w a b c : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c v out=
      eval x y z w a b c (fun i => eval x y z w a b c v (inputs i)) op := by
  induction h with
  | nil => rfl
  | term r i e out hc =>
    rw [←hc,eval_shift x y z w a b c v hx hy hz hw]
    simp only [eval_cons,eval_nil,add_zero]
  | append op₁ op₂ p q out fuel hp hq hc ihp ihq =>
    rw [←hc,eval_mergeFuel,ihp,ihq,eval_append]

#print axioms Expansion.eval_eq
end SmallLevelIntegerLaurentExpansion
