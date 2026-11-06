module
public import SmallLevelSparsePolynomialMergeV1
public import Mathlib.Algebra.Polynomial.OfFn
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelSparseCoefficientAssembly
open Complex QuantitativeArithmeticSparsePolynomialCertificate
open scoped Classical

def liftX (n : ℕ) (p : Poly) : Poly :=
  p.map fun t => (t.1,(n,t.2.1,t.2.2.1,t.2.2.2.1,0))

theorem eval_liftX (x y z w a : ℂ) (n : ℕ) (p : Poly) :
    eval x y z w a (liftX n p)=x^n*eval y z w 1 1 p := by
  induction p with
  | nil => simp [liftX]
  | cons t p ih =>
    simp only [liftX,List.map_cons,eval_cons] at *
    rw [ih]
    simp only [monomial,pow_zero,one_pow,mul_one]
    ring

theorem eval_flatten (x y z w a : ℂ) (ps : List Poly) :
    eval x y z w a ps.flatten=(ps.map (eval x y z w a)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatten_cons,eval_append,List.map_cons,List.sum_cons,ih]

def assemble {n : ℕ} (cs : Fin n→Poly) : Poly :=
  (List.ofFn fun i => liftX i (cs i)).flatten

theorem eval_assemble {n : ℕ} (cs : Fin n→Poly) (x y z w a : ℂ) :
    eval x y z w a (assemble cs)=∑ i : Fin n,x^(i:ℕ)*eval y z w 1 1 (cs i) := by
  rw [assemble,eval_flatten,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact eval_liftX x y z w a i (cs i)

theorem assemble_eval_polynomial {n : ℕ} (cs : Fin n→Poly) (x y z w a : ℂ) :
    eval x y z w a (assemble cs)=
      (Polynomial.ofFn n (fun i => eval y z w 1 1 (cs i))).eval x := by
  rw [eval_assemble,Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms eval_liftX
#print axioms assemble_eval_polynomial
end SmallLevelSparseCoefficientAssembly
