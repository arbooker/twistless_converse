module
public import QuantitativeArithmeticSparsePolynomialCertificateTheoryV4
public import Mathlib.Data.List.Sort
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelSparsePolynomialMerge
open Complex QuantitativeArithmeticSparsePolynomialCertificate

theorem merge_zero (x y z w a : ℂ) (p q : Poly) (n : ℕ)
    (hp : eval x y z w a p=0) (hq : eval x y z w a q=0) :
    eval x y z w a (mergeFuel n p q)=0 := by
  rw [eval_mergeFuel,hp,hq,add_zero]

def sortTerms (p : Poly) : Poly :=
  p.mergeSort (fun t u => exponentKey t.2 ≤ exponentKey u.2)

theorem eval_sort (x y z w a : ℂ) (p : Poly) :
    eval x y z w a (sortTerms p)=eval x y z w a p := by
  exact ((List.mergeSort_perm p _).map
    (fun t => (t.1:ℂ)*monomial x y z w a t.2)).sum_eq

def eraseAuxiliary (p : Poly) : Poly :=
  p.map fun t => (t.1,(t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,0))

theorem eval_erase (x y z w a : ℂ) (p : Poly) :
    eval x y z w a (eraseAuxiliary p)=eval x y z w 1 p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [eraseAuxiliary,List.map_cons,eval_cons,monomial,pow_zero,one_pow,mul_one] at *
    rw [ih]

theorem eval_independent (x y z w a : ℂ) (p : Poly)
    (h : eraseAuxiliary p=p) : eval x y z w a p=eval x y z w 1 p := by
  calc
    eval x y z w a p=eval x y z w a (eraseAuxiliary p) := congrArg (eval x y z w a) h.symm
    _=eval x y z w 1 p := eval_erase x y z w a p

#print axioms merge_zero
#print axioms eval_sort
#print axioms eval_independent
end SmallLevelSparsePolynomialMerge
