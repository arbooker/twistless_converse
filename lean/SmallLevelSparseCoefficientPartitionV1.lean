module
public import SmallLevelSparseCoefficientAssemblyV1
public import SmallLevelSparsePolynomialNormalizeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelSparseCoefficientPartition
open Complex QuantitativeArithmeticSparsePolynomialCertificate

/-- The coefficient of the first variable, retained as a sparse polynomial
in the remaining three physical variables. -/
def slice (n : ℕ) (p : Poly) : Poly :=
  p.filterMap fun t => if t.2.1=n then
    some (t.1,(t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,0,0)) else none

def coefficientValue (y z w : ℂ) (t : Term) : ℂ :=
  (t.1:ℂ)*y^t.2.2.1*z^t.2.2.2.1*w^t.2.2.2.2.1

theorem eval_slice_cons (y z w : ℂ) (n : ℕ) (t : Term) (p : Poly) :
    eval y z w 1 1 (slice n (t::p))=
      (if t.2.1=n then coefficientValue y z w t else 0)+eval y z w 1 1 (slice n p) := by
  by_cases h : t.2.1=n
  · simp only [slice,List.filterMap_cons,h,ite_true,eval_cons]
    simp only [monomial,coefficientValue,pow_zero,mul_one]
    ring
  · simp [slice,h]

def bounded (n : ℕ) (p : Poly) : Bool := p.all fun t => decide (t.2.1<n)

theorem eval_partition (n : ℕ) (p : Poly) (h : bounded n p=true) (x y z w : ℂ) :
    eval x y z w 1 p=∑ i : Fin n,x^(i:ℕ)*eval y z w 1 1 (slice i p) := by
  induction p with
  | nil => simp [slice]
  | cons t p ih =>
    have hh : t.2.1<n ∧ bounded n p=true := by
      simpa only [bounded,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] using h
    have hi := ih hh.2
    simp only [eval_cons]
    rw [hi]
    simp_rw [eval_slice_cons,mul_add]
    rw [Finset.sum_add_distrib]
    apply congrArg (fun v : ℂ => v+∑ i : Fin n,x^(i:ℕ)*eval y z w 1 1 (slice i p))
    symm
    rw [Finset.sum_eq_single (⟨t.2.1,hh.1⟩ : Fin n)]
    · simp only [ite_true,coefficientValue,monomial,one_pow,mul_one]
      ring
    · intro b _ hb
      have hb' : t.2.1≠(b:ℕ) := by
        intro he
        apply hb
        exact Fin.ext he.symm
      simp [hb']
    · simp

#print axioms eval_slice_cons
#print axioms eval_partition
end SmallLevelSparseCoefficientPartition
