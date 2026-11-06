module
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSelectedRowAnnihilator
open Matrix

def selector {n r : ℕ} (idx : Fin n→Fin r) (w : Fin n→ℂ) :
    Matrix (Fin 1) (Fin r) ℂ := fun _ j => ∑ i, if idx i=j then w i else 0

theorem selector_mulVec {n r : ℕ} (idx : Fin n→Fin r) (w : Fin n→ℂ)
    (v : Fin r→ℂ) : (selector idx w *ᵥ v) 0=∑ i, w i*v (idx i) := by
  classical
  change (∑ j, (∑ i, if idx i=j then w i else 0)*v j)=_
  simp_rw [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

/-- A functional identity on every vector is an actual left matrix
annihilator, including repeated selected rows. -/
theorem selector_mul_eq_zero {n r d : ℕ} (idx : Fin n→Fin r)
    (w : Fin n→ℂ) (A : Matrix (Fin r) (Fin d) ℂ)
    (h : ∀ v, ∑ i, w i*(A *ᵥ v) (idx i)=0) : selector idx w*A=0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec,Matrix.zero_mulVec]
  funext i
  have hi : i=(0:Fin 1) := Subsingleton.elim _ _
  subst i
  exact (selector_mulVec idx w (A *ᵥ v)).trans (h v)

theorem selector_analytic {n r : ℕ} (idx : Fin n→Fin r)
    (w : ℂ→Fin n→ℂ) (s : ℂ)
    (hw : ∀ i, AnalyticAt ℂ (fun z => w z i) s) (i : Fin 1) (j : Fin r) :
    AnalyticAt ℂ (fun z => selector idx (w z) i j) s := by
  classical
  unfold selector
  apply Finset.analyticAt_fun_sum
  intro a ha
  by_cases h : idx a=j
  · simpa only [h,ite_true] using hw a
  · simp only [h,ite_false]
    exact analyticAt_const

#print axioms selector_mulVec
#print axioms selector_mul_eq_zero
#print axioms selector_analytic
end QuantitativeArithmeticSelectedRowAnnihilator
