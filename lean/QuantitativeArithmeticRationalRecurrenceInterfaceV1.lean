module
public import QuantitativeArithmeticRationalRecurrenceV1
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticRationalRecurrence

/-- Finite algebraic data for a row recurrence. The analytic and linear
properties below are conclusions, rather than fields of this certificate. -/
structure Certificate (m s : ℕ) [NeZero m] where
  instructions : ℕ → List (Coefficient × ℕ)
  row : (Fin 6 → ℂ) → ℕ → (Fin m → ℂ) → ℂ
  before : ∀ i, i<s → ∀ t ∈ instructions i, t.2<m+i
  recurrence : ∀ v r i, i<s → row v i r = ((instructions i).map fun t =>
    t.1.eval v * (if t.2<m then r (Fin.ofNat m t.2) else row v (t.2-m) r)).sum

namespace Certificate
variable {m s : ℕ} [NeZero m]

/-- The underlying function is definitionally the original row. This keeps
existing downstream uses of evaluation and simplification unchanged. -/
def rowMap (c : Certificate m s) (v : Fin 6 → ℂ) (i : Fin s) :
    (Fin m → ℂ) →ₗ[ℂ] ℂ where
  toFun := c.row v i.val
  map_add' r t := by
    obtain ⟨L, hL⟩ := linear_rows c.instructions c.row c.before c.recurrence v i.val i.isLt
    rw [← congrFun hL (r+t), ← congrFun hL r, ← congrFun hL t]
    exact L.map_add r t
  map_smul' a r := by
    change c.row v i.val (a • r) = a • c.row v i.val r
    obtain ⟨L, hL⟩ := linear_rows c.instructions c.row c.before c.recurrence v i.val i.isLt
    rw [← congrFun hL (a • r), ← congrFun hL r]
    exact L.map_smul a r

theorem rowMap_apply (c : Certificate m s) (v : Fin 6 → ℂ) (i : Fin s)
    (r : Fin m → ℂ) : c.rowMap v i r = c.row v i.val r := rfl

theorem analytic (c : Certificate m s) (v : ℂ → Fin 6 → ℂ)
    (r : ℂ → Fin m → ℂ) (z : ℂ)
    (hv : ∀ j, AnalyticAt ℂ (fun t => v t j) z)
    (hne : ∀ j : Fin 4, v z (j.castLE (by decide)) ≠ 0)
    (hr : ∀ j, AnalyticAt ℂ (fun t => r t j) z) (i : Fin s) :
    AnalyticAt ℂ (fun t => c.rowMap (v t) i (r t)) z :=
  analytic_rows c.instructions c.row c.before c.recurrence v r z hv hne hr i.val i.isLt

end Certificate
#print axioms Certificate.rowMap
#print axioms Certificate.analytic
end QuantitativeArithmeticRationalRecurrence
