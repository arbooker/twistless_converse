module
public import QuantitativeArithmeticSparseEliminationV1
public import Mathlib.Analysis.Analytic.Constructions
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSparseRecurrence

/-- A local property preserved by the allowed coefficients propagates through
an entire finite row-operation program. This avoids separate induction proofs
of linearity or analyticity for every generated intermediate row. -/
theorem invariant {R E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    (inputs rows : ℕ → E) (instructions : ℕ → List (R × ℕ)) (m s : ℕ)
    (P : E → Prop) (Allowed : R → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x+y))
    (hsmul : ∀ c x, Allowed c → P x → P (c • x))
    (hinput : ∀ j, j<m → P (inputs j))
    (hbefore : ∀ i, i<s → ∀ t ∈ instructions i, t.2<m+i)
    (hcoeff : ∀ i, i<s → ∀ t ∈ instructions i, Allowed t.1)
    (hrow : ∀ i, i<s → rows i = ((instructions i).map fun t =>
      t.1 • (if t.2<m then inputs t.2 else rows (t.2-m))).sum) :
    ∀ i, i<s → P (rows i) := by
  have sum_property (xs : List E) (hx : ∀ x ∈ xs, P x) : P xs.sum := by
    induction xs with
    | nil => exact hzero
    | cons x xs ih =>
      exact hadd x xs.sum (hx x List.mem_cons_self)
        (ih (fun y hy => hx y (List.mem_cons_of_mem x hy)))
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [hrow i hi]
    apply sum_property
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    apply hsmul _ _ (hcoeff i hi t ht)
    split_ifs with hj
    · exact hinput _ hj
    · have hb := hbefore i hi t ht
      exact ih (t.2-m) (by omega) (by omega)

/-- Linear source coordinates yield linear reconstructed coordinates, without
one generated additivity and scalar-multiplication proof per pivot. -/
theorem linear_rows {V : Type*} [AddCommGroup V] [Module ℂ V]
    (inputs : ℕ → V →ₗ[ℂ] ℂ) (rows : ℕ → V → ℂ)
    (instructions : ℕ → List (ℂ × ℕ)) (m s : ℕ)
    (hbefore : ∀ i, i<s → ∀ t ∈ instructions i, t.2<m+i)
    (hrow : ∀ i, i<s → rows i = ((instructions i).map fun t =>
      t.1 • (if t.2<m then (inputs t.2 : V → ℂ) else rows (t.2-m))).sum) :
    ∀ i, i<s → ∃ L : V →ₗ[ℂ] ℂ, (L : V → ℂ)=rows i := by
  apply invariant (fun j => (inputs j : V → ℂ)) rows instructions m s
    (fun f => ∃ L : V →ₗ[ℂ] ℂ, (L : V → ℂ)=f) (fun _ => True)
  · exact ⟨0, rfl⟩
  · intro f g hf hg
    obtain ⟨L, rfl⟩ := hf
    obtain ⟨M, rfl⟩ := hg
    exact ⟨L+M, rfl⟩
  · intro c f _ hf
    obtain ⟨L, rfl⟩ := hf
    exact ⟨c • L, rfl⟩
  · intro j _
    exact ⟨inputs j, rfl⟩
  · exact hbefore
  · intro _ _ _ _
    trivial
  · exact hrow

/-- Analytic coefficients and sources yield an analytic reconstructed family
at every stage of the same finite recurrence. -/
theorem analytic_rows (inputs rows : ℕ → ℂ → ℂ)
    (instructions : ℕ → List ((ℂ → ℂ) × ℕ)) (m s : ℕ) (z : ℂ)
    (hinput : ∀ j, j<m → AnalyticAt ℂ (inputs j) z)
    (hbefore : ∀ i, i<s → ∀ t ∈ instructions i, t.2<m+i)
    (hcoeff : ∀ i, i<s → ∀ t ∈ instructions i, AnalyticAt ℂ t.1 z)
    (hrow : ∀ i, i<s → rows i = ((instructions i).map fun t =>
      t.1 * (if t.2<m then inputs t.2 else rows (t.2-m))).sum) :
    ∀ i, i<s → AnalyticAt ℂ (rows i) z := by
  apply invariant inputs rows instructions m s
    (fun f => AnalyticAt ℂ f z) (fun f => AnalyticAt ℂ f z)
  · exact analyticAt_const
  · intro f g hf hg
    exact hf.add hg
  · intro c f hc hf
    exact hc.mul hf
  · exact hinput
  · exact hbefore
  · exact hcoeff
  · exact hrow

#print axioms invariant
#print axioms linear_rows
#print axioms analytic_rows
end QuantitativeArithmeticSparseRecurrence
