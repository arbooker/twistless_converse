module
public import QuantitativeArithmeticSparseRecurrenceV1
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticRationalRecurrence

/-- A coefficient expression with inverses only in designated parameters.
Keeping the expression, rather than cancelling Laurent powers, also preserves
the linear identities when a parameter is zero. -/
inductive Coefficient where
  | rat : ℚ → Coefficient
  | param : Fin 6 → Coefficient
  | invParam : Fin 4 → Coefficient
  | add : Coefficient → Coefficient → Coefficient
  | mul : Coefficient → Coefficient → Coefficient
  | neg : Coefficient → Coefficient
  | pow : Coefficient → ℕ → Coefficient

namespace Coefficient

def eval (v : Fin 6 → ℂ) : Coefficient → ℂ
  | .rat q => q
  | .param j => v j
  | .invParam j => (v (j.castLE (by decide)))⁻¹
  | .add a b => eval v a + eval v b
  | .mul a b => eval v a * eval v b
  | .neg a => -eval v a
  | .pow a n => eval v a ^ n

theorem analytic (v : ℂ → Fin 6 → ℂ) (z : ℂ)
    (hv : ∀ j, AnalyticAt ℂ (fun t => v t j) z)
    (hne : ∀ j : Fin 4, v z (j.castLE (by decide)) ≠ 0)
    (a : Coefficient) : AnalyticAt ℂ (fun t => eval (v t) a) z := by
  induction a with
  | rat q => exact analyticAt_const
  | param j => exact hv j
  | invParam j => exact (hv _).inv (hne j)
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | neg a ha => exact ha.neg
  | pow a n ha => exact ha.pow n

end Coefficient

private theorem sum_functions {A : Type*} (fs : List (A → ℂ)) (a : A) :
    fs.sum a = (fs.map (fun f => f a)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simpa only [List.sum_cons, List.map_cons, Pi.add_apply] using
      (congrArg (fun z => f a + z) ih)

/-- One recurrence certificate gives linearity for all parameter values,
including values at which a denominator vanishes. -/
theorem linear_rows {m s : ℕ} [NeZero m]
    (instructions : ℕ → List (Coefficient × ℕ))
    (rows : (Fin 6 → ℂ) → ℕ → (Fin m → ℂ) → ℂ)
    (hbefore : ∀ i, i<s → ∀ t ∈ instructions i, t.2<m+i)
    (hrow : ∀ v r i, i<s → rows v i r = ((instructions i).map fun t =>
      t.1.eval v * (if t.2<m then r (Fin.ofNat m t.2) else rows v (t.2-m) r)).sum)
    (v : Fin 6 → ℂ) (i : ℕ) (hi : i<s) :
    ∃ L : (Fin m → ℂ) →ₗ[ℂ] ℂ, (L : (Fin m → ℂ) → ℂ) = rows v i := by
  apply QuantitativeArithmeticSparseRecurrence.linear_rows
    (fun j => LinearMap.proj (Fin.ofNat m j)) (rows v)
    (fun j => (instructions j).map (fun t => (t.1.eval v, t.2))) m s ?_ ?_ i hi
  · intro j hj t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hbefore j hj u hu
  · intro j hj
    funext r
    simpa only [sum_functions, List.map_map, Function.comp_def, Pi.smul_apply,
      smul_eq_mul, ite_apply, LinearMap.proj_apply] using hrow v r j hj

/-- The same certificate also proves analytic dependence on parameters and
sources. Only the four inverted parameters must be nonzero at the point. -/
theorem analytic_rows {m s : ℕ} [NeZero m]
    (instructions : ℕ → List (Coefficient × ℕ))
    (rows : (Fin 6 → ℂ) → ℕ → (Fin m → ℂ) → ℂ)
    (hbefore : ∀ i, i<s → ∀ t ∈ instructions i, t.2<m+i)
    (hrow : ∀ v r i, i<s → rows v i r = ((instructions i).map fun t =>
      t.1.eval v * (if t.2<m then r (Fin.ofNat m t.2) else rows v (t.2-m) r)).sum)
    (v : ℂ → Fin 6 → ℂ) (r : ℂ → Fin m → ℂ) (z : ℂ)
    (hv : ∀ j, AnalyticAt ℂ (fun t => v t j) z)
    (hne : ∀ j : Fin 4, v z (j.castLE (by decide)) ≠ 0)
    (hr : ∀ j, AnalyticAt ℂ (fun t => r t j) z) :
    ∀ i, i<s → AnalyticAt ℂ (fun t => rows (v t) i (r t)) z := by
  apply QuantitativeArithmeticSparseRecurrence.analytic_rows
    (fun j t => r t (Fin.ofNat m j)) (fun j t => rows (v t) j (r t))
    (fun j => (instructions j).map (fun u => ((fun t => u.1.eval (v t)), u.2))) m s z
  · intro j _
    exact hr _
  · intro j hj t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hbefore j hj u hu
  · intro j hj t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact u.1.analytic v z hv hne
  · intro j hj
    funext t
    simpa only [sum_functions, List.map_map, Function.comp_def, Pi.mul_apply,
      ite_apply] using hrow (v t) (r t) j hj

#print axioms Coefficient.analytic
#print axioms linear_rows
#print axioms analytic_rows
end QuantitativeArithmeticRationalRecurrence
