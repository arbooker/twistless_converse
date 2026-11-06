module
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelLaurentProjectiveChart
open QuantitativeArithmeticSevenLaurentRows

theorem eval_div (X Y Z W A B C c : ℂ) (v : ℕ→ℂ) (p : Poly) :
    eval X Y Z W A B C (fun j => v j/c) p=eval X Y Z W A B C v p/c := by
  induction p with
  | nil => simp
  | cons t p ih => simp only [eval_cons,ih,add_div,mul_div_assoc]

/-- Normalize a two-coordinate kernel in the chart where its first
coordinate is nonzero. No coefficient polynomial is divided out. -/
theorem normalize_first {ρ : Type*} (X Y Z W A B C : ℂ) (p : ρ→Poly)
    (v : Fin 2→ℂ) (hv : v 0≠0)
    (hrows : ∀ i,eval X Y Z W A B C (fun j => if j=0 then v 0 else v 1) (p i)=0) :
    ∃ u : ℂ,∀ i,eval X Y Z W A B C (fun j => if j=0 then 1 else u) (p i)=0 := by
  refine ⟨v 1/v 0,?_⟩
  intro i
  have h := eval_div X Y Z W A B C (v 0)
    (fun j => if j=0 then v 0 else v 1) (p i)
  simpa only [ite_div,div_self hv,hrows i,zero_div] using h

#print axioms eval_div
#print axioms normalize_first
end SmallLevelLaurentProjectiveChart
