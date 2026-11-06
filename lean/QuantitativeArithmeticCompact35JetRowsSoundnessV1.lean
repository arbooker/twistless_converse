module
public import QuantitativeArithmeticLaurentRegisterProgramTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section

/-! UNVERIFIED draft. Existing Laurent derivations preserve zero evaluation
under exactly the four original Laurent-unit hypotheses. -/
namespace QuantitativeArithmeticCompact35JetRows
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation

def lift (v : Fin 210 → ℂ) (j : ℕ) : ℂ :=
  if h : j<210 then v ⟨j,h⟩ else 0

theorem derived_zero {sources : ℕ → Poly} {initial : ℕ} {p : Poly}
    (derived : Derived sources initial p)
    (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (hsources : ∀ j, j < initial → eval x y z w a b c v (sources j)=0) :
    eval x y z w a b c v p=0 := by
  induction derived with
  | source j hj => exact hsources j hj
  | zero => rfl
  | combine p q operation out hp hq hcompute ihp ihq =>
    rw [← hcompute, substituteCompute_eq,
      eval_substitute x y z w a b c v hx hy hz hw]
    have hzero : (fun i => eval x y z w a b c v (binaryRows p q i)) = fun _ => 0 := by
      funext i
      by_cases hi : i=0 <;> simp [binaryRows,hi,ihp,ihq]
    rw [hzero]
    simp [eval]

/-- A single checked final table certifies every requested output. -/
theorem result_zero (sources : ℕ → Poly) (initial slots : ℕ)
    (program : List QuantitativeArithmeticLaurentRegisterProgram.Instruction)
    (indices : List ℕ) {r : ℕ} (result : Fin r → Poly)
    (checked : QuantitativeArithmeticLaurentRegisterProgram.verify
      (QuantitativeArithmeticLaurentProgram.sourceInputs sources initial (List.range slots))
      program indices ((List.finRange r).map result)=true)
    (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (hsources : ∀ j, j < initial → eval x y z w a b c v (sources j)=0)
    (i : Fin r) : eval x y z w a b c v (result i)=0 := by
  have hd := QuantitativeArithmeticLaurentRegisterProgram.checked_outputs
    (QuantitativeArithmeticLaurentProgram.sourceInputs_derived sources initial (List.range slots))
    program indices (QuantitativeArithmeticLaurentRegisterProgram.verify_sound checked)
  apply derived_zero (hd (result i) ?_) x y z w a b c v hx hy hz hw hsources
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

#print axioms derived_zero
#print axioms result_zero
end QuantitativeArithmeticCompact35JetRows
