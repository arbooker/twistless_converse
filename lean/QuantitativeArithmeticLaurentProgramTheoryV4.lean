module

public import SmallLevelLaurentDerivationV1

/-! Consolidated chapter: QuantitativeArithmeticLaurentProgram. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticLaurentProgramV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticLaurentProgram
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation


def rowAt : List Poly → ℕ → Poly
  | [], _ => []
  | p :: _, 0 => p
  | _ :: ps, n + 1 => rowAt ps n

def step (rows : List Poly) (instruction : Instruction) : List Poly :=
  substituteCompute
    (binaryRows (rowAt rows instruction.left) (rowAt rows instruction.right))
    instruction.operation :: rows

def run (rows : List Poly) : List Instruction → List Poly
  | [] => rows
  | instruction :: rest => run (step rows instruction) rest

def outputs (rows : List Poly) (program : List Instruction)
    (indices : List ℕ) : List Poly := indices.map (rowAt (run rows program))

def sourceInputs (sources : ℕ → Poly) (initial : ℕ) (indices : List ℕ) : List Poly :=
  indices.map (fun i => if i < initial then sources i else [])

theorem sourceInputs_derived (sources : ℕ → Poly) (initial : ℕ) (indices : List ℕ) :
    ∀ p ∈ sourceInputs sources initial indices, Derived sources initial p := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  by_cases hi : i < initial
  · simpa only [ite_eq_left hi] using Derived.source (sources := sources) i hi
  · simpa only [ite_eq_right hi] using
      (Derived.zero (sources := sources) (initial := initial))

theorem rowAt_derived {sources : ℕ → Poly} {initial : ℕ}
    {rows : List Poly} (hrows : ∀ p ∈ rows, Derived sources initial p) (i : ℕ) :
    Derived sources initial (rowAt rows i) := by
  induction rows generalizing i with
  | nil => exact Derived.zero
  | cons p ps ih =>
    cases i with
    | zero => exact hrows p (List.mem_cons_self)
    | succ i =>
      exact ih (fun q hq => hrows q (List.mem_cons_of_mem p hq)) i

theorem step_derived {sources : ℕ → Poly} {initial : ℕ}
    {rows : List Poly} (hrows : ∀ p ∈ rows, Derived sources initial p)
    (instruction : Instruction) :
    ∀ p ∈ step rows instruction, Derived sources initial p := by
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    exact Derived.combine _ _ _ _ (rowAt_derived hrows instruction.left)
      (rowAt_derived hrows instruction.right) rfl
  · exact hrows p hp

theorem run_derived {sources : ℕ → Poly} {initial : ℕ}
    {rows : List Poly} (hrows : ∀ p ∈ rows, Derived sources initial p)
    (program : List Instruction) :
    ∀ p ∈ run rows program, Derived sources initial p := by
  induction program generalizing rows with
  | nil => exact hrows
  | cons instruction rest ih => exact ih (step_derived hrows instruction)

/-- Soundness of a whole certificate block. The program and the equality
certificate are data; no external computation is trusted. Intermediate rows
need not be printed as separate definitions and theorems. -/
theorem checked_outputs {sources : ℕ → Poly} {initial : ℕ}
    {rows result : List Poly} (hrows : ∀ p ∈ rows, Derived sources initial p)
    (program : List Instruction) (indices : List ℕ)
    (certificate : outputs rows program indices = result) :
    ∀ p ∈ result, Derived sources initial p := by
  rw [← certificate]
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact rowAt_derived (run_derived hrows program) i

#print axioms checked_outputs
end QuantitativeArithmeticLaurentProgram
end
end

/-! ## QuantitativeArithmeticLaurentProgramBlocksV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticLaurentProgram
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation

theorem nil_derived (sources : ℕ → Poly) (initial : ℕ) :
    ∀ p ∈ ([] : List Poly), Derived sources initial p := by
  intro p hp
  cases hp

theorem cons_derived {sources : ℕ → Poly} {initial : ℕ}
    {p : Poly} {rows : List Poly} (hp : Derived sources initial p)
    (hrows : ∀ q ∈ rows, Derived sources initial q) :
    ∀ q ∈ p :: rows, Derived sources initial q := by
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · simpa only [hq] using hp
  · exact hrows q hq

#print axioms cons_derived
end QuantitativeArithmeticLaurentProgram
end
end
