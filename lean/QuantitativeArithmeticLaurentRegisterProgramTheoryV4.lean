module

public import QuantitativeArithmeticLaurentProgramTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticLaurentRegisterProgram. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticLaurentRegisterProgramV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

/-! A register machine for Laurent row operations. Reusing a dead register
discards intermediate rows while preserving the row-span invariant. -/
namespace QuantitativeArithmeticLaurentRegisterProgram
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation
open QuantitativeArithmeticLaurentProgram (rowAt sourceInputs sourceInputs_derived
  rowAt_derived cons_derived)


def store : List Poly → ℕ → Poly → List Poly
  | [], _, _ => []
  | _ :: ps, 0, p => p :: ps
  | q :: ps, n+1, p => q :: store ps n p

def step (rows : List Poly) (instruction : Instruction) : List Poly :=
  store rows instruction.destination
    (substituteCompute
      (binaryRows (rowAt rows instruction.left) (rowAt rows instruction.right))
      instruction.operation)

def run (rows : List Poly) : List Instruction → List Poly
  | [] => rows
  | instruction :: rest => run (step rows instruction) rest

def outputs (rows : List Poly) (program : List Instruction)
    (indices : List ℕ) : List Poly := indices.map (rowAt (run rows program))

theorem store_derived {sources : ℕ → Poly} {initial : ℕ}
    {rows : List Poly} (hrows : ∀ p ∈ rows, Derived sources initial p)
    (i : ℕ) {p : Poly} (hp : Derived sources initial p) :
    ∀ q ∈ store rows i p, Derived sources initial q := by
  induction rows generalizing i with
  | nil =>
    intro q hq
    cases hq
  | cons q qs ih =>
    cases i with
    | zero =>
      exact cons_derived hp (fun r hr => hrows r (List.mem_cons_of_mem q hr))
    | succ i =>
      exact cons_derived (hrows q List.mem_cons_self)
        (ih (fun r hr => hrows r (List.mem_cons_of_mem q hr)) i)

theorem step_derived {sources : ℕ → Poly} {initial : ℕ}
    {rows : List Poly} (hrows : ∀ p ∈ rows, Derived sources initial p)
    (instruction : Instruction) :
    ∀ p ∈ step rows instruction, Derived sources initial p := by
  apply store_derived hrows instruction.destination
  exact Derived.combine _ _ _ _ (rowAt_derived hrows instruction.left)
    (rowAt_derived hrows instruction.right) rfl

theorem run_derived {sources : ℕ → Poly} {initial : ℕ}
    {rows : List Poly} (hrows : ∀ p ∈ rows, Derived sources initial p)
    (program : List Instruction) :
    ∀ p ∈ run rows program, Derived sources initial p := by
  induction program generalizing rows with
  | nil => exact hrows
  | cons instruction rest ih => exact ih (step_derived hrows instruction)

/-- The only arithmetic certificate required is the final list equality. -/
theorem checked_outputs {sources : ℕ → Poly} {initial : ℕ}
    {rows result : List Poly} (hrows : ∀ p ∈ rows, Derived sources initial p)
    (program : List Instruction) (indices : List ℕ)
    (certificate : outputs rows program indices = result) :
    ∀ p ∈ result, Derived sources initial p := by
  rw [← certificate]
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact rowAt_derived (run_derived hrows program) i

#print axioms store_derived
#print axioms checked_outputs
end QuantitativeArithmeticLaurentRegisterProgram
end
end

/-! ## QuantitativeArithmeticLaurentRegisterCertificateV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace QuantitativeArithmeticLaurentRegisterProgram
open QuantitativeArithmeticSevenLaurentRows

/-- Fix the decidable equality instance before inserting a large program.
This avoids typeclass synthesis inspecting the complete concrete computation. -/
def verify (rows : List Poly) (program : List Instruction)
    (indices : List ℕ) (result : List Poly) : Bool :=
  decide (outputs rows program indices = result)

theorem verify_sound {rows : List Poly} {program : List Instruction}
    {indices : List ℕ} {result : List Poly}
    (certificate : verify rows program indices result = true) :
    outputs rows program indices = result :=
  of_decide_eq_true certificate

/-- A checkpoint is certified by the original machine, independently of its producer. -/
def verifyRun (rows : List Poly) (program : List Instruction)
    (result : List Poly) : Bool := decide (run rows program = result)

theorem verifyRun_sound {rows result : List Poly} {program : List Instruction}
    (certificate : verifyRun rows program result = true) : run rows program = result :=
  of_decide_eq_true certificate

theorem run_append (rows : List Poly) (first second : List Instruction) :
    run rows (first++second) = run (run rows first) second := by
  induction first generalizing rows with
  | nil => rfl
  | cons instruction rest ih => exact ih (step rows instruction)

#print axioms verifyRun_sound
#print axioms run_append

#print axioms verify_sound
end QuantitativeArithmeticLaurentRegisterProgram
end
end
