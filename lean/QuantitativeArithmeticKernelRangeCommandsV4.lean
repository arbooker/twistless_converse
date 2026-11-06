module
public meta import Lean
public import QuantitativeArithmeticFiniteRangeCertificatesV1

/-! A single finite assertion replaces named proofs of every small block.
The block size controls kernel-reduction memory, not a compilation timeout.
Each leaf uses `decide +kernel`; the balanced joins are ordinary theorems.
No native evaluator, external truth value or mathematical axiom is trusted. -/

public meta section
open Lean

private def kernelRangeProof (P : TSyntax `term) (block : Nat) :
    Nat → Nat → Nat → MacroM (TSyntax `term)
  | 0, _, _ => Macro.throwError "finite-range recursion exhausted"
  | fuel + 1, start, count => do
    if count ≤ block then
      `(by
        have h : ∀ i : Fin $(quote count), $P (i.val + $(quote start)) := by
          decide +kernel
        exact fun i hi => h ⟨i, hi⟩)
    else
      let left := count / 2
      let right := count - left
      let hl ← kernelRangeProof P block fuel start left
      let hr ← kernelRangeProof P block fuel (start + left) right
      `(QuantitativeArithmeticFiniteRangeCertificates.join $P
        $(quote start) $(quote left) $(quote right) $hl $hr)

/-- Prove a closed assertion on `Fin count` by bounded kernel reductions. -/
syntax "kernel_range% " term:max num " block " num : term

macro_rules
  | `(kernel_range% $P:term $count:num block $size:num) => do
    if size.getNat == 0 then Macro.throwError "finite-range block size must be positive"
    let h ← kernelRangeProof P size.getNat (count.getNat + 1) 0 count.getNat
    `(by
      have h : ∀ i < $count, $P (i + 0) := $h
      intro i
      exact h i.val i.isLt)

end
