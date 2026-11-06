module
public meta import Lean
public import QuantitativeArithmeticFiniteRangeCertificatesV1

/-! Assemble adjacent finite certificates without writing their binary join tree.
The entries record interval lengths and their existing proofs in increasing order.
Expansion uses only `FiniteRangeCertificates.join`; the kernel checks every leaf,
offset, and resulting range. This command performs no mathematical computation. -/
public meta section
open Lean

declare_syntax_cat finiteRangeBlock
syntax num " => " term : finiteRangeBlock
syntax "finite_range% " term:max num " [" finiteRangeBlock,* "]" : term

private def assembleRange (P : TSyntax `term) :
    Nat → Nat → Array (Nat × TSyntax `term) → MacroM (TSyntax `term)
  | 0, _, _ => Macro.throwError "empty finite certificate cover"
  | fuel + 1, start, blocks => do
    if blocks.size == 1 then return blocks[0]!.2
    if blocks.isEmpty then Macro.throwError "empty finite certificate cover"
    let mid := blocks.size / 2
    let left := blocks.extract 0 mid
    let right := blocks.extract mid blocks.size
    let m := left.foldl (fun n b => n + b.1) 0
    let n := right.foldl (fun n b => n + b.1) 0
    let hl ← assembleRange P fuel start left
    let hr ← assembleRange P fuel (start + m) right
    `(QuantitativeArithmeticFiniteRangeCertificates.join $P
      $(quote start) $(quote m) $(quote n) $hl $hr)

macro_rules
  | `(finite_range% $P:term $start:num [$entries:finiteRangeBlock,*]) => do
    let mut blocks := #[]
    for entry in entries.getElems do
      let `(finiteRangeBlock| $n:num => $h:term) := entry
        | Macro.throwUnsupported
      blocks := blocks.push (n.getNat, h)
    assembleRange P blocks.size start.getNat blocks
