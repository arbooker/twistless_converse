module
public import Mathlib.Data.Rat.Defs
set_option autoImplicit false
set_option synthInstance.maxSize 2048
@[expose] public section

/-! Executable candidate generation for row-operation certificates.
These functions produce data only. Every use is checked against the original
`QuantitativeArithmeticLaurentProgram.outputs` by Lean's kernel. -/
namespace QuantitativeArithmeticSevenLaurentRows
abbrev Exponent := ℤ × ℤ × ℤ × ℤ × ℕ × ℕ × ℕ
abbrev Term := ℚ × ℕ × Exponent
abbrev Poly := List Term
end QuantitativeArithmeticSevenLaurentRows

namespace QuantitativeArithmeticLaurentProgram
open QuantitativeArithmeticSevenLaurentRows
/-- A row-operation instruction. Indices refer to the current list of rows;
the newest computed row is prepended. An absent row denotes the zero row. -/
structure Instruction where
  left : ℕ
  right : ℕ
  operation : Poly
end QuantitativeArithmeticLaurentProgram

namespace QuantitativeArithmeticLaurentProgram.Compute
open QuantitativeArithmeticSevenLaurentRows

def addExponent (e f : Exponent) : Exponent :=
  (e.1+f.1,e.2.1+f.2.1,e.2.2.1+f.2.2.1,e.2.2.2.1+f.2.2.2.1,
   e.2.2.2.2.1+f.2.2.2.2.1,e.2.2.2.2.2.1+f.2.2.2.2.2.1,
   e.2.2.2.2.2.2+f.2.2.2.2.2.2)

def orderKey (j : ℕ) (e : Exponent) : ℤ :=
  (((((((j:ℤ)*100+e.1)*100+e.2.1)*100+e.2.2.1)*100+e.2.2.2.1)*100+
    e.2.2.2.2.1)*100+e.2.2.2.2.2.1)*100+e.2.2.2.2.2.2

def merge : ℕ → Poly → Poly → Poly
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,(a,j,e)::p,(b,k,f)::q =>
      if j=k ∧ e=f then
        if a+b=0 then merge n p q
        else (a+b,j,e)::merge n p q
      else if orderKey j e < orderKey k f then (a,j,e)::merge n p ((b,k,f)::q)
      else (b,k,f)::merge n ((a,j,e)::p) q

def shift (r : ℚ) (e : Exponent) (p : Poly) : Poly :=
  p.map fun t => (r*t.1,t.2.1,addExponent e t.2.2)

def substitute (p q : Poly) : Poly → Poly
  | [] => []
  | (r,j,e)::op => merge 20000 (shift r e (if j=0 then p else q)) (substitute p q op)

def row (rows : List Poly) (i : ℕ) : Poly := rows[i]?.getD []

def run (rows : List Poly) : List Instruction → List Poly
  | [] => rows
  | i::program => run (substitute (row rows i.left) (row rows i.right) i.operation :: rows) program

def outputs (rows : List Poly) (program : List Instruction) (indices : List ℕ) : List Poly :=
  indices.map (row (run rows program))

end QuantitativeArithmeticLaurentProgram.Compute

/-! Executable register-state candidates. Their uses require separate kernel
checks against the original register machine; no result is trusted. -/
namespace QuantitativeArithmeticLaurentRegisterProgram
open QuantitativeArithmeticSevenLaurentRows
structure Instruction where
  left : ℕ
  right : ℕ
  destination : ℕ
  operation : Poly

namespace Compute
open QuantitativeArithmeticLaurentProgram.Compute

def store : List Poly → ℕ → Poly → List Poly
  | [], _, _ => []
  | _ :: ps, 0, p => p :: ps
  | q :: ps, n+1, p => q :: store ps n p

def run (rows : List Poly) : List Instruction → List Poly
  | [] => rows
  | i::program => run
      (store rows i.destination (substitute (row rows i.left) (row rows i.right) i.operation))
      program
end Compute
end QuantitativeArithmeticLaurentRegisterProgram
