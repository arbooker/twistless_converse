module
public import QuantitativeArithmeticPackedBucketsV1
set_option autoImplicit false
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace QuantitativeArithmeticCoefficientSlices
open QuantitativeArithmeticIntegerSevenLaurentRows
open QuantitativeArithmeticPackedIntegerSubstitution
open QuantitativeArithmeticPackedBuckets
open QuantitativeArithmeticExponentEncoding
open scoped BigOperators

/-- Select coefficients before constructing shifted terms. Unselected terms
never enter either the sorting or the integer-coefficient multiplication. -/
def shiftedSlice (r : ℤ) (code B j : ℕ) : Poly → Packed
  | [] => []
  | t :: p =>
      if (code + encode t.2.2) % B = j then
        (r*t.1, code + encode t.2.2) :: shiftedSlice r code B j p
      else shiftedSlice r code B j p

theorem shiftedSlice_eq (r : ℤ) (code B j : ℕ) (p : Poly) :
    shiftedSlice r code B j p = bucket B j (shiftPacked r code (pack p)) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      by_cases h : (code + encode t.2.2) % B = j
      · simp [shiftedSlice, bucket, shiftPacked, pack, h, ih]
      · simp [shiftedSlice, bucket, shiftPacked, pack, h, ih]

def substitute (inputs : ℕ → Poly) (op : Poly) (B j : ℕ) : Packed :=
  reduce op.length (op.map fun t => sortPacked
    (shiftedSlice t.1 (encode t.2.2) B j (inputs t.2.1)))

theorem eval_substitute (v : ℕ → ℂ) (inputs : ℕ → Poly)
    (op : Poly) (B j : ℕ) :
    evalPacked v (substitute inputs op B j) =
    evalPacked v (bucket B j (substitutePacked inputs op)) := by
  simp only [substitute, shiftedSlice_eq, substitutePacked, eval_bucket,
    eval_reduce, List.map_map, Function.comp_def, eval_sortPacked,
    eval_bucket, eval_shiftPacked_sort]

theorem substitution_zero (x y z w a b c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (inputs : ℕ → Poly) (op : Poly) (B : ℕ) (hB : 0 < B)
    (hb : ∀ t ∈ op, Small t.2.2 ∧ ∀ u ∈ inputs t.2.1, Small u.2.2)
    (h : ∀ j < B, substitute inputs op B j = []) :
    eval x y z w a b c (fun i => eval x y z w a b c (fun _ => 1) (inputs i)) op = 0 := by
  rw [← eval_substitutePacked x y z w a b c hx hy hz hw inputs op hb,
    eval_decompose _ B hB]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← eval_substitute, h j (Finset.mem_range.mp hj)]
  rfl

#print axioms shiftedSlice_eq
#print axioms eval_substitute
#print axioms substitution_zero
end QuantitativeArithmeticCoefficientSlices
