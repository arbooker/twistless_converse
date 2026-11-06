module
public import QuantitativeArithmeticPackedIntegerSubstitutionV1
set_option autoImplicit false
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace QuantitativeArithmeticPackedBuckets
open QuantitativeArithmeticIntegerSevenLaurentRows
open QuantitativeArithmeticPackedIntegerSubstitution
open scoped BigOperators

/-! Decompose a polynomial certificate by exponent-code residue. Each piece
can be checked independently in the same module. The number of pieces affects
only computation, not the mathematical hypotheses of the certificate. -/
def bucket (B j : ℕ) (p : Packed) : Packed :=
  p.filter fun t => t.2 % B = j

theorem eval_bucket (v : ℕ → ℂ) (B j : ℕ) (p : Packed) :
    evalPacked v (bucket B j p) =
    evalPacked (fun code => if code % B = j then v code else 0) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      by_cases h : t.2 % B = j
      · simp [bucket, h, evalPacked_cons, ← ih]
      · simp [bucket, h, evalPacked_cons, ← ih]

theorem eval_sum {ι : Type*} (s : Finset ι) (v : ι → ℕ → ℂ) (p : Packed) :
    evalPacked (fun code => ∑ i ∈ s, v i code) p =
    ∑ i ∈ s, evalPacked (v i) p := by
  induction p with
  | nil => simp
  | cons t p ih =>
      simp only [evalPacked_cons, ih, Finset.mul_sum, Finset.sum_add_distrib]

theorem eval_decompose (v : ℕ → ℂ) (B : ℕ) (hB : 0 < B) (p : Packed) :
    evalPacked v p = ∑ j ∈ Finset.range B, evalPacked v (bucket B j p) := by
  simp only [eval_bucket, ← eval_sum]
  congr 1
  funext code
  simp [Nat.mod_lt code hB]

def substituteBucket (inputs : ℕ → Poly) (op : Poly) (B j : ℕ) : Packed :=
  reduce op.length (op.map fun t => bucket B j
    (shiftPacked t.1 (QuantitativeArithmeticExponentEncoding.encode t.2.2)
      (sortPacked (pack (inputs t.2.1)))))

theorem eval_substituteBucket (v : ℕ → ℂ) (inputs : ℕ → Poly)
    (op : Poly) (B j : ℕ) :
    evalPacked v (substituteBucket inputs op B j) =
    evalPacked v (bucket B j (substitutePacked inputs op)) := by
  simp only [substituteBucket, substitutePacked, eval_bucket, eval_reduce, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  exact eval_bucket v B j _

theorem packed_zero_of_buckets (v : ℕ → ℂ) (inputs : ℕ → Poly)
    (op : Poly) (B : ℕ) (hB : 0 < B)
    (h : ∀ j < B, substituteBucket inputs op B j = []) :
    evalPacked v (substitutePacked inputs op) = 0 := by
  rw [eval_decompose v B hB]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← eval_substituteBucket, h j (Finset.mem_range.mp hj)]
  rfl

theorem substitution_zero (x y z w a b c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (inputs : ℕ → Poly) (op : Poly) (B : ℕ) (hB : 0 < B)
    (hb : ∀ t ∈ op, QuantitativeArithmeticExponentEncoding.Small t.2.2 ∧
      ∀ u ∈ inputs t.2.1, QuantitativeArithmeticExponentEncoding.Small u.2.2)
    (h : ∀ j < B, substituteBucket inputs op B j = []) :
    eval x y z w a b c (fun i => eval x y z w a b c (fun _ => 1) (inputs i)) op = 0 := by
  rw [← eval_substitutePacked x y z w a b c hx hy hz hw inputs op hb]
  exact packed_zero_of_buckets _ inputs op B hB h

#print axioms eval_decompose
#print axioms packed_zero_of_buckets
#print axioms substitution_zero
end QuantitativeArithmeticPackedBuckets
