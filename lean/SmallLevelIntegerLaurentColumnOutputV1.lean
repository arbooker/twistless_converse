module
public import QuantitativeArithmeticIntegerSevenLaurentRowsTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelIntegerLaurentColumnOutput
open QuantitativeArithmeticIntegerSevenLaurentRows

theorem eval_perm (x y z w a b c : ℂ) (v : ℕ→ℂ) {p q : Poly}
    (h : p.Perm q) : eval x y z w a b c v p=eval x y z w a b c v q := by
  exact (h.map _).sum_eq

theorem eval_column_sum (x y z w a b c : ℂ) (v : ℕ→ℂ)
    (rows : ℕ→Poly) (is : List ℕ) (j : ℕ) :
    eval x y z w a b c v (column rows is j)=
      (is.map fun i => v i*eval x y z w a b c (fun k => if k=j then 1 else 0) (rows i)).sum := by
  induction is with
  | nil => simp [column]
  | cons i is ih => simp only [column,eval_append,eval_columnPiece,ih,List.map_cons,List.sum_cons]

/-- Transfer a staged scalar output certificate to its actual row column.
The last scalar input is the output column; the first inputs are weights. -/
theorem column_output (x y z w a b c : ℂ) (rows weights : ℕ→Poly)
    (output : Poly) (n j : ℕ)
    (hout : (weights n).Perm (columnPiece 0 j output))
    (hzero : eval x y z w a b c
      (fun i => eval x y z w a b c (fun _ => 1) (weights i))
      (column rows (List.range n) j++[(-1,n,(0,0,0,0,0,0,0))])=0) :
    eval x y z w a b c (fun k => if k=j then 1 else 0) output=
      eval x y z w a b c
        (fun i => eval x y z w a b c (fun _ => 1) (weights i))
        (column rows (List.range n) j) := by
  rw [eval_append,eval_cons,eval_nil] at hzero
  have ho := eval_perm x y z w a b c (fun _ => 1) hout
  rw [eval_columnPiece,one_mul] at ho
  rw [ho] at hzero
  norm_num [monomial] at hzero
  linear_combination -hzero

theorem output_of_columns (x y z w a b c : ℂ) (v weights : ℕ→ℂ)
    (rows : ℕ→Poly) (output : Poly) (is : List ℕ) (js : Finset ℕ)
    (hrows : ∀ i∈is,∀ t∈rows i,t.2.1∈js)
    (hout : ∀ t∈output,t.2.1∈js)
    (hcols : ∀ j∈js,eval x y z w a b c (fun k => if k=j then 1 else 0) output=
      eval x y z w a b c weights (column rows is j)) :
    eval x y z w a b c v output=
      (is.map fun i => weights i*eval x y z w a b c v (rows i)).sum := by
  rw [eval_partition x y z w a b c v js output hout,
    row_column_identity x y z w a b c weights v rows is js hrows]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcols j hj]

#print axioms column_output
#print axioms output_of_columns
end SmallLevelIntegerLaurentColumnOutput
