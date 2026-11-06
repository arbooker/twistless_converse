module

public import QuantitativeMaassHeckeTreeReductionV1

set_option autoImplicit false
@[expose] public section

open Matrix
open scoped Matrix

namespace QuantitativeMaass

/-- Literal integral upper-triangular matrices, without quotient assumptions. -/
structure HeckeUpper where
  a : ℤ
  b : ℤ
  d : ℤ
deriving DecidableEq

namespace HeckeUpper

def matrix (M : HeckeUpper) : Matrix (Fin 2) (Fin 2) ℤ := !![M.a,M.b;0,M.d]

def det (M : HeckeUpper) : ℤ := M.a * M.d

def primitive (p : ℕ) (M : HeckeUpper) : Prop :=
  ¬ ((p : ℤ) ∣ M.a ∧ (p : ℤ) ∣ M.b ∧ (p : ℤ) ∣ M.d)

def left (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper) : HeckeUpper :=
  match j with
  | none => ⟨p * M.a, p * M.b, M.d⟩
  | some u => ⟨M.a, M.b + (u.val : ℤ) * M.d, p * M.d⟩

def branchMatrix (p : ℕ) (j : Option (ZMod p)) : Matrix (Fin 2) (Fin 2) ℤ :=
  match j with
  | none => !![p,0;0,1]
  | some u => !![1,(u.val : ℤ);0,p]

theorem left_matrix (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper) :
    (left p j M).matrix = branchMatrix p j * M.matrix := by
  cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [matrix, left, branchMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_matrix (M : HeckeUpper) : M.matrix.det = M.det := by
  simp [matrix, det, Matrix.det_fin_two]

theorem left_det (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper) :
    (left p j M).det = p * M.det := by
  cases j <;> simp [left, det] <;> ring

def cancels (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper) : Prop :=
  (p : ℤ) ∣ (left p j M).a ∧ (p : ℤ) ∣ (left p j M).b ∧
    (p : ℤ) ∣ (left p j M).d

instance (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper) :
    Decidable (cancels p j M) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem none_cancels_iff (p : ℕ) (M : HeckeUpper) :
    cancels p none M ↔ (p : ℤ) ∣ M.d := by
  simp [cancels, left]

theorem some_cancels_iff (p : ℕ) (u : ZMod p) (M : HeckeUpper) :
    cancels p (some u) M ↔ (p : ℤ) ∣ M.a ∧ (p : ℤ) ∣ M.b + (u.val : ℤ) * M.d := by
  simp [cancels, left]

theorem cancels_mod_iff (p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) (M : HeckeUpper) :
    cancels p j M ↔
      heckeBranchMod j * !![(M.a : ZMod p),(M.b : ZMod p);0,(M.d : ZMod p)] = 0 := by
  cases j with
  | none => rw [none_cancels_iff, heckeBranchMod_none_zero_iff,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  | some u =>
    rw [some_cancels_iff, heckeBranchMod_some_zero_iff]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd M.a p,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd (M.b + (u.val : ℤ) * M.d) p]
    simp

/-- Unique cancellation for the actual p+1 integral representatives. -/
theorem unique_cancel (p : ℕ) [Fact p.Prime] (M : HeckeUpper)
    (hM : primitive p M) (hdet : (p : ℤ) ∣ M.det) :
    ∃! j : Option (ZMod p), cancels p j M := by
  have hpmod : ¬ ((M.a : ZMod p) = 0 ∧ (M.b : ZMod p) = 0 ∧ (M.d : ZMod p) = 0) := by
    simpa only [primitive, ZMod.intCast_zmod_eq_zero_iff_dvd] using hM
  have hdmod : (M.a : ZMod p) * (M.d : ZMod p) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdet
  simpa only [← cancels_mod_iff] using
    heckeBranchMod_unique_cancel (M.a : ZMod p) (M.b : ZMod p) (M.d : ZMod p) hpmod hdmod

theorem no_cancel (p : ℕ) [Fact p.Prime] (M : HeckeUpper)
    (hdet : ¬ (p : ℤ) ∣ M.det) (j : Option (ZMod p)) : ¬ cancels p j M := by
  rw [cancels_mod_iff]
  apply heckeBranchMod_no_cancel
  intro h
  apply hdet
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd M.det p).mp
  simpa only [det, Int.cast_mul] using h

/-- Remove the one scalar factor p exactly when all entries are divisible. -/
def next (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper) : HeckeUpper :=
  if cancels p j M then
    ⟨(left p j M).a / p, (left p j M).b / p, (left p j M).d / p⟩
  else left p j M

theorem next_of_not_cancel (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper)
    (h : ¬ cancels p j M) : next p j M = left p j M := ite_eq_right h

theorem next_of_cancel (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper)
    (h : cancels p j M) : next p j M =
      ⟨(left p j M).a / p, (left p j M).b / p, (left p j M).d / p⟩ := ite_eq_left h

theorem next_none_of_cancel (p : ℕ) (hp : (p : ℤ) ≠ 0) (M : HeckeUpper)
    (h : cancels p none M) : next p none M = ⟨M.a, M.b, M.d / p⟩ := by
  rw [next_of_cancel p none M h]
  simp only [left, Int.mul_ediv_cancel_left _ hp]

theorem next_some_of_cancel (p : ℕ) (hp : (p : ℤ) ≠ 0) (u : ZMod p) (M : HeckeUpper)
    (h : cancels p (some u) M) :
    next p (some u) M = ⟨M.a / p, (M.b + (u.val : ℤ)*M.d) / p, M.d⟩ := by
  rw [next_of_cancel p (some u) M h]
  simp only [left, Int.mul_ediv_cancel_left _ hp]

/-- Removing the cancelling scalar leaves a primitive matrix. -/
theorem next_primitive (p : ℕ) (hp : (p : ℤ) ≠ 0) (j : Option (ZMod p))
    (M : HeckeUpper) (hM : primitive p M) : primitive p (next p j M) := by
  by_cases hc : cancels p j M
  · cases j with
    | none =>
      rw [next_none_of_cancel p hp M hc]
      rintro ⟨ha, hb, _⟩
      exact hM ⟨ha, hb, (none_cancels_iff p M).mp hc⟩
    | some u =>
      rw [next_some_of_cancel p hp u M hc]
      rintro ⟨_, _, hd⟩
      obtain ⟨ha, hb⟩ := (some_cancels_iff p u M).mp hc
      have hb' : (p : ℤ) ∣ M.b := by
        simpa only [add_sub_cancel_right] using
          dvd_sub hb (dvd_mul_of_dvd_right hd (u.val : ℤ))
      exact hM ⟨ha, hb', hd⟩
  · rw [next_of_not_cancel p j M hc]
    exact hc

/-- Exact integral determinant drop at the cancelling branch. -/
theorem next_det_cancel (p : ℕ) (hp : (p : ℤ) ≠ 0) (j : Option (ZMod p))
    (M : HeckeUpper) (hc : cancels p j M) :
    (p : ℤ) * (next p j M).det = M.det := by
  cases j with
  | none =>
    rw [next_none_of_cancel p hp M hc]
    have hd := Int.ediv_mul_cancel ((none_cancels_iff p M).mp hc)
    change (p : ℤ) * (M.a * (M.d / p)) = M.a * M.d
    linear_combination M.a * hd
  | some u =>
    rw [next_some_of_cancel p hp u M hc]
    have ha := Int.ediv_mul_cancel ((some_cancels_iff p u M).mp hc).1
    change (p : ℤ) * ((M.a / p) * M.d) = M.a * M.d
    linear_combination M.d * ha

theorem next_det_forward (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper)
    (hc : ¬ cancels p j M) : (next p j M).det = p * M.det := by
  rw [next_of_not_cancel p j M hc, left_det]

end HeckeUpper

#print axioms HeckeUpper.left_matrix
#print axioms HeckeUpper.unique_cancel
#print axioms HeckeUpper.no_cancel
#print axioms HeckeUpper.next_primitive
#print axioms HeckeUpper.next_det_cancel
#print axioms HeckeUpper.next_det_forward

end QuantitativeMaass
