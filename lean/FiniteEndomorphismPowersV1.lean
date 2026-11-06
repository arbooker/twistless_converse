module

/- Every self-map of a finite set has a positive idempotent iterate. -/
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace FiniteEndomorphismPowers

variable {A : Type*}

theorem repeat_eventually {f : A → A} {i d : ℕ}
    (h : f^[i+d] = f^[i]) {n : ℕ} (hn : i ≤ n) :
    f^[n+d] = f^[n] := by
  have he : n-i+i = n := Nat.sub_add_cancel hn
  calc
    f^[n+d] = f^[n-i+(i+d)] := by congr 1; omega
    _ = f^[n-i] ∘ f^[i+d] := Function.iterate_add _ _ _
    _ = f^[n-i] ∘ f^[i] := by rw [h]
    _ = f^[n-i+i] := (Function.iterate_add _ _ _).symm
    _ = f^[n] := by rw [he]

theorem repeat_multiple {f : A → A} {i d : ℕ}
    (h : f^[i+d] = f^[i]) {n : ℕ} (hn : i ≤ n) (t : ℕ) :
    f^[n+t*d] = f^[n] := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he : n+(t+1)*d = (n+t*d)+d := by simp [Nat.add_mul, Nat.add_assoc]
    rw [he, repeat_eventually h (show i ≤ n+t*d by omega), ih]

/-- Every self-map of a finite set has an idempotent positive iterate. -/
theorem exists_idempotent_iterate [Fintype A] (f : A → A) :
    ∃ m, 0 < m ∧ ∀ a, f^[m] (f^[m] a) = f^[m] a := by
  classical
  obtain ⟨i, j, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n])
  have hh : ∃ i j, i < j ∧ f^[i] = f^[j] := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  obtain ⟨i, j, hij, he⟩ := hh
  let d := j-i
  have hd : 0 < d := by dsimp [d]; omega
  have hp : f^[i+d] = f^[i] := by
    have : i+d = j := by dsimp [d]; omega
    rw [this, he]
  let m := (i+1)*d
  have hm : 0 < m := Nat.mul_pos (by omega) hd
  have hmi : i ≤ m := by dsimp [m]; nlinarith
  have hperiod := repeat_multiple hp hmi (i+1)
  have hid : f^[m+m] = f^[m] := hperiod
  refine ⟨m, hm, fun a => ?_⟩
  rw [← Function.iterate_add_apply, hid]

#print axioms exists_idempotent_iterate

end FiniteEndomorphismPowers
