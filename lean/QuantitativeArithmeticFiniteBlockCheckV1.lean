module
public import Mathlib.Data.List.FinRange
public import Lean.Elab.Tactic.Omega
set_option autoImplicit false
@[expose] public section
namespace QuantitativeArithmeticFiniteBlockCheck

/-- Check a consecutive part of a finite table. Entries beyond its end are
ignored, so the last part needs no padding or a second certificate format. -/
def window {n : ℕ} (f : Fin n → Bool) (start width : ℕ) : Bool :=
  (List.range width).all (fun j => if h : start+j<n then f ⟨start+j,h⟩ else true)

theorem window_sound {n start width : ℕ} {f : Fin n → Bool}
    (h : window f start width = true) (i : Fin n)
    (hlo : start ≤ i.val) (hhi : i.val < start+width) : f i = true := by
  have hj : i.val-start < width := by omega
  have he : start+(i.val-start)=i.val := by omega
  have hf := (List.all_eq_true.mp h) (i.val-start) (List.mem_range.mpr hj)
  simpa only [he, dite_eq_left i.isLt] using hf

/-- Assemble bounded kernel computations into a proof about the whole table.
This controls checker memory without creating a file for each computation. -/
theorem blocks_sound {n width count : ℕ} {f : Fin n → Bool}
    (hwidth : 0<width) (hcover : n ≤ count*width)
    (h : ∀ b : Fin count, window f (b.val*width) width = true)
    (i : Fin n) : f i = true := by
  have hrem := Nat.mod_lt i.val hwidth
  have hdiv := Nat.div_add_mod i.val width
  rw [Nat.mul_comm width] at hdiv
  have hb : i.val / width < count := by
    apply (Nat.div_lt_iff_lt_mul hwidth).mpr
    exact lt_of_lt_of_le i.isLt hcover
  apply window_sound (h ⟨i.val / width,hb⟩) i
  · change i.val / width * width ≤ i.val
    omega
  · change i.val < i.val / width * width + width
    omega

#print axioms blocks_sound
end QuantitativeArithmeticFiniteBlockCheck
