module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

open Matrix
open scoped Matrix

namespace QuantitativeMaass

section ResidueField

variable {F : Type*} [Field F]

/-- The reductions modulo p of the literal unramified Hecke representatives
diag(p,1) and [[1,j],[0,p]]. None denotes the first representative. -/
def heckeBranchMod (j : Option F) : Matrix (Fin 2) (Fin 2) F :=
  match j with
  | none => !![0, 0; 0, 1]
  | some u => !![1, u; 0, 0]

theorem heckeBranchMod_none_product (a b d : F) :
    heckeBranchMod none * !![a,b;0,d] = !![0,0;0,d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeBranchMod, Matrix.mul_apply, Fin.sum_univ_two]

theorem heckeBranchMod_some_product (u a b d : F) :
    heckeBranchMod (some u) * !![a,b;0,d] = !![a,b + u*d;0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeBranchMod, Matrix.mul_apply, Fin.sum_univ_two]

theorem heckeBranchMod_none_zero_iff (a b d : F) :
    heckeBranchMod none * !![a,b;0,d] = 0 ↔ d = 0 := by
  rw [heckeBranchMod_none_product]
  constructor
  · intro h
    exact congrArg (fun M => M 1 1) h
  · intro h
    subst d
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem heckeBranchMod_some_zero_iff (u a b d : F) :
    heckeBranchMod (some u) * !![a,b;0,d] = 0 ↔ a = 0 ∧ b + u*d = 0 := by
  rw [heckeBranchMod_some_product]
  constructor
  · intro h
    exact ⟨congrArg (fun M => M 0 0) h, congrArg (fun M => M 0 1) h⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- Exactly one literal Hecke branch cancels modulo p at a nonzero
upper-triangular matrix of determinant zero. This is the arithmetic source
of the single backward edge; no graph or spectral law is assumed. -/
theorem heckeBranchMod_unique_cancel (a b d : F)
    (hprimitive : ¬ (a = 0 ∧ b = 0 ∧ d = 0)) (hdet : a*d = 0) :
    ∃! j : Option F, heckeBranchMod j * !![a,b;0,d] = 0 := by
  by_cases hd : d = 0
  · refine ⟨none, (heckeBranchMod_none_zero_iff a b d).mpr hd, ?_⟩
    intro j hj
    cases j with
    | none => rfl
    | some u =>
      obtain ⟨ha, hb⟩ := (heckeBranchMod_some_zero_iff u a b d).mp hj
      have hb' : b = 0 := by simpa only [hd, mul_zero, add_zero] using hb
      exact False.elim (hprimitive ⟨ha, hb', hd⟩)
  · have ha : a = 0 := (mul_eq_zero.mp hdet).resolve_right hd
    refine ⟨some (-b/d), (heckeBranchMod_some_zero_iff _ a b d).mpr ⟨ha, ?_⟩, ?_⟩
    · rw [div_mul_cancel₀ _ hd]
      exact add_neg_cancel b
    · intro j hj
      cases j with
      | none => exact False.elim (hd ((heckeBranchMod_none_zero_iff a b d).mp hj))
      | some u =>
        apply congrArg some
        apply (eq_div_iff hd).mpr
        have hb := ((heckeBranchMod_some_zero_iff u a b d).mp hj).2
        linear_combination hb

/-- At determinant nonzero there is no cancellation, giving all p+1
forward branches at the root. -/
theorem heckeBranchMod_no_cancel (a b d : F) (hdet : a*d ≠ 0) (j : Option F) :
    heckeBranchMod j * !![a,b;0,d] ≠ 0 := by
  intro hj
  cases j with
  | none =>
    have hd := (heckeBranchMod_none_zero_iff a b d).mp hj
    exact hdet (by rw [hd, mul_zero])
  | some u =>
    have ha := ((heckeBranchMod_some_zero_iff u a b d).mp hj).1
    exact hdet (by rw [ha, zero_mul])

end ResidueField

#print axioms heckeBranchMod_unique_cancel
#print axioms heckeBranchMod_no_cancel

end QuantitativeMaass
