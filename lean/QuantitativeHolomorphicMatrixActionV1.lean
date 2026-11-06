module

public import QuantitativeHolomorphicAutomaticGeometryV1
public import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane AsymptoticFiniteBranch

def IntegerAction (g : AsymptoticRationalGroup.Group) (M : IntegerMatrix2) : Prop :=
  M.det ≠ 0 ∧ ∀ z : UpperHalfPlane, ((g • z : UpperHalfPlane):ℂ)=
    ((M 0 0:ℂ)*(z:ℂ)+M 0 1)/((M 1 0:ℂ)*(z:ℂ)+M 1 1)

theorem integerAction_one : IntegerAction 1 1 := by
  constructor
  · simp
  · intro z
    simp

/-- Global integer representatives multiply with the actual projective
labels. Their denominators cannot vanish anywhere in the upper half-plane. -/
theorem IntegerAction.mul {g h : AsymptoticRationalGroup.Group} {M L : IntegerMatrix2}
    (hM : IntegerAction g M) (hL : IntegerAction h L) : IntegerAction (g*h) (M*L) := by
  constructor
  · rw [Matrix.det_mul]
    exact mul_ne_zero hM.1 hL.1
  · intro z
    have hl := QuantitativeArithmetic.integer_matrix_denominator_ne_zero L hL.1 z
    have hm := QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.1 (h • z)
    have hp := QuantitativeArithmetic.integer_matrix_denominator_ne_zero (M*L)
      (by rw [Matrix.det_mul]; exact mul_ne_zero hM.1 hL.1) z
    have he : ((h • z : UpperHalfPlane):ℂ)*((L 1 0:ℂ)*(z:ℂ)+L 1 1)=
        (L 0 0:ℂ)*(z:ℂ)+L 0 1 := (eq_div_iff hl).mp (hL.2 z)
    rw [mul_smul,hM.2]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul] at hp ⊢
    apply (div_eq_div_iff hm hp).mpr
    linear_combination ((M 0 0:ℂ)*(M 1 1:ℂ)-(M 0 1:ℂ)*(M 1 0:ℂ))*he

/-- Integer adjugation represents the inverse label and does not enlarge
entry height in dimension two. -/
theorem IntegerAction.inv {g : AsymptoticRationalGroup.Group} {M : IntegerMatrix2}
    (hM : IntegerAction g M) : IntegerAction g⁻¹ M.adjugate := by
  have hd : M.adjugate.det ≠ 0 := by simpa only [Matrix.det_adjugate,Fintype.card_fin,Nat.reduceSub,pow_one] using hM.1
  refine ⟨hd,?_⟩
  intro z
  have hm := QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.1 (g⁻¹ • z)
  have ha := QuantitativeArithmetic.integer_matrix_denominator_ne_zero M.adjugate hd z
  have he := (div_eq_iff hm).mp (hM.2 (g⁻¹ • z)).symm
  simp only [smul_inv_smul] at he
  simp [Matrix.adjugate_fin_two] at ha ⊢
  apply (eq_div_iff ha).mpr
  linear_combination he

theorem matrix_entry_bound_adjugate {M : IntegerMatrix2} {B : ℝ}
    (hM : MatrixEntryBound M B) : MatrixEntryBound M.adjugate B := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.adjugate_fin_two] using hM _ _

/-- Matrix representatives concatenate in the correct order for composed
branches (the orbit label is contravariant to operator composition). -/
theorem integerAction_compose {b c : Branch} {M L : IntegerMatrix2}
    (hb : IntegerAction b.label M) (hc : IntegerAction c.label L) :
    IntegerAction (compose b c).label (L*M) := hc.mul hb

theorem integerAction_adjoint {b : Branch} {M : IntegerMatrix2}
    (hb : IntegerAction b.label M) : IntegerAction (adjoint b).label M.adjugate := hb.inv

#print axioms integerAction_one
#print axioms IntegerAction.mul
#print axioms IntegerAction.inv
#print axioms matrix_entry_bound_adjugate

end QuantitativeHolomorphic
