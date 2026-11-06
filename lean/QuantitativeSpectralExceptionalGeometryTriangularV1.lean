module

public import QuantitativeSpectralExceptionalGeometryV1
public import AsymptoticClassicalIntegralTriangularV1
public import AsymptoticClassicalTriangularSlashV1
public import Mathlib.LinearAlgebra.Matrix.Integer

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open Matrix UpperHalfPlane AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticClassicalDiscriminant AsymptoticRegularBranchFamily
open QuantitativeSpectralExceptionalReducedRows AsymptoticCongruenceLabels
open scoped MatrixGroups

/-- Clearing the common denominator gives a positive integral matrix,
without any additional arithmetic hypothesis on the rational branch. -/
theorem branch_numerator_positive (b : Branch) : 0 < b.matrix.val.num.det := by
  let D : ℝ := b.matrix.val.den
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.pos_of_ne_zero b.matrix.val.den_ne_zero
  have hn (i j : Fin 2) : (b.matrix.val.num i j : ℝ) = D * (b.matrix i j : ℝ) := by
    have hh := b.matrix.val.num_div_den i j
    have hq : (b.matrix.val.den : ℚ) ≠ 0 := by exact_mod_cast b.matrix.val.den_ne_zero
    have he := (div_eq_iff hq).mp hh
    dsimp [D]
    exact_mod_cast (he.trans (mul_comm _ _))
  have hd : (b.matrix.val.num.det : ℝ) = D^2 * (realMatrix b.matrix).det.val := by
    rw [Matrix.det_fin_two]
    simp only [Int.cast_sub,Int.cast_mul,hn]
    rw [GeneralLinearGroup.val_det_apply,Matrix.det_fin_two]
    change _ = D^2 * ((b.matrix 0 0:ℝ)*(b.matrix 1 1:ℝ) -
      (b.matrix 0 1:ℝ)*(b.matrix 1 0:ℝ))
    ring
  have hh : 0 < (b.matrix.val.num.det : ℝ) := by
    rw [hd]
    exact mul_pos (sq_pos_of_pos hD) b.positive
  exact_mod_cast hh

/-- Every positive rational branch is an integral modular matrix followed
by a positive affine map. This is the actual cusp chart needed for finite
horizontal translation reductions. -/
theorem branch_affine_chart (b : Branch) :
    ∃ U : SL(2,ℤ), ∃ α β : ℝ, ∃ hα : 0 < α,
      ∀ z : ℍ, label b • z = U • affine α hα β z := by
  obtain ⟨U,a,c,d,ha,hd,he⟩ := integral_triangular b.matrix.val.num
    (branch_numerator_positive b)
  let D : ℝ := b.matrix.val.den
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.pos_of_ne_zero b.matrix.val.den_ne_zero
  have ha' : 0 < (a:ℝ)/D := div_pos (by exact_mod_cast ha) hD
  have hd' : 0 < (d:ℝ)/D := div_pos (by exact_mod_cast hd) hD
  have hmat : realMatrix b.matrix = SpecialLinearGroup.mapGL ℝ U *
      triangularGL ((a:ℝ)/D) ((c:ℝ)/D) ((d:ℝ)/D) ha' hd' := by
    apply Units.ext
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => (M i j : ℝ)) he
    have hn : (b.matrix.val.num i j : ℝ) / D = (b.matrix i j : ℝ) := by
      have hq : (b.matrix.val.num i j : ℚ) / (b.matrix.val.den : ℚ) = b.matrix i j :=
        b.matrix.val.num_div_den i j
      have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
      simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hr
    change (b.matrix i j : ℝ) = _
    rw [← hn]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul] at hh
    fin_cases i <;> fin_cases j <;>
      simp [triangularGL,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two] at hh ⊢ <;> rw [hh] <;> ring
  refine ⟨U,((a:ℝ)/D)/((d:ℝ)/D),((c:ℝ)/D)/((d:ℝ)/D),div_pos ha' hd',?_⟩
  intro z
  rw [ofMatrix_action,hmat,mul_smul,triangularGL_action]
  rfl

#print axioms branch_numerator_positive
#print axioms branch_affine_chart

end QuantitativeSpectralExceptionalGeometry
