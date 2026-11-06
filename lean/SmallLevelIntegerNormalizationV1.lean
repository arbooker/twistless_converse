module

public import SmallLevelNormalizedMatricesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelIntegerNormalization

open Matrix SmallLevelNormalized
open scoped MatrixGroups

abbrev IntegerMatrix := Matrix (Fin 2) (Fin 2) ℤ

def normalize (X : IntegerMatrix) (d : ℕ) (hd : 0<d)
    (hX : X 0 0*X 1 1-X 0 1*X 1 0=(d:ℤ)) : GL (Fin 2) ℝ :=
  matrix ((X 0 0:ℝ)/Real.sqrt d) ((X 0 1:ℝ)/Real.sqrt d)
    ((X 1 0:ℝ)/Real.sqrt d) ((X 1 1:ℝ)/Real.sqrt d) (by
      have hs : (Real.sqrt d)^2=d := Real.sq_sqrt (by positivity)
      have hn : Real.sqrt d≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
      have he : (X 0 0:ℝ)*X 1 1-(X 0 1:ℝ)*X 1 0=d := by exact_mod_cast hX
      field_simp [hn]
      nlinarith)

theorem normalize_apply (X : IntegerMatrix) (d : ℕ) (hd : 0<d)
    (hX : X 0 0*X 1 1-X 0 1*X 1 0=(d:ℤ)) (i j : Fin 2) :
    (normalize X d hd hX).val i j=(X i j:ℝ)/Real.sqrt d := by
  fin_cases i <;> fin_cases j <;> rfl

theorem normalize_det (X : IntegerMatrix) (d : ℕ) (hd : 0<d)
    (hX : X 0 0*X 1 1-X 0 1*X 1 0=(d:ℤ)) :
    (GeneralLinearGroup.det (normalize X d hd hX):ℝ)=1 := matrix_det _ _ _ _ _

/-- A positive scalar identity between integer matrices gives an exact
identity of their determinant-one real normalizations. -/
theorem normalized_relation (X Y R : IntegerMatrix) (dx dy dr : ℕ)
    (hx : 0<dx) (hy : 0<dy) (hr : 0<dr)
    (hX : X 0 0*X 1 1-X 0 1*X 1 0=(dx:ℤ))
    (hY : Y 0 0*Y 1 1-Y 0 1*Y 1 0=(dy:ℤ))
    (hR : R 0 0*R 1 1-R 0 1*R 1 0=(dr:ℤ))
    (K : SL(2,ℤ)) (c : ℤ) (hc : 0<c)
    (hraw : X*Y=c • ((K:IntegerMatrix)*R))
    (hdet : (dx:ℤ)*dy=c^2*dr) :
    normalize X dx hx hX*normalize Y dy hy hY=
      SpecialLinearGroup.mapGL ℝ K*normalize R dr hr hR := by
  have hcx : (c:ℝ)≠0 := by exact_mod_cast hc.ne'
  have hnx : Real.sqrt dx≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hx)).ne'
  have hny : Real.sqrt dy≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hy)).ne'
  have hnr : Real.sqrt dr≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  have hs : Real.sqrt dx*Real.sqrt dy=(c:ℝ)*Real.sqrt dr := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (dx:ℝ)*dy=(c:ℝ)^2*dr by exact_mod_cast hdet,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by exact_mod_cast hc.le)]
  apply Units.ext
  ext i j
  have he : (X i 0:ℝ)*(Y 0 j:ℝ)+(X i 1:ℝ)*(Y 1 j:ℝ)=
      (c:ℝ)*((K i 0:ℝ)*(R 0 j:ℝ)+(K i 1:ℝ)*(R 1 j:ℝ)) := by
    have h := congrArg (fun M : IntegerMatrix => M i j) hraw
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul] at h
    exact_mod_cast h
  simp only [Units.val_mul,Matrix.mul_apply,Fin.sum_univ_two,normalize_apply]
  change ((X i 0:ℝ)/Real.sqrt dx)*((Y 0 j:ℝ)/Real.sqrt dy)+
      ((X i 1:ℝ)/Real.sqrt dx)*((Y 1 j:ℝ)/Real.sqrt dy)=
    (K i 0:ℝ)*((R 0 j:ℝ)/Real.sqrt dr)+(K i 1:ℝ)*((R 1 j:ℝ)/Real.sqrt dr)
  calc
    _ = ((X i 0:ℝ)*Y 0 j+(X i 1:ℝ)*Y 1 j)/(Real.sqrt dx*Real.sqrt dy) := by
      field_simp
    _ = _ := by
      rw [hs,he]
      field_simp

#print axioms normalized_relation

end SmallLevelIntegerNormalization
