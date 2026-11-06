module

public import SmallLevelOddFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelRamifiedTwo

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem sqrt_two_ne : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem normalized_det (N a : ℕ) (ha : 2*a=N+2) :
    (!![(a:ℝ)/Real.sqrt 2,1/Real.sqrt 2;(N:ℝ)/Real.sqrt 2,2/Real.sqrt 2]).det=1 := by
  have hh : 2*(a:ℝ)=(N:ℝ)+2 := by exact_mod_cast ha
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  simp only [det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp [sqrt_two_ne]
  nlinarith

/-- Determinant-one normalization of the ramified modulus-two matrix. -/
def Q (N a : ℕ) (ha : 2*a=N+2) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero
    !![(a:ℝ)/Real.sqrt 2,1/Real.sqrt 2;(N:ℝ)/Real.sqrt 2,2/Real.sqrt 2]
    (by rw [normalized_det N a ha]; norm_num)

theorem Q_det (N a : ℕ) (ha : 2*a=N+2) : (GeneralLinearGroup.det (Q N a ha):ℝ)=1 :=
  normalized_det N a ha

theorem Q_denom (N a : ℕ) (ha : 2*a=N+2) (z : ℍ) :
    denom (Q N a ha) z=((N:ℂ)*(z:ℂ)+2)/(Real.sqrt 2:ℂ) := by
  change (((N:ℝ)/Real.sqrt 2:ℝ):ℂ)*(z:ℂ)+((2/Real.sqrt 2:ℝ):ℂ)=_
  push_cast
  ring

theorem Q_point (N a : ℕ) (ha : 2*a=N+2) (z : ℍ) :
    ((Q N a ha • z : ℍ):ℂ)=((a:ℂ)*(z:ℂ)+1)/((N:ℂ)*(z:ℂ)+2) := by
  rw [coe_smul_of_det_pos (by rw [Q_det]; norm_num)]
  have hs : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr sqrt_two_ne
  change ((((a:ℝ)/Real.sqrt 2:ℝ):ℂ)*(z:ℂ)+((1/Real.sqrt 2:ℝ):ℂ))/
    ((((N:ℝ)/Real.sqrt 2:ℝ):ℂ)*(z:ℂ)+((2/Real.sqrt 2:ℝ):ℂ))=_
  push_cast
  field_simp [hs]

theorem Q_slash (N a : ℕ) (ha : 2*a=N+2) (F : ℍ → ℂ) (k : ℤ) (z : ℍ) :
    (F ∣[k] Q N a ha) z=F (Q N a ha • z)*
      (((N:ℂ)*(z:ℂ)+2)/(Real.sqrt 2:ℂ))^(-k) := by
  rw [ModularForm.slash_apply]
  have hs : σ (Q N a ha)=ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [σ, Q_det]; norm_num
  rw [hs, Q_det, Q_denom]
  norm_num

#print axioms normalized_det
#print axioms Q_point
#print axioms Q_slash

end SmallLevelRamifiedTwo
