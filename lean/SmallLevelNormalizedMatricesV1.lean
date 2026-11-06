module

public import SmallLevelRamifiedTwoActionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelNormalized

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

def matrix (a b c d : ℝ) (h : a*d-b*c=1) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![a,b;c,d] (by simp [det_fin_two, h])

theorem matrix_det (a b c d : ℝ) (h : a*d-b*c=1) :
    (GeneralLinearGroup.det (matrix a b c d h):ℝ)=1 := by
  simpa [matrix, det_fin_two] using h

theorem det_one_slash (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (F : ℍ → ℂ) (k : ℤ) (z : ℍ) :
    (F ∣[k] g) z=F (g • z)*denom g z^(-k) := by
  rw [ModularForm.slash_apply]
  have hs : σ g=ContinuousAlgEquiv.refl ℝ ℂ := by simp only [σ, hg]; norm_num
  rw [hs, hg]
  norm_num

theorem det_one_smul (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (F : ℍ → ℂ) (k : ℤ) (c : ℂ) : (c • F) ∣[k] g=c • (F ∣[k] g) := by
  rw [ModularForm.smul_slash]
  have hs : σ g=ContinuousAlgEquiv.refl ℝ ℂ := by simp only [σ, hg]; norm_num
  rw [hs, ContinuousAlgEquiv.refl_apply]

theorem det_one_inv (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1) :
    (GeneralLinearGroup.det g⁻¹:ℝ)=1 := by
  simpa using congrArg (fun x : ℝ => x⁻¹) hg

def translation (r : ℝ) : GL (Fin 2) ℝ := matrix 1 r 0 1 (by ring)

theorem translation_det (r : ℝ) : (GeneralLinearGroup.det (translation r):ℝ)=1 :=
  matrix_det _ _ _ _ _

theorem translation_point (r : ℝ) (z : ℍ) :
    ((translation r • z : ℍ):ℂ)=(z:ℂ)+r := by
  rw [coe_smul_of_det_pos (by rw [translation_det]; norm_num)]
  change (1*(z:ℂ)+(r:ℂ))/(0*(z:ℂ)+1)=_
  ring

theorem translation_slash (r : ℝ) (F : ℍ → ℂ) (k : ℤ) (z : ℍ) :
    (F ∣[k] translation r) z=F (translation r • z) := by
  rw [det_one_slash _ (translation_det _) F k]
  have hd : denom (translation r) z=1 := by
    change 0*(z:ℂ)+1=1
    ring
  rw [hd, one_zpow, mul_one]

theorem translation_mul (r s : ℝ) : translation r*translation s=translation (r+s) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translation, matrix, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def fricke (N : ℕ) (hN : 0<N) : GL (Fin 2) ℝ :=
  matrix 0 (-1/Real.sqrt N) (Real.sqrt N) 0 (by
    have hs : Real.sqrt N≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
    field_simp
    norm_num)

theorem fricke_det (N : ℕ) (hN : 0<N) : (GeneralLinearGroup.det (fricke N hN):ℝ)=1 :=
  matrix_det _ _ _ _ _

theorem fricke_denom (N : ℕ) (hN : 0<N) (z : ℍ) :
    denom (fricke N hN) z=(Real.sqrt N:ℂ)*(z:ℂ) := by
  change (Real.sqrt N:ℂ)*(z:ℂ)+0=_
  ring

theorem fricke_point (N : ℕ) (hN : 0<N) (z : ℍ) :
    ((fricke N hN • z : ℍ):ℂ)= -1/((N:ℂ)*(z:ℂ)) := by
  rw [coe_smul_of_det_pos (by rw [fricke_det]; norm_num)]
  change (0*(z:ℂ)+((-1/Real.sqrt N:ℝ):ℂ))/((Real.sqrt N:ℂ)*(z:ℂ)+0)=_
  have hs : (Real.sqrt N:ℂ)^2=(N:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N : (0:ℝ)≤N)
  push_cast
  simp only [zero_mul, zero_add, add_zero]
  rw [← hs]
  field_simp

#print axioms det_one_slash
#print axioms translation_point
#print axioms fricke_point

end SmallLevelNormalized
