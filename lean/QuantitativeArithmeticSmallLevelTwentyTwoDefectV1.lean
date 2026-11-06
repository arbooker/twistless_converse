module

public import QuantitativeArithmeticSmallLevelTwentyTwoPairsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open scoped MatrixGroups ModularForm

def W : GL (Fin 2) ℝ := fricke 22 (by decide)
def K : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ Y⁻¹*W⁻¹*translation (2/3)
def R : GL (Fin 2) ℝ := translation (-1)*W*E
def L : GL (Fin 2) ℝ := R*translation (2/3)
def S : GL (Fin 2) ℝ := W*translation (-1)*E⁻¹

private theorem sign_inverse (F : ℍ→ℂ) (k : ℤ) (M : GL (Fin 2) ℝ)
    (hdet : (GeneralLinearGroup.det M:ℝ)=1) (χ : ℂ) (hχ : χ=1 ∨ χ= -1)
    (hM : F ∣[k] M=χ • F) : F ∣[k] M⁻¹=χ • F := by
  have h := congrArg (fun g : ℍ → ℂ => g ∣[k] M⁻¹) hM
  rw [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,
    det_one_smul _ (det_one_inv _ hdet)] at h
  rcases hχ with rfl|rfl
  · simpa only [one_smul] using h.symm
  · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm

theorem E_explicit : E=matrix (2/Real.sqrt 2) (-1/Real.sqrt 2)
    (-22/Real.sqrt 2) (12/Real.sqrt 2) (by
      have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SmallLevelRamifiedTwo.Q,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp <;> nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem W_inverse : W⁻¹=matrix 0 (1/Real.sqrt 22) (-Real.sqrt 22) 0 (by
    field_simp; ring) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem Y_K : SpecialLinearGroup.mapGL ℝ Y*K=W⁻¹*translation (2/3) := by
  simp only [K,← mul_assoc,← map_mul,mul_inv_cancel,map_one,one_mul]

theorem K_alternate : K=(-1:GL (Fin 2) ℝ)*W*SpecialLinearGroup.mapGL ℝ X*translation (2/3) := by
  apply mul_left_cancel (a:=SpecialLinearGroup.mapGL ℝ Y)
  rw [Y_K,W_inverse]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X,Y,W,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem X_conjugacy : SpecialLinearGroup.mapGL ℝ X=S*SpecialLinearGroup.mapGL ℝ Y*R := by
  rw [S,R]
  have hi : E⁻¹=SmallLevelRamifiedTwo.Q 22 12 (by decide) := inv_inv _
  rw [hi,E_explicit]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X,Y,W,fricke,translation,SmallLevelRamifiedTwo.Q,matrix,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [mul_nonneg (sq_nonneg (Real.sqrt 22)) (sq_nonneg (Real.sqrt 2))]

private theorem sub_slash (F G : ℍ→ℂ) (k : ℤ) (M : GL (Fin 2) ℝ) :
    (F-G) ∣[k] M=F ∣[k] M-G ∣[k] M := by
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]

/-- The first exact symmetry of the original denominator-three defect. -/
theorem original_K (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (η : ℂ)
    (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    let F:=SmallLevelOriginal.fourierFunction (2*m) f
    let u:=F ∣[((2*m:ℕ):ℤ)] Y-F
    u ∣[((2*m:ℕ):ℤ)] K=η • u := by
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  change F ∣[k] W=η • F at hW
  have hi:=sign_inverse F k W (fricke_det _ _) η hη hW
  have hp:=original_three_defect hf
  change F ∣[k] X-F= -(F ∣[k] Y-F) ∣[k] translation (-2/3) at hp
  change (F ∣[k] Y-F) ∣[k] K=η • (F ∣[k] Y-F)
  rw [sub_slash]
  change (F ∣[k] SpecialLinearGroup.mapGL ℝ Y) ∣[k] K-F ∣[k] K=_
  rw [← SlashAction.slash_mul,Y_K,K_alternate]
  have hZ : F ∣[k] (-1:GL (Fin 2) ℝ)=F := central_even F m
  simp only [SlashAction.slash_mul,hZ,hW,hi,
    det_one_smul _ (translation_det _),det_one_smul _ (by simp :
      (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ X):ℝ)=1)]
  change η • (F ∣[k] translation (2/3))-
    η • ((F ∣[k] X) ∣[k] translation (2/3))=η • (F ∣[k] Y-F)
  rw [← smul_sub]
  congr 1
  have hh:=congrArg (fun G : ℍ→ℂ => G ∣[k] translation (2/3)) hp
  rw [sub_slash,SlashAction.neg_slash,← SlashAction.slash_mul,translation_mul,
    show (-2/3:ℝ)+2/3=0 by ring] at hh
  have h0 : translation 0=(1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [h0,SlashAction.slash_one] at hh
  linear_combination -hh

private theorem original_tminus (k : ℕ) (f : ℕ→ℂ) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-1)=
      SmallLevelOriginal.fourierFunction k f := by
  have ht : translation (-1)=SpecialLinearGroup.mapGL ℝ T⁻¹ := by
    rw [show T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
        SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
  rw [ht]
  have hh:=congrArg (fun F : ℍ→ℂ => F ∣[(k:ℤ)] (T⁻¹:SL(2,ℤ))) (original_T k f)
  simp only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hh
  exact hh.symm

/-- The second exact symmetry of the original denominator-three defect.
Both signs are the original Fricke and ramified signs, with no extra
unramified Hecke-eigenvalue hypothesis. -/
theorem original_L (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hE : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] E=
      δ • SmallLevelOriginal.fourierFunction (2*m) f)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    let F:=SmallLevelOriginal.fourierFunction (2*m) f
    let u:=F ∣[((2*m:ℕ):ℤ)] Y-F
    u ∣[((2*m:ℕ):ℤ)] L=(-δ*η) • u := by
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let u:=F ∣[k] Y-F
  have hEi:=sign_inverse F k E E_det δ hδ hE
  have ht:=original_tminus (2*m) f
  have hRdet : (GeneralLinearGroup.det R:ℝ)=1 := by
    simp only [R,map_mul,Units.val_mul,translation_det,fricke_det,W,E_det,mul_one]
  have hR : F ∣[k] R=(η*δ) • F := by
    rw [R,SlashAction.slash_mul,SlashAction.slash_mul,ht,hW,
      det_one_smul _ E_det,hE,smul_smul]
  have hS : F ∣[k] S=(η*δ) • F := by
    rw [S,SlashAction.slash_mul,SlashAction.slash_mul,hW,
      det_one_smul _ (translation_det _),ht,
      det_one_smul _ (det_one_inv _ E_det),hEi,smul_smul]
  have hx : F ∣[k] X=(η*δ) • ((F ∣[k] Y) ∣[k] R) := by
    change F ∣[k] SpecialLinearGroup.mapGL ℝ X=_
    rw [X_conjugacy,SlashAction.slash_mul,SlashAction.slash_mul,hS,
      det_one_smul _ (by simp : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ Y):ℝ)=1),
      det_one_smul _ hRdet]
    rfl
  have hdef : (η*δ) • (u ∣[k] R)=F ∣[k] X-F := by
    dsimp [u]
    rw [sub_slash,smul_sub,← hx,hR,smul_smul]
    rcases hδ with hd|hd <;> rcases hη with he|he <;> simp [hd,he]
  have hp:=original_three_defect hf
  change F ∣[k] X-F= -u ∣[k] translation (-2/3) at hp
  rw [← hdef] at hp
  have hh:=congrArg (fun G : ℍ→ℂ => G ∣[k] translation (2/3)) hp
  rw [det_one_smul _ (translation_det _),SlashAction.neg_slash,
    ← SlashAction.slash_mul,← SlashAction.slash_mul,translation_mul,
    show (-2/3:ℝ)+2/3=0 by ring] at hh
  have h0 : translation 0=(1:GL (Fin 2) ℝ) := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [h0,SlashAction.slash_one] at hh
  change (η*δ) • (u ∣[k] L)= -u at hh
  change u ∣[k] L=(-δ*η) • u
  rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;>
    simpa only [one_mul,mul_one,neg_one_mul,neg_neg,one_smul,neg_one_smul,neg_mul,
      neg_inj] using hh

/-- Both auxiliary defect laws are consequences of the literal original
solution assumptions. -/
theorem original_defect_symmetries (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ δ η : ℂ, (δ=1 ∨ δ= -1) ∧ (η=1 ∨ η= -1) ∧
      let F:=SmallLevelOriginal.fourierFunction (2*m) f
      let u:=F ∣[((2*m:ℕ):ℤ)] Y-F
      (F ∣[((2*m:ℕ):ℤ)] E=δ • F) ∧
      (F ∣[((2*m:ℕ):ℤ)] W=η • F) ∧
      (u ∣[((2*m:ℕ):ℤ)] K=η • u) ∧
      (u ∣[((2*m:ℕ):ℤ)] L=(-δ*η) • u) := by
  obtain ⟨δ,hδ,hE⟩:=original_E hf
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<22) m hf
  exact ⟨δ,η,hδ,hη,hE,hW,original_K m hf η hη hW,original_L m hf δ η hδ hη hE hW⟩

#print axioms original_L
#print axioms original_defect_symmetries

#print axioms original_K
end QuantitativeArithmeticSmallLevelTwentyTwo
