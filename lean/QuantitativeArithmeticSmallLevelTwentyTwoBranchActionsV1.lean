module

public import QuantitativeArithmeticSmallLevelTwentyTwoFinishBranchesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

private theorem W_det : (GeneralLinearGroup.det W:ℝ)=1 := fricke_det _ _
private theorem Ei_det : (GeneralLinearGroup.det E⁻¹:ℝ)=1 := det_one_inv _ E_det

private theorem sub_slash (F G : ℍ→ℂ) (k : ℤ) (M : GL (Fin 2) ℝ) :
    (F-G) ∣[k] M=F ∣[k] M-G ∣[k] M := by
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]

variable (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
variable (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
variable (hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F)
variable (hTm : F ∣[((2*m:ℕ):ℤ)] translation (-1)=F)
variable (hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F)
variable (hEi : F ∣[((2*m:ℕ):ℤ)] E⁻¹=δ • F)
variable (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)

include hδ hη hT hTm hE hEi hW

omit hδ hT hE hEi in
theorem M0_X_action : F ∣[((2*m:ℕ):ℤ)] (M 0*SpecialLinearGroup.mapGL ℝ X)=
    F ∣[((2*m:ℕ):ℤ)] (SpecialLinearGroup.mapGL ℝ Y*translation (-1)*M 1) := by
  have hp : F ∣[((2*m:ℕ):ℤ)] ((-1:GL (Fin 2) ℝ)*W*translation (-1)*W)=F := by
    rw [SlashAction.slash_mul,SlashAction.slash_mul,SlashAction.slash_mul,central_even F m,
      hW,det_one_smul _ (translation_det _),hTm,det_one_smul _ W_det,hW,smul_smul]
    rcases hη with rfl|rfl <;> simp
  rw [M0_X]
  simp only [SlashAction.slash_mul] at hp ⊢
  rw [hp]

omit hη hT hE hW in
theorem M1_X_action : F ∣[((2*m:ℕ):ℤ)] (M 1*SpecialLinearGroup.mapGL ℝ X)=
    F ∣[((2*m:ℕ):ℤ)] (SpecialLinearGroup.mapGL ℝ C5*M 0) := by
  have hp : F ∣[((2*m:ℕ):ℤ)] ((-1:GL (Fin 2) ℝ)*E⁻¹*translation (-1)*E⁻¹)=F := by
    rw [SlashAction.slash_mul,SlashAction.slash_mul,SlashAction.slash_mul,central_even F m,
      hEi,det_one_smul _ (translation_det _),hTm,det_one_smul _ Ei_det,hEi,smul_smul]
    rcases hδ with rfl|rfl <;> simp
  rw [M1_X]
  simp only [SlashAction.slash_mul] at hp ⊢
  rw [hp]

omit hδ hTm hE hEi in
theorem M0_Y_action : F ∣[((2*m:ℕ):ℤ)] (M 0*SpecialLinearGroup.mapGL ℝ Y)=
    F ∣[((2*m:ℕ):ℤ)] (SpecialLinearGroup.mapGL ℝ X*M 1) := by
  have hp : F ∣[((2*m:ℕ):ℤ)] ((-1:GL (Fin 2) ℝ)*W*translation 1*W)=F := by
    rw [SlashAction.slash_mul,SlashAction.slash_mul,SlashAction.slash_mul,central_even F m,
      hW,det_one_smul _ (translation_det _),hT,det_one_smul _ W_det,hW,smul_smul]
    rcases hη with rfl|rfl <;> simp
  rw [M0_Y]
  simp only [SlashAction.slash_mul] at hp ⊢
  rw [hp]

omit hδ hTm hEi in
theorem M1_Y_action : F ∣[((2*m:ℕ):ℤ)] (M 1*SpecialLinearGroup.mapGL ℝ Y)=
    δ • (F ∣[((2*m:ℕ):ℤ)] (SpecialLinearGroup.mapGL ℝ B5*translation (-1)*E⁻¹*M 0)) := by
  have hp : F ∣[((2*m:ℕ):ℤ)] (W*E*translation 1*W)=δ • F := by
    rw [SlashAction.slash_mul,SlashAction.slash_mul,SlashAction.slash_mul,hW,
      det_one_smul _ E_det,hE,det_one_smul _ (translation_det _),
      det_one_smul _ (translation_det _),hT,det_one_smul _ W_det,det_one_smul _ W_det,hW,
      smul_smul,smul_smul]
    rcases hη with rfl|rfl <;> simp
  rw [M1_Y]
  simp only [SlashAction.slash_mul] at hp ⊢
  rw [hp,det_one_smul _ (by simp : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ B5):ℝ)=1),
    det_one_smul _ (translation_det _),det_one_smul _ Ei_det,det_one_smul _ (M_det _)]

omit hTm hEi in
/-- The C5 defect is an explicit translate of the P defect. -/
theorem C5_defect : F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ C5-F=
    (δ*η) • ((F ∣[((2*m:ℕ):ℤ)] P-δ • F) ∣[((2*m:ℕ):ℤ)] W) := by
  rw [C5_factor,SlashAction.slash_mul,SlashAction.slash_mul,SlashAction.slash_mul,
    SlashAction.slash_mul,hE,det_one_smul _ (translation_det _),hT,det_one_smul _ W_det,hW,
    det_one_smul _ P_det,det_one_smul _ P_det,det_one_smul _ W_det,det_one_smul _ W_det,
    sub_slash,det_one_smul _ W_det,hW]
  rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> simp [sub_eq_add_neg]

omit hT hEi in
/-- The A5 defect is an explicit translate of the same P defect. -/
theorem A5_defect : F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ A5-F=
    η • ((F ∣[((2*m:ℕ):ℤ)] P-δ • F) ∣[((2*m:ℕ):ℤ)] R) := by
  have hR : F ∣[((2*m:ℕ):ℤ)] R=(δ*η) • F := by
    rw [R,SlashAction.slash_mul,SlashAction.slash_mul,hTm,hW,det_one_smul _ E_det,hE,smul_smul]
    congr 1
    ring
  have hRd : (GeneralLinearGroup.det R:ℝ)=1 := by
    change (GeneralLinearGroup.det (translation (-1)*W*E):ℝ)=1
    rw [map_mul,map_mul,Units.val_mul,Units.val_mul,translation_det,W_det,E_det]
    norm_num
  rw [A5_factor,SlashAction.slash_mul,SlashAction.slash_mul,hW,det_one_smul _ P_det,
    det_one_smul _ hRd,sub_slash,det_one_smul _ hRd,hR]
  rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> simp [sub_eq_add_neg]

#print axioms M0_X_action
#print axioms M1_X_action
#print axioms M0_Y_action
#print axioms M1_Y_action
#print axioms C5_defect
#print axioms A5_defect
end QuantitativeArithmeticSmallLevelTwentyTwo
