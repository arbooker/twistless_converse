module

public import QuantitativeArithmeticSmallLevelTwentyTwoBranchActionsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def auxiliaryDefect (m : ℕ) (F : ℍ→ℂ) : ℍ→ℂ :=
  F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ Y-F
def pDefect (m : ℕ) (F : ℍ→ℂ) (δ : ℂ) : ℍ→ℂ := F ∣[((2*m:ℕ):ℤ)] P-δ • F

private theorem sub_slash (F G : ℍ→ℂ) (k : ℤ) (M : GL (Fin 2) ℝ) :
    (F-G) ∣[k] M=F ∣[k] M-G ∣[k] M := by
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]

/-- The first ramified branch equation for the two explicit defects. -/
theorem first_defect_relation (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F)
    (hTm : F ∣[((2*m:ℕ):ℤ)] translation (-1)=F)
    (hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F)
    (hEi : F ∣[((2*m:ℕ):ℤ)] E⁻¹=δ • F)
    (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)
    (hHecke : F ∣[((2*m:ℕ):ℤ)] M 0+F ∣[((2*m:ℕ):ℤ)] M 1=(-δ) • F)
    (hthree : F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ X-F=
      -(auxiliaryDefect m F ∣[((2*m:ℕ):ℤ)] translation (-2/3))) :
    δ • (auxiliaryDefect m F ∣[((2*m:ℕ):ℤ)] translation (-2/3))=
      auxiliaryDefect m F ∣[((2*m:ℕ):ℤ)] (translation (-1)*M 1)+
        (δ*η) • (pDefect m F δ ∣[((2*m:ℕ):ℤ)] (W*M 0)) := by
  let k : ℤ:=((2*m:ℕ):ℤ)
  have he:=congrArg (fun g : ℍ→ℂ => g ∣[k] SpecialLinearGroup.mapGL ℝ X) hHecke
  rw [SlashAction.add_slash,← SlashAction.slash_mul,← SlashAction.slash_mul,
    M0_X_action m F η hη hTm hW,M1_X_action m F δ hδ hTm hEi,
    det_one_smul _ (by simp : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ X):ℝ)=1)] at he
  have hC:=congrArg (fun g : ℍ→ℂ => g ∣[k] M 0) (C5_defect m F δ η hδ hη hT hE hW)
  rw [sub_slash,det_one_smul _ (M_det 0),← SlashAction.slash_mul,← SlashAction.slash_mul] at hC
  have hY : F ∣[k] (SpecialLinearGroup.mapGL ℝ Y*translation (-1)*M 1)-F ∣[k] M 1=
      auxiliaryDefect m F ∣[k] (translation (-1)*M 1) := by
    change F ∣[k] translation (-1)=F at hTm
    simp only [auxiliaryDefect,sub_slash,SlashAction.slash_mul,hTm]
    rfl
  funext z
  have hez:=congrFun he z
  have hCz:=congrFun hC z
  have hYz:=congrFun hY z
  have hHz:=congrFun hHecke z
  have hXz:=congrFun hthree z
  simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at *
  change δ*(auxiliaryDefect m F ∣[k] translation (-2/3)) z=
    (auxiliaryDefect m F ∣[k] (translation (-1)*M 1)) z+
      (δ*η)*((F ∣[k] P-δ • F) ∣[k] (W*M 0)) z
  linear_combination -hez+hHz+hYz+hCz+δ*hXz

/-- The separated modulus-five pair expresses B5 through the P defect. -/
theorem B5_defect (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hTm : F ∣[((2*m:ℕ):ℤ)] translation (-1)=F)
    (hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F)
    (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)
    (hfive : F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ B5-F=
      -((F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ A5-F) ∣[((2*m:ℕ):ℤ)] translation (4/5))) :
    F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ B5-F=
      (-η) • (pDefect m F δ ∣[((2*m:ℕ):ℤ)] (R*translation (4/5))) := by
  rw [hfive,A5_defect m F δ η hδ hη hTm hE hW,det_one_smul _ (translation_det _),← SlashAction.slash_mul]
  simp [pDefect]

/-- The second ramified branch equation; this uses only the one separated
modulus-five pair explicitly displayed in the hypothesis. -/
theorem second_defect_relation (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F)
    (hTm : F ∣[((2*m:ℕ):ℤ)] translation (-1)=F)
    (hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F)
    (hEi : F ∣[((2*m:ℕ):ℤ)] E⁻¹=δ • F)
    (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)
    (hHecke : F ∣[((2*m:ℕ):ℤ)] M 0+F ∣[((2*m:ℕ):ℤ)] M 1=(-δ) • F)
    (hthree : F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ X-F=
      -(auxiliaryDefect m F ∣[((2*m:ℕ):ℤ)] translation (-2/3)))
    (hfive : F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ B5-F=
      -((F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ A5-F) ∣[((2*m:ℕ):ℤ)] translation (4/5))) :
    (-δ) • auxiliaryDefect m F=
      -(auxiliaryDefect m F ∣[((2*m:ℕ):ℤ)] A0)-
        (δ*η) • (pDefect m F δ ∣[((2*m:ℕ):ℤ)] Z0) := by
  let k : ℤ:=((2*m:ℕ):ℤ)
  let v:=translation (-1)*E⁻¹*M 0
  have hvd : (GeneralLinearGroup.det v:ℝ)=1 := by
    change (GeneralLinearGroup.det (translation (-1)*E⁻¹*M 0):ℝ)=1
    rw [map_mul,map_mul,Units.val_mul,Units.val_mul,translation_det,det_one_inv _ E_det,M_det]
    norm_num
  have hv : F ∣[k] v=δ • (F ∣[k] M 0) := by
    dsimp [v]
    rw [SlashAction.slash_mul,SlashAction.slash_mul,hTm,hEi,det_one_smul _ (M_det _)]
  have he:=congrArg (fun g : ℍ→ℂ => g ∣[k] SpecialLinearGroup.mapGL ℝ Y) hHecke
  rw [SlashAction.add_slash,← SlashAction.slash_mul,← SlashAction.slash_mul,
    M0_Y_action m F η hη hT hW,M1_Y_action m F δ η hη hT hE hW,
    det_one_smul _ (by simp : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ Y):ℝ)=1)] at he
  have hB:=congrArg (fun g : ℍ→ℂ => g ∣[k] v) (B5_defect m F δ η hδ hη hTm hE hW hfive)
  rw [sub_slash,det_one_smul _ hvd,hv,← SlashAction.slash_mul,← SlashAction.slash_mul] at hB
  have hprod : R*translation (4/5)*v=Z0 := by simp only [v,Z0,mul_assoc]
  rw [hprod] at hB
  have hX:=congrArg (fun g : ℍ→ℂ => g ∣[k] M 1) hthree
  rw [sub_slash,SlashAction.neg_slash,← SlashAction.slash_mul,← SlashAction.slash_mul,branch_A0] at hX
  have hd : δ*δ=1 := by rcases hδ with rfl|rfl <;> norm_num
  funext z
  have hez:=congrFun he z
  have hBz:=congrFun hB z
  have hXz:=congrFun hX z
  have hHz:=congrFun hHecke z
  simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at *
  change -δ*((F ∣[k] SpecialLinearGroup.mapGL ℝ Y) z-F z)=
    -(auxiliaryDefect m F ∣[k] A0) z-(δ*η)*(pDefect m F δ ∣[k] Z0) z
  have hp : SpecialLinearGroup.mapGL ℝ B5*translation (-1)*E⁻¹*M 0=
      SpecialLinearGroup.mapGL ℝ B5*v := by simp only [v,mul_assoc]
  rw [hp] at hez
  linear_combination -hez+hXz+δ*hBz+hHz+(F ∣[k] M 0) z*hd

#print axioms first_defect_relation
#print axioms B5_defect
#print axioms second_defect_relation
end QuantitativeArithmeticSmallLevelTwentyTwo
