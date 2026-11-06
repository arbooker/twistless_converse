module
public import SmallLevelThirtyFourPrimeFiveTheoryV4
public import SmallLevelElevenDefectV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPrimeFive
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

private theorem branch_factor (W L H R T : GL (Fin 2) ℝ)
    (h : W*H*T=R*L) : W⁻¹*R*L=H*T := by
  calc
    W⁻¹*R*L=W⁻¹*(R*L) := mul_assoc _ _ _
    _=W⁻¹*(W*H*T) := by rw [h]
    _=H*T := by group

/-- The exact four-term defect identity follows from the original
prime-five Ramanujan functional equation, for every eigenvalue. -/
theorem original_defect_sum {k : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] G1)-SmallLevelOriginal.fourierFunction k f) ∣[(k:ℤ)] translation (1/5)+
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] Gm1)-SmallLevelOriginal.fourierFunction k f) ∣[(k:ℤ)] translation (-(1/5))+
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] G2)-SmallLevelOriginal.fourierFunction k f) ∣[(k:ℤ)] translation (-(2/5))+
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] Gm2)-SmallLevelOriginal.fourierFunction k f) ∣[(k:ℤ)] translation (2/5)=0 := by
  have h := original_five_fricke hf
  have h0 := branch_factor (fricke 34 (by decide)) (fricke 850 (by decide))
    (SpecialLinearGroup.mapGL ℝ G1) (translation (1/5)) (translation (1/5)) G1_branch
  have h1 := branch_factor (fricke 34 (by decide)) (fricke 850 (by decide))
    (SpecialLinearGroup.mapGL ℝ Gm1) (translation (-(1/5))) (translation (-(1/5))) Gm1_branch
  have h2 := branch_factor (fricke 34 (by decide)) (fricke 850 (by decide))
    (SpecialLinearGroup.mapGL ℝ G2) (translation (2/5)) (translation (-(2/5))) G2_branch
  have h3 := branch_factor (fricke 34 (by decide)) (fricke 850 (by decide))
    (SpecialLinearGroup.mapGL ℝ Gm2) (translation (-(2/5))) (translation (2/5)) Gm2_branch
  rw [h0,h1,h2,h3] at h
  simp only [SlashAction.slash_mul] at h
  simp only [SmallLevelEleven.sub_slash]
  linear_combination h

#print axioms original_defect_sum
end SmallLevelThirtyFourPrimeFive
