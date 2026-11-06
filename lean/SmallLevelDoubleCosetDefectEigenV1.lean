module

public import SmallLevelNormalizedMatricesV1
public import SmallLevelElevenDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelNormalized

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem double_coset_defect_eigen (g : ℍ → ℂ) (k : ℤ) (C Cp L R E : GL (Fin 2) ℝ)
    (hRdet : (GeneralLinearGroup.det R:ℝ)=1)
    (hCdet : (GeneralLinearGroup.det C:ℝ)=1)
    (ρ δ : ℂ) (hρ : ρ=1 ∨ ρ= -1) (hδ : δ=1 ∨ δ= -1)
    (hL : g ∣[k] L=ρ • g) (hR : g ∣[k] R=ρ • g)
    (hCp : Cp=L*C⁻¹*R) (r : ℝ)
    (hE : E*translation r=C⁻¹*R*translation (-r))
    (hp : ((g ∣[k] C) ∣[k] translation r)+((g ∣[k] Cp) ∣[k] translation (-r))=
      δ • ((g ∣[k] translation r)+(g ∣[k] translation (-r)))) :
    ((g ∣[k] C)-δ • g) ∣[k] E=(ρ*δ) • ((g ∣[k] C)-δ • g) := by
  let D := (g ∣[k] C)-δ • g
  have hprime : (g ∣[k] Cp)-δ • g=(-ρ*δ) • (D ∣[k] (C⁻¹*R)) := by
    rw [hCp]
    simp only [SlashAction.slash_mul,hL,det_one_smul _ (det_one_inv _ hCdet),
      det_one_smul _ hRdet]
    dsimp only [D]
    simp only [SmallLevelEleven.sub_slash,
      det_one_smul _ (det_one_inv _ hCdet),det_one_smul _ hRdet]
    rw [← SlashAction.slash_mul k C C⁻¹, mul_inv_cancel, SlashAction.slash_one, hR]
    rcases hρ with rfl|rfl <;> rcases hδ with rfl|rfl <;>
      simp <;> abel
  have hh : (D ∣[k] translation r)+(((g ∣[k] Cp)-δ • g) ∣[k] translation (-r))=0 := by
    dsimp only [D]
    simp only [SmallLevelEleven.sub_slash,det_one_smul _ (translation_det _)]
    rw [smul_add] at hp
    linear_combination hp
  rw [hprime,det_one_smul _ (translation_det _),← SlashAction.slash_mul,← hE,
    SlashAction.slash_mul] at hh
  have hx := congrArg (fun F : ℍ → ℂ => F ∣[k] (translation r)⁻¹) hh
  simp only [SlashAction.add_slash,det_one_smul _ (det_one_inv _ (translation_det _)),
    ← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,mul_inv_cancel_right,
    SlashAction.zero_slash] at hx
  have he : D ∣[k] E=(ρ*δ) • D := by
    rcases hρ with rfl|rfl <;> rcases hδ with rfl|rfl <;>
      simp only [mul_neg,mul_one,neg_neg,one_smul,neg_one_smul] at hx ⊢ <;>
      first | linear_combination hx | linear_combination -hx
  exact he

#print axioms double_coset_defect_eigen
end SmallLevelNormalized
