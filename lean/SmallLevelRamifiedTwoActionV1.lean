module

public import SmallLevelRamifiedTwoFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelRamifiedTwo

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem Q_smul (N a : ℕ) (ha : 2*a=N+2) (F : ℍ → ℂ) (k : ℤ) (c : ℂ) :
    (c • F) ∣[k] Q N a ha=c • (F ∣[k] Q N a ha) := by
  rw [ModularForm.smul_slash]
  have hs : σ (Q N a ha)=ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [σ, Q_det]; norm_num
  rw [hs, ContinuousAlgEquiv.refl_apply]

theorem eigen_square (N a : ℕ) (ha : 2*a=N+2) (F : ℍ → ℂ) (k : ℤ) (δ : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hQ : F ∣[k] Q N a ha=δ • F) :
    F ∣[k] (Q N a ha*Q N a ha)=F := by
  rw [SlashAction.slash_mul, hQ, Q_smul, hQ, smul_smul]
  rcases hδ with rfl | rfl <;> simp

theorem invariant_conjugate (N a : ℕ) (ha : 2*a=N+2) (F : ℍ → ℂ) (k : ℤ) (δ : ℂ)
    (hQ : F ∣[k] Q N a ha=δ • F) (γ κ : SL(2,ℤ))
    (hκ : SpecialLinearGroup.mapGL ℝ κ*Q N a ha=Q N a ha*SpecialLinearGroup.mapGL ℝ γ)
    (hγ : F ∣[k] γ=F) : F ∣[k] κ=F := by
  have hh : (F ∣[k] κ) ∣[k] Q N a ha=F ∣[k] Q N a ha := by
    change (F ∣[k] SpecialLinearGroup.mapGL ℝ κ) ∣[k] Q N a ha=F ∣[k] Q N a ha
    rw [← SlashAction.slash_mul, hκ, SlashAction.slash_mul]
    change (F ∣[k] Q N a ha) ∣[k] γ=F ∣[k] Q N a ha
    rw [hQ, ModularForm.SL_smul_slash, hγ]
  have h := congrArg (fun g : ℍ → ℂ => g ∣[k] (Q N a ha)⁻¹) hh
  simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h

#print axioms eigen_square
#print axioms invariant_conjugate

end SmallLevelRamifiedTwo
