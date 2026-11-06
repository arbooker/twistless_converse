module

public import SmallLevelThirtySixGammaZeroV1
public import Mathlib.NumberTheory.ModularForms.QExpansion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane ModularGroup Matrix
open scoped ModularForm MatrixGroups

/-- An explicit cusp width valid for every Gamma0(36) cusp. -/
theorem conjugate_T_mem (γ : SL(2,ℤ)) :
    γ*(T^(36:ℤ))*γ⁻¹ ∈ CongruenceSubgroup.Gamma0 36 := by
  let r : SL(2,ℤ) →* SL(2,ZMod 36) := SpecialLinearGroup.map (Int.castRingHom (ZMod 36))
  have ht : r (T^(36:ℤ))=1 := by decide
  have he : r (γ*(T^(36:ℤ))*γ⁻¹)=1 := by rw [map_mul, map_mul, map_inv, ht]; group
  have hh := congrArg (fun A : SL(2,ZMod 36) => A 1 0) he
  exact CongruenceSubgroup.Gamma0_mem.mpr hh

theorem gamma_zero_cusp_period (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ : SL(2,ℤ), γ∈CongruenceSubgroup.Gamma0 36 → f ∣[k] γ=f)
    (γ : SL(2,ℤ)) :
    Function.Periodic ((f ∣[k] γ) ∘ ofComplex) (36:ℂ) := by
  have he := congrArg (fun F : ℍ → ℂ => F ∣[k] γ) (hf _ (conjugate_T_mem γ))
  have hh : (f ∣[k] γ) ∣[k] (T^(36:ℤ))=f ∣[k] γ := by
    simpa only [← SlashAction.slash_mul, mul_assoc, inv_mul_cancel, mul_one] using he
  apply UpperHalfPlane.periodic_comp_ofComplex (h:=36)
  intro z
  have hz := congrFun hh z
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul] at hz
  have hd : denom (T^(36:ℤ) : SL(2,ℤ)) z=1 := by
    rw [ModularGroup.denom_apply]
    rw [ModularGroup.coe_T_zpow]
    norm_num
  simpa only [hd, one_zpow, mul_one, Int.cast_ofNat] using hz

#print axioms conjugate_T_mem
#print axioms gamma_zero_cusp_period

end SmallLevelThirtySix
