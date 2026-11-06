module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter ConjAct
open scoped MatrixGroups ModularForm Pointwise

variable (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne] (k : ℤ)

def cuspBoundaryGroup (γ : SL(2,ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  toConjAct (SpecialLinearGroup.mapGL ℝ γ)⁻¹ • Γ

instance cuspBoundaryGroup_arithmetic (γ : SL(2,ℤ)) :
    (cuspBoundaryGroup Γ γ).IsArithmetic := by
  change (toConjAct (SpecialLinearGroup.mapGL ℝ γ)⁻¹ • Γ).IsArithmetic
  have he : (SpecialLinearGroup.mapGL ℝ γ)⁻¹ =
      (SpecialLinearGroup.mapGL ℚ γ⁻¹).map (Rat.castHom ℝ) := by
    rw [← map_inv]
    apply Units.ext
    ext i j
    simp [SpecialLinearGroup.mapGL, SpecialLinearGroup.map, GeneralLinearGroup.map]
  rw [he]
  exact Subgroup.IsArithmetic.conj Γ _

instance cuspBoundaryGroup_det (γ : SL(2,ℤ)) : (cuspBoundaryGroup Γ γ).HasDetOne :=
  inferInstanceAs (toConjAct (SpecialLinearGroup.mapGL ℝ γ)⁻¹ • Γ).HasDetOne

omit [Γ.HasDetOne] in
/-- The actual cusp constant exists; no Fourier growth or Eisenstein
classification hypothesis is imposed. -/
theorem cuspBoundary_tendsto (F : ModularForm Γ k) (γ : SL(2,ℤ)) :
    Tendsto ((F : ℍ → ℂ) ∣[k] γ) atImInfty
      (nhds (valueAtInfty ((F : ℍ → ℂ) ∣[k] γ))) := by
  let G : ModularForm (cuspBoundaryGroup Γ γ) k :=
    ModularForm.translate F (SpecialLinearGroup.mapGL ℝ γ)
  have hh : 0 < (cuspBoundaryGroup Γ γ).strictWidthInfty :=
    (cuspBoundaryGroup Γ γ).strictWidthInfty_pos_iff.mpr (inferInstance : Fact
      (IsCusp OnePoint.infty (cuspBoundaryGroup Γ γ))).out
  have ht := ModularFormClass.tendsto_atImInfty G hh
    (cuspBoundaryGroup Γ γ).strictWidthInfty_mem_strictPeriods
  apply tendsto_nhds_limUnder
  refine ⟨(qExpansion (cuspBoundaryGroup Γ γ).strictWidthInfty G).coeff 0, ?_⟩
  change Tendsto ((F : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ γ) _ _ at ht
  change Tendsto ((F : ℍ → ℂ) ∣[k]
    SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) γ)) _ _ at ht
  simpa only [ModularForm.SL_slash] using ht

/-- Constant terms at all rational cusp representatives, as a genuine
linear map on the full modular-form space. -/
def cuspBoundary : ModularForm Γ k →ₗ[ℂ] (SL(2,ℤ) → ℂ) where
  toFun F γ := valueAtInfty ((F : ℍ → ℂ) ∣[k] γ)
  map_add' F G := by
    funext γ
    apply tendsto_nhds_unique (cuspBoundary_tendsto Γ k (F+G) γ)
    simp only [FunLike.coe_add,SlashAction.add_slash]
    change Tendsto (fun z ↦ ((F : ℍ → ℂ) ∣[k] γ) z + ((G : ℍ → ℂ) ∣[k] γ) z) _ _
    exact (cuspBoundary_tendsto Γ k F γ).add (cuspBoundary_tendsto Γ k G γ)
  map_smul' c F := by
    funext γ
    apply tendsto_nhds_unique (cuspBoundary_tendsto Γ k (c • F) γ)
    simp only [FunLike.coe_smul,ModularForm.SL_smul_slash]
    change Tendsto (fun z ↦ c * ((F : ℍ → ℂ) ∣[k] γ) z) _ _
    exact (cuspBoundary_tendsto Γ k F γ).const_mul c

@[simp] theorem cuspBoundary_apply (F : ModularForm Γ k) (γ : SL(2,ℤ)) :
    cuspBoundary Γ k F γ = valueAtInfty ((F : ℍ → ℂ) ∣[k] γ) := rfl

/-- The kernel is exactly the genuine Mathlib cusp-form subspace, for
any arithmetic determinant-one group and any integer weight. -/
theorem cuspBoundary_ker :
    LinearMap.ker (cuspBoundary Γ k) = ModularForm.cuspFormSubmodule Γ k := by
  ext F
  constructor
  · intro hF
    apply (ModularForm.isCuspForm_iff F).mpr
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := by
      simpa only [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] using hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hcSL]
    intro γ _
    have hz : cuspBoundary Γ k F γ = 0 := congrFun hF γ
    change Tendsto ((F : ℍ → ℂ) ∣[k] γ) atImInfty (nhds 0)
    have ht := cuspBoundary_tendsto Γ k F γ
    change Tendsto ((F : ℍ → ℂ) ∣[k] γ) atImInfty (nhds (cuspBoundary Γ k F γ)) at ht
    rwa [hz] at ht
  · rintro ⟨G,hG⟩
    apply funext
    intro γ
    have hg := (CuspFormClass.zero_at_infty_slash G γ).valueAtInfty_eq_zero
    change valueAtInfty ((F : ℍ → ℂ) ∣[k] γ) = 0
    have he : (G : ℍ → ℂ) = (F : ℍ → ℂ) :=
      congrArg (fun H : ModularForm Γ k ↦ (H : ℍ → ℂ)) hG
    simpa only [he] using hg

#print axioms cuspBoundary_tendsto
#print axioms cuspBoundary
#print axioms cuspBoundary_ker

end QuantitativeArithmeticSmallLevelEisenstein
