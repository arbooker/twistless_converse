module

public import QuantitativeMaassEulerLevelOneModularV1
public import QuantitativeMaassEulerWeightedL2V1
public import QuantitativeMaassHeckeL2V1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups

namespace QuantitativeMaass

variable {b : ℕ → ℂ} (r : ℝ) (σ : ℕ)
  (hb : MaassOriginal.IsEulerSolution 1 (.principal r) σ b)

include hb

theorem principalEulerPhysical_level_one_invariant (g : SL(2,ℤ)) (z : ℍ) :
    principalEulerPhysical b r σ ((g•z:ℍ):ℂ)=principalEulerPhysical b r σ z := by
  simpa only [ModularForm.SL_slash_apply,neg_zero,zpow_zero,mul_one] using
    congrFun (principalEulerPhysical_level_one_modular r σ hb g) z

/-- Modular reduction turns the proved positive-height tail bound into a
global bound at level one. No boundedness hypothesis is added. -/
theorem principalEulerPhysical_level_one_bounded :
    ∃ C : ℝ,0≤C ∧ ∀ z : ℍ,‖principalEulerPhysical b r σ z‖≤C := by
  obtain ⟨C,hC,hbound⟩ := principalEulerWave_height_bound hb.polynomialGrowth r σ 0 (1/2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro z
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hy : (1:ℝ)/2≤(g•z).im := by
    nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg,(g•z).im_pos]
  have hh := hbound (g•z).re (g•z).im hy
  simp only [pow_zero,one_mul] at hh
  change ‖principalEulerPhysical b r σ ((g•z:ℍ):ℂ)‖≤C at hh
  rwa [principalEulerPhysical_level_one_invariant r σ hb g z] at hh

theorem principalEulerPhysical_level_one_memLp :
    MemLp (fun z : ℍ => principalEulerPhysical b r σ z) 2 (quotientMeasure 1) := by
  obtain ⟨C,_,hC⟩ := principalEulerPhysical_level_one_bounded r σ hb
  exact MemLp.of_bound (principalEulerPhysical_continuous_upper hb.polynomialGrowth r σ).aestronglyMeasurable
    C (Eventually.of_forall hC)

def principalEulerLevelOneRepresentative : AutomorphicL2.representatives (gamma 1) (quotientMeasure 1) := by
  refine ⟨fun z : ℍ => principalEulerPhysical b r σ z,
    (principalEulerPhysical_continuous_upper hb.polynomialGrowth r σ).measurable,?_,
    principalEulerPhysical_level_one_memLp r σ hb⟩
  intro g z
  have he : representative g • z=g.val•z := by
    rw [←integralLabel_action,representative_label]
  rw [←he]
  exact principalEulerPhysical_level_one_invariant r σ hb (representative g) z

/-- Genuine level-one quotient L2 class, built from the original solution. -/
def principalEulerLevelOneClass : AutomorphicSpace 1 :=
  AutomorphicL2.denseEmbedding (gamma 1) (quotientMeasure 1) (principalEulerLevelOneRepresentative r σ hb)

theorem principalEulerLevelOneClass_coeFn :
    (principalEulerLevelOneClass r σ hb).val=ᵐ[quotientMeasure 1]
      (fun z : ℍ => principalEulerPhysical b r σ z) :=
  (principalEulerPhysical_level_one_memLp r σ hb).coeFn_toLp

#print axioms principalEulerPhysical_level_one_invariant
#print axioms principalEulerPhysical_level_one_bounded
#print axioms principalEulerPhysical_level_one_memLp
#print axioms principalEulerLevelOneRepresentative
#print axioms principalEulerLevelOneClass
#print axioms principalEulerLevelOneClass_coeFn

end QuantitativeMaass
