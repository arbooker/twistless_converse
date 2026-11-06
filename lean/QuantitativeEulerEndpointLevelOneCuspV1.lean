module

public import QuantitativeEulerEndpointLevelOneModularityV1
public import FinitenessOriginalDiskIndependenceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointLevelOne
open UpperHalfPlane ModularGroup Filter
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped ModularForm MatrixGroups Manifold Topology

theorem solutionFunction_holomorphic (m : ℕ) (f : ℕ → ℂ) (hf : IsSolution 1 (2*m) f) :
    MDiff (solutionFunction m f) := by
  obtain ⟨τ,_hτ,hg⟩ := hf.growth
  intro z
  exact (FinitenessFourierConstruction.holomorphic (polynomial_bound hf.zero hg (2*m)) z.im_pos).mdifferentiableAt.comp z
    (mdifferentiable_coe z)

theorem solutionFunction_zeroAtInfty (m : ℕ) (f : ℕ → ℂ) (hf : IsSolution 1 (2*m) f) :
    IsZeroAtImInfty (solutionFunction m f) := by
  obtain ⟨τ,_hτ,hg⟩ := hf.growth
  have ha := polynomial_bound hf.zero hg (2*m)
  have hs := (FinitenessPolynomialSeries.has_series ha).differentiableAt.continuousAt
  have hq := ((Function.Periodic.qParam_tendsto (by norm_num : (0:ℝ)<1)).mono_right nhdsWithin_le_nhds).comp
    tendsto_coe_atImInfty
  have hh := hs.tendsto.comp hq
  rw [FinitenessPolynomialSeries.zero (fullCoefficients_zero hf.zero (2*m))] at hh
  exact hh

def solutionCusp (m : ℕ) (f : FinitenessOriginalInput.S 1 (2*m)) : CuspForm 𝒮ℒ ((2*m : ℕ) : ℤ) where
  toFun := solutionFunction m f.val
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,rfl⟩ := hg
    exact solutionFunction_modular m f.val f.property γ
  holo' := solutionFunction_holomorphic m f.val f.property
  zero_at_cusps' hc := by
    apply (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr
    intro γ _hγ
    rw [solutionFunction_modular m f.val f.property γ]
    exact solutionFunction_zeroAtInfty m f.val f.property

#print axioms solutionCusp
end QuantitativeEulerEndpointLevelOne
