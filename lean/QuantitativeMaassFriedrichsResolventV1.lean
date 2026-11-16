module

public import QuantitativeMaassFriedrichsInclusionV1
public import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
@[expose] public noncomputable section

open Set UniformSpace
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The actual bounded inverse of the shifted Friedrichs realization,
constructed by Riesz duality through the energy inclusion. -/
def friedrichsResolvent (N : ℕ) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  (energyInclusion N).comp (energyInclusion N).adjoint

theorem friedrichsResolvent_inner (N : ℕ) (x y : AutomorphicSpace N) :
    inner ℂ x (friedrichsResolvent N y)=
      inner ℂ ((energyInclusion N).adjoint x) ((energyInclusion N).adjoint y) :=
  ((energyInclusion N).adjoint_inner_left ((energyInclusion N).adjoint y) x).symm

theorem friedrichsResolvent_isSelfAdjoint (N : ℕ) : IsSelfAdjoint (friedrichsResolvent N) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact ((energyInclusion N).adjoint_inner_right ((energyInclusion N).adjoint x) y).symm.trans
    (friedrichsResolvent_inner N x y).symm

theorem friedrichsResolvent_nonnegative (N : ℕ) (x : AutomorphicSpace N) :
    0≤(inner ℂ x (friedrichsResolvent N x)).re := by
  rw [friedrichsResolvent_inner]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem energyInclusion_adjoint_injective (N : ℕ) :
    Function.Injective (energyInclusion N).adjoint := by
  intro x y h
  apply (energyInclusion_denseRange N).eq_of_inner_left (𝕜 := ℂ)
  intro z
  rw [← (energyInclusion N).adjoint_inner_left z x,
    ← (energyInclusion N).adjoint_inner_left z y,h]

theorem friedrichsResolvent_injective (N : ℕ) : Function.Injective (friedrichsResolvent N) :=
  (energyInclusion N).self_comp_adjoint_injective_iff.mpr (energyInclusion_adjoint_injective N)

theorem energyInclusion_adjoint_shifted (N : ℕ) (y : QuotientEnergyDomain N) :
    (energyInclusion N).adjoint (energyDomainValue N y+energyDomainLaplacian N y)=
      (y : QuotientEnergySpace N) := by
  apply ext_inner_left ℂ
  intro x
  exact ((energyInclusion N).adjoint_inner_right x _).trans (energy_inner_coe_right N x y).symm

/-- Exact inverse identity on the original densely defined quotient
Laplacian. This establishes agreement of the eventual extension. -/
theorem friedrichsResolvent_shifted (N : ℕ) (y : quotientLaplacianDomain N) :
    friedrichsResolvent N (y.val+quotientLaplacian N y)=y.val := by
  let z : QuotientEnergyDomain N := y
  have h := congrArg (energyInclusion N) (energyInclusion_adjoint_shifted N z)
  exact h.trans (energyInclusion_coe N z)

theorem friedrichsResolvent_denseRange (N : ℕ) : DenseRange (friedrichsResolvent N) := by
  apply (quotientLaplacian_denseDomain N).mono
  intro x hx
  exact ⟨x+quotientLaplacian N ⟨x,hx⟩,friedrichsResolvent_shifted N ⟨x,hx⟩⟩

theorem friedrichsResolvent_opNorm_le (N : ℕ) : ‖friedrichsResolvent N‖≤1 := by
  have h := (energyInclusion N).opNorm_comp_le (energyInclusion N).adjoint
  rw [LinearIsometryEquiv.norm_map] at h
  have hJ := energyInclusion_opNorm_le N
  change ‖friedrichsResolvent N‖≤‖energyInclusion N‖*‖energyInclusion N‖ at h
  nlinarith [norm_nonneg (energyInclusion N)]

theorem friedrichsResolvent_lower (N : ℕ) (x : AutomorphicSpace N) :
    ‖friedrichsResolvent N x‖^2≤(inner ℂ (friedrichsResolvent N x) x).re := by
  have h := energyInclusion_norm_le N ((energyInclusion N).adjoint x)
  have hi := (energyInclusion N).adjoint_inner_right ((energyInclusion N).adjoint x) x
  have he : (inner ℂ (friedrichsResolvent N x) x).re=
      ‖(energyInclusion N).adjoint x‖^2 := by
    exact (congrArg Complex.re hi.symm).trans (inner_self_eq_norm_sq (𝕜 := ℂ) _)
  rw [he]
  change ‖friedrichsResolvent N x‖≤‖(energyInclusion N).adjoint x‖ at h
  nlinarith [norm_nonneg (friedrichsResolvent N x),norm_nonneg ((energyInclusion N).adjoint x)]

#print axioms friedrichsResolvent_injective
#print axioms friedrichsResolvent_shifted
#print axioms friedrichsResolvent_denseRange

end QuantitativeMaass
