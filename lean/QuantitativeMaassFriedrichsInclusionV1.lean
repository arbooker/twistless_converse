module

public import QuantitativeMaassFriedrichsEnergyV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set UniformSpace
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

def energyDomainInclusion (N : ℕ) : QuotientEnergyDomain N →ₗ[ℂ] AutomorphicSpace N where
  toFun := energyDomainValue N
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The bounded extension of the literal inclusion to the constructed
energy Hilbert completion. -/
def energyInclusion (N : ℕ) : QuotientEnergySpace N →L[ℂ] AutomorphicSpace N :=
  (energyDomainInclusion N).extendOfNorm (Completion.toComplₗᵢ.toLinearMap)

theorem energyInclusion_coe (N : ℕ) (x : QuotientEnergyDomain N) :
    energyInclusion N (x : QuotientEnergySpace N)=energyDomainValue N x := by
  apply LinearMap.extendOfNorm_eq Completion.denseRange_coe
  refine ⟨1,fun y => ?_⟩
  change ‖energyDomainValue N y‖≤1*‖(y : QuotientEnergySpace N)‖
  simpa only [one_mul,Completion.norm_coe] using energyDomainValue_norm_le N y

theorem energyInclusion_norm_le (N : ℕ) (x : QuotientEnergySpace N) :
    ‖energyInclusion N x‖≤‖x‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := energyDomainInclusion N) (e := Completion.toComplₗᵢ.toLinearMap)
    Completion.denseRange_coe 1 (fun y => by
      change ‖energyDomainValue N y‖≤1*‖(y : QuotientEnergySpace N)‖
      simpa only [one_mul,Completion.norm_coe] using energyDomainValue_norm_le N y) x
  simpa only [energyInclusion,one_mul] using h

theorem energyInclusion_opNorm_le (N : ℕ) : ‖energyInclusion N‖≤1 :=
  (energyInclusion N).opNorm_le_bound (by norm_num)
    (fun x => by simpa only [one_mul] using energyInclusion_norm_le N x)

theorem energyInclusion_denseRange (N : ℕ) : DenseRange (energyInclusion N) := by
  apply (quotientLaplacian_denseDomain N).mono
  intro x hx
  let y : QuotientEnergyDomain N := (⟨x,hx⟩ : quotientLaplacianDomain N)
  refine ⟨(y : QuotientEnergySpace N),?_⟩
  rw [energyInclusion_coe]
  rfl

/-- Testing the completed energy product against the actual operator
domain gives the exact shifted-operator pairing. -/
theorem energy_inner_coe_right (N : ℕ) (x : QuotientEnergySpace N)
    (y : QuotientEnergyDomain N) :
    inner ℂ x (y : QuotientEnergySpace N)=
      inner ℂ (energyInclusion N x) (energyDomainValue N y+energyDomainLaplacian N y) := by
  refine Completion.induction_on (p := fun z : QuotientEnergySpace N =>
    inner ℂ z (y : QuotientEnergySpace N)=
      inner ℂ (energyInclusion N z) (energyDomainValue N y+energyDomainLaplacian N y)) x ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const)
      ((energyInclusion N).continuous.inner continuous_const)
  · intro z
    rw [Completion.inner_coe,energyInclusion_coe,quotientEnergy_inner,inner_add_right]

/-- Closability of the energy embedding is proved, not assumed: a
completed vector mapping to zero pairs to zero with a dense family. -/
theorem energyInclusion_injective (N : ℕ) : Function.Injective (energyInclusion N) := by
  intro x y h
  apply (Completion.denseRange_coe (α := QuotientEnergyDomain N)).eq_of_inner_left (𝕜 := ℂ)
  intro z
  rw [energy_inner_coe_right,energy_inner_coe_right,h]

#print axioms energyInclusion
#print axioms energyInclusion_injective
#print axioms energyInclusion_denseRange

end QuantitativeMaass
