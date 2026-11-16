module

public import QuantitativeMaassFriedrichsOperatorV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set UniformSpace
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The closed energy form, with its domain represented by the injectively
embedded energy completion. The ambient inner product is removed from the
completion inner product to leave the actual Dirichlet energy. -/
def quotientClosedEnergy (N : ℕ) (u v : QuotientEnergySpace N) : ℂ :=
  inner ℂ u v-inner ℂ (energyInclusion N u) (energyInclusion N v)

theorem quotientClosedEnergy_nonnegative (N : ℕ) (u : QuotientEnergySpace N) :
    0≤(quotientClosedEnergy N u u).re := by
  have h := energyInclusion_norm_le N u
  have hu : (inner ℂ u u).re=‖u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have hJ : (inner ℂ (energyInclusion N u) (energyInclusion N u)).re=
      ‖energyInclusion N u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  simp only [quotientClosedEnergy,Complex.sub_re,hu,hJ]
  nlinarith [norm_nonneg u,norm_nonneg (energyInclusion N u)]

/-- The form norm is exactly the complete Hilbert norm already constructed;
closedness is not assumed. -/
theorem quotientClosedEnergy_norm (N : ℕ) (u : QuotientEnergySpace N) :
    ‖energyInclusion N u‖^2+(quotientClosedEnergy N u u).re=‖u‖^2 := by
  have hu : (inner ℂ u u).re=‖u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have hJ : (inner ℂ (energyInclusion N u) (energyInclusion N u)).re=
      ‖energyInclusion N u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  simp only [quotientClosedEnergy,Complex.sub_re,hu,hJ]
  ring

theorem quotientClosedEnergy_coe (N : ℕ) (u v : QuotientEnergyDomain N) :
    quotientClosedEnergy N (u : QuotientEnergySpace N) (v : QuotientEnergySpace N)=
      inner ℂ (energyDomainValue N u) (energyDomainLaplacian N v) := by
  simp only [quotientClosedEnergy,Completion.inner_coe,energyInclusion_coe,quotientEnergy_inner]
  ring

/-- Exact representation of the constructed operator by the completed energy
form. This is the Friedrichs variational identity on its full form domain. -/
theorem friedrichsGraph_iff_form (N : ℕ) (x y : AutomorphicSpace N) :
    FriedrichsGraph N x y ↔ ∃ u : QuotientEnergySpace N,
      energyInclusion N u=x ∧ ∀ v : QuotientEnergySpace N,
        quotientClosedEnergy N v u=inner ℂ (energyInclusion N v) y := by
  constructor
  · intro h
    refine ⟨(energyInclusion N).adjoint (x+y),h,?_⟩
    intro v
    change inner ℂ v ((energyInclusion N).adjoint (x+y))-
      inner ℂ (energyInclusion N v) (friedrichsResolvent N (x+y))=_
    rw [(energyInclusion N).adjoint_inner_right,h,inner_add_right]
    ring
  · rintro ⟨u,hu,hq⟩
    have he : u=(energyInclusion N).adjoint (x+y) := by
      apply ext_inner_left ℂ
      intro v
      have hv := hq v
      simp only [quotientClosedEnergy,hu] at hv
      rw [(energyInclusion N).adjoint_inner_right,inner_add_right]
      linear_combination hv
    change energyInclusion N ((energyInclusion N).adjoint (x+y))=x
    rw [← he,hu]

/-- The original closed differential domain is dense in the constructed
form domain in its actual form norm. This does not assert that it is an
operator graph core for the Friedrichs extension. -/
theorem quotientClosedEnergy_domain_dense (N : ℕ) :
    DenseRange (fun u : QuotientEnergyDomain N => (u : QuotientEnergySpace N)) :=
  Completion.denseRange_coe

#print axioms quotientClosedEnergy_nonnegative
#print axioms quotientClosedEnergy_coe
#print axioms friedrichsGraph_iff_form

end QuantitativeMaass
