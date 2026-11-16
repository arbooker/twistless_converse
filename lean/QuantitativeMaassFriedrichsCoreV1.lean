module

public import QuantitativeMaassFriedrichsFormV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set UniformSpace
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The energy norm is controlled by the actual differential graph norm. -/
theorem quotientEnergy_norm_le_graph (N : ℕ) (x : QuotientEnergyDomain N) :
    ‖x‖≤2*‖(energyDomainValue N x,energyDomainLaplacian N x)‖ := by
  have h := quotientEnergy_norm_sq N x
  have hi := re_inner_le_norm (𝕜 := ℂ) (energyDomainValue N x) (energyDomainLaplacian N x)
  have hf := norm_fst_le (energyDomainValue N x,energyDomainLaplacian N x)
  have hs := norm_snd_le (energyDomainValue N x,energyDomainLaplacian N x)
  have hp : ‖energyDomainValue N x‖*‖energyDomainLaplacian N x‖≤
      ‖(energyDomainValue N x,energyDomainLaplacian N x)‖^2 := by
    nlinarith [norm_nonneg (energyDomainValue N x),norm_nonneg (energyDomainLaplacian N x)]
  change (inner ℂ (energyDomainValue N x) (energyDomainLaplacian N x)).re≤_ at hi
  nlinarith [norm_nonneg x,norm_nonneg (energyDomainValue N x),
    norm_nonneg (energyDomainValue N x,energyDomainLaplacian N x)]

def poincareEnergySeed (N : ℕ) (u : SmoothUpperSeed) : QuotientEnergyDomain N :=
  (⟨poincareSeedVector N u,poincareSeedVector_mem_quotientLaplacianDomain N u⟩ :
    quotientLaplacianDomain N)

theorem poincareEnergySeed_value (N : ℕ) (u : SmoothUpperSeed) :
    energyDomainValue N (poincareEnergySeed N u)=poincareSeedVector N u := rfl

theorem poincareEnergySeed_laplacian (N : ℕ) (u : SmoothUpperSeed) :
    energyDomainLaplacian N (poincareEnergySeed N u)=poincareSeedVector N u.laplacian :=
  quotientLaplacian_poincareSeed N u

/-- Smooth Poincaré seeds are dense for the stronger energy norm. This is
proved from the defining differential graph closure and the graph-to-energy
norm estimate, rather than inferred from ordinary Hilbert density. -/
theorem poincareEnergySeed_dense (N : ℕ) : DenseRange (poincareEnergySeed N) := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  have hx := quotientLaplacian_graph N (x : quotientLaplacianDomain N)
  change (energyDomainValue N x,energyDomainLaplacian N x)∈
    closure (poincareLinearGraph N : Set (AutomorphicSpace N × AutomorphicSpace N)) at hx
  obtain ⟨p,hp,hd⟩ := Metric.mem_closure_iff.mp hx (ε/2) (by positivity)
  obtain ⟨u,hu,hdu⟩ := (poincareLinearGraph_mem_iff N p).mp hp
  refine ⟨u,?_⟩
  rw [dist_eq_norm] at hd ⊢
  have hn := quotientEnergy_norm_le_graph N (x-poincareEnergySeed N u)
  have hv : energyDomainValue N (x-poincareEnergySeed N u)=energyDomainValue N x-p.1 := by
    change energyDomainValue N x-poincareSeedVector N u=energyDomainValue N x-p.1
    rw [hu]
  have hl : energyDomainLaplacian N (x-poincareEnergySeed N u)=
      energyDomainLaplacian N x-p.2 := by
    change quotientLaplacian N ((x : quotientLaplacianDomain N)-
      (poincareEnergySeed N u : quotientLaplacianDomain N))=_
    exact ((quotientLaplacian N).map_sub (x : quotientLaplacianDomain N)
      (poincareEnergySeed N u : quotientLaplacianDomain N)).trans
      (congrArg (energyDomainLaplacian N x-·)
        ((poincareEnergySeed_laplacian N u).trans hdu.symm))
  rw [hv,hl] at hn
  change ‖x-poincareEnergySeed N u‖≤
    2*‖(energyDomainValue N x,energyDomainLaplacian N x)-p‖ at hn
  linarith

/-- The smooth compact Poincaré differential domain is a core for the
completed energy form. This asserts form density, not essential
self-adjointness or equality of operator graph domains. -/
theorem poincareEnergySeed_completion_dense (N : ℕ) :
    DenseRange (fun u : SmoothUpperSeed =>
      (poincareEnergySeed N u : QuotientEnergySpace N)) :=
  Completion.denseRange_coe.comp (poincareEnergySeed_dense N) (Completion.continuous_coe _)

#print axioms poincareEnergySeed_dense
#print axioms poincareEnergySeed_completion_dense

end QuantitativeMaass
