module

public import AsymptoticModularBoundaryV1
public import AsymptoticCongruenceFiniteCoverV1
public import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticModularDomain

open Matrix UpperHalfPlane MeasureTheory Filter Set
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped MatrixGroups Modular Pointwise

theorem ae_closed_mem_open : ∀ᵐ z : ℍ ∂volume,z∈𝒟 → z∈𝒟ᵒ := by
  rw [ae_iff]
  simp only [not_imp]
  change (volume : Measure ℍ) (𝒟 \ 𝒟ᵒ)=0
  exact boundary_null

theorem gamma_one_orbit_meets (z : ℍ) : ∃ g : gamma 1,g.val • z∈𝒟 := by
  obtain ⟨A,hA⟩ := ModularGroup.exists_smul_mem_fd z
  have hm : A∈CongruenceSubgroup.Gamma0 1 := by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact Subsingleton.elim _ _
  refine ⟨⟨integralLabel A,⟨A,hm,rfl⟩⟩,?_⟩
  simpa only [integralLabel_action] using hA

set_option backward.isDefEq.respectTransparency false in
/-- The standard modular domain is a measurable fundamental domain
for the projective integral group, where the scalar signs occur once. -/
theorem gamma_one_fundamental : IsFundamentalDomain (gamma 1) 𝒟 (volume : Measure ℍ) := by
  apply IsFundamentalDomain.mk'' ModularGroup.isClosed_fd.measurableSet.nullMeasurableSet
    (Eventually.of_forall gamma_one_orbit_meets)
  · intro g hg
    have hno : ∀ᵐ z : ℍ ∂volume,z∉g • 𝒟∩𝒟 := by
      filter_upwards [ae_closed_mem_open,
        (AsymptoticRationalGroup.measurePreserving g.val⁻¹).quasiMeasurePreserving.ae
          ae_closed_mem_open,AsymptoticRationalGroup.ae_free] with z hz hi hf
      intro h
      have hzi : g.val⁻¹ • z∈𝒟 := by
        have hh := mem_smul_set_iff_inv_smul_mem.mp h.1
        change g⁻¹ • z∈𝒟
        exact hh
      have ho := hz h.2
      have hoi := hi hzi
      have hrep : representative g⁻¹ • z=g.val⁻¹ • z := by
        rw [← integralLabel_action,representative_label]
        rfl
      have he : z=g.val⁻¹ • z := by
        rw [← hrep]
        exact ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo ho (hrep.symm ▸ hoi)
      have he' := hf g.val⁻¹ he.symm
      apply hg
      apply Subtype.ext
      exact inv_eq_one.mp he'
    rw [ae_iff] at hno
    change (volume : Measure ℍ) (g • 𝒟∩𝒟)=0
    simpa only [not_not,Set.ofPred_mem_eq] using hno
  · intro g
    exact (AsymptoticRationalGroup.measurePreserving g.val).quasiMeasurePreserving

#print axioms ae_closed_mem_open
#print axioms gamma_one_orbit_meets
#print axioms gamma_one_fundamental

end AsymptoticModularDomain
