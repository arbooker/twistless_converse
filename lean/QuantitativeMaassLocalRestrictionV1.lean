module

public import QuantitativeMaassQuotientRestrictionBoundV1
public import QuantitativeMaassPoincareGraphV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass

theorem representativeLocalMemLp (N : ℕ) (K : Set ℍ) (hK : IsCompact K) (hKm : MeasurableSet K)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    MemLp f.val 2 (volume.restrict K) :=
  invariant_memLp_restrict_compact volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    f.val f.property.1 f.property.2.1 f.property.2.2 K hK hKm

/-- Literal restriction of invariant representatives to a compact set,
before passage to the completed quotient space. -/
def representativeRestriction (N : ℕ) (K : Set ℍ) (hK : IsCompact K) (hKm : MeasurableSet K) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) →ₗ[ℂ]
      Lp ℂ 2 (volume.restrict K) where
  toFun f := (representativeLocalMemLp N K hK hKm f).toLp f.val
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Eventually.of_forall (fun _ => rfl)
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Eventually.of_forall (fun _ => rfl)

theorem representativeRestriction_bound (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (hKm : MeasurableSet K) :
    ∃ C : ℝ, ∀ f, ‖representativeRestriction N K hK hKm f‖≤
      C*‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖ := by
  obtain ⟨C,_,hC⟩ := quotient_restriction_norm_bound volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) K hK hKm
  exact ⟨C,fun f => hC f.val f.property.1 f.property.2.1 f.property.2.2⟩

/-- The actual bounded local restriction operator on the entire quotient
Hilbert completion. Its bound comes from compact orbit multiplicity. -/
def quotientRestriction (N : ℕ) (K : Set ℍ) (hK : IsCompact K) (hKm : MeasurableSet K) :
    AutomorphicSpace N →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
  (representativeRestriction N K hK hKm).extendOfNorm
    (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))

theorem quotientRestriction_representative (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    quotientRestriction N K hK hKm
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)=
        (representativeLocalMemLp N K hK hKm f).toLp f.val :=
  LinearMap.extendOfNorm_eq (f := representativeRestriction N K hK hKm)
    (e := AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
    (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N))
    (representativeRestriction_bound N K hK hKm) f

theorem quotientRestriction_representative_ae (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    (quotientRestriction N K hK hKm
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) : ℍ → ℂ)=ᵐ[volume.restrict K] f.val := by
  rw [quotientRestriction_representative]
  exact MemLp.coeFn_toLp _

#print axioms quotientRestriction
#print axioms quotientRestriction_representative_ae

end QuantitativeMaass
