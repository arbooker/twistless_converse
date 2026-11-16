module

public import QuantitativeMaassLocalRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass

def localRestrictionMap (K L : Set ℍ) (hKL : K⊆L) :
    Lp ℂ 2 (volume.restrict L) →L[ℝ] Lp ℂ 2 (volume.restrict K) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_mono_set volume hKL)

theorem localRestrictionMap_ae (K L : Set ℍ) (hKL : K⊆L)
    (f : Lp ℂ 2 (volume.restrict L)) :
    (localRestrictionMap K L hKL f : ℍ → ℂ)=ᵐ[volume.restrict K] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- The constructed compact restrictions agree on nested sets. Thus they
describe a coherent local L2 function, rather than unrelated extensions. -/
theorem quotientRestriction_coherence (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L) (hKm : MeasurableSet K) (hLm : MeasurableSet L)
    (hKL : K⊆L) (f : AutomorphicSpace N) :
    localRestrictionMap K L hKL (quotientRestriction N L hL hLm f)=
      quotientRestriction N K hK hKm f := by
  have he : (fun f : AutomorphicSpace N =>
      localRestrictionMap K L hKL (quotientRestriction N L hL hLm f))=
      fun f => quotientRestriction N K hK hKm f := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (by fun_prop) (by fun_prop)
    funext g
    dsimp only [Function.comp_apply]
    apply Lp.ext
    have hlarge := quotientRestriction_representative_ae N L hL hLm g
    have hac : volume.restrict K ≪ volume.restrict L :=
      (Measure.restrict_mono_set volume hKL).absolutelyContinuous
    have hlarge' := hac.ae_eq hlarge
    filter_upwards [localRestrictionMap_ae K L hKL
      (quotientRestriction N L hL hLm (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) g)),
      hlarge',quotientRestriction_representative_ae N K hK hKm g] with Z hr hLZ hKZ
    exact (hr.trans hLZ).trans hKZ.symm
  exact congrFun he f

theorem quotientRestriction_coherence_ae (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L) (hKm : MeasurableSet K) (hLm : MeasurableSet L)
    (hKL : K⊆L) (f : AutomorphicSpace N) :
    (quotientRestriction N K hK hKm f : ℍ → ℂ)=ᵐ[volume.restrict K]
      quotientRestriction N L hL hLm f := by
  rw [← quotientRestriction_coherence N K L hK hL hKm hLm hKL f]
  exact localRestrictionMap_ae K L hKL _

#print axioms quotientRestriction_coherence_ae

end QuantitativeMaass
