module

public import QuantitativeNewGapSectorIncidenceV1
public import QuantitativeNewGapSectorGapV1
public import QuantitativeNewGapIndexedV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared

open QuantitativeNewGap
open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticSectorSigns
open AsymptoticPolarIsometry QuantitativeArithmeticCrossPrime UpperHalfPlane
open scoped lp

def sectorInduction (N : ℕ) (hN : 0<N) (e : Sector N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    countingSectorSpace N hN e →ₗᵢ[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (AsymptoticCongruenceQuotient.induction N hε ht z).comp (countingSectorSpace N hN e).subtypeₗᵢ

/-- The finite exact new/sign corner realizes the original incidence
space, not merely a containing model. -/
theorem sectorInduction_range (N : ℕ) (hN : 0<N) (e : Sector N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    (sectorInduction N hN e hε ht z).toLinearMap.range=
      AsymptoticQuotientIncidence.space N hN hε ht e z := by
  ext v
  constructor
  · rintro ⟨f,rfl⟩
    exact countingSector_induction_mem_incidence N hN e hε ht z f.val f.property
  · intro hv
    have hq := ((AsymptoticQuotientIncidence.space_mem N hN hε ht e z v).mp hv).1
    obtain ⟨f,rfl⟩ := hq
    exact ⟨⟨f,incidence_induction_mem_countingSector N hN e hε ht z f hv⟩,rfl⟩

theorem incidence_projection_compression (N : ℕ) (hN : 0<N) (e : Sector N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    (AsymptoticQuotientIncidence.space N hN hε ht e z).starProjection=
      AsymptoticCongruenceQuotient.compression N hε ht (countingSectorSpace N hN e).starProjection z := by
  have hh := AsymptoticIsometryRange.cogram_comp
    (AsymptoticCongruenceQuotient.induction N hε ht z) (countingSectorSpace N hN e).subtypeₗᵢ
  have hr : (countingSectorSpace N hN e).subtypeₗᵢ.toLinearMap.range=countingSectorSpace N hN e :=
    Submodule.range_subtype _
  rw [starProjection_congr _ _ hr] at hh
  have hs := sectorInduction_range N hN e hε ht z
  change (sectorInduction N hN e hε ht z).toLinearMap.range.starProjection=_ at hh
  rw [starProjection_congr _ _ hs] at hh
  exact hh

theorem incidence_projection_induction (N : ℕ) (hN : 0<N) (e : Sector N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    (AsymptoticQuotientIncidence.space N hN hε ht e z).starProjection
      (AsymptoticCongruenceQuotient.induction N hε ht z f)=
      AsymptoticCongruenceQuotient.induction N hε ht z ((countingSectorSpace N hN e).starProjection f) := by
  rw [incidence_projection_compression]
  exact QuantitativeEulerOldProjectionBlock.compressed_apply_isometry _ _ f

def weightedSectorSignRow (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  AsymptoticCongruenceQuotient.compression N hε ht (sectorSignRow N hN e i) z

theorem weightedSectorSignRow_induction (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    weightedSectorSignRow N hN e i hε ht z (AsymptoticCongruenceQuotient.induction N hε ht z f)=
      AsymptoticCongruenceQuotient.induction N hε ht z (sectorSignRow N hN e i f) :=
  QuantitativeEulerOldProjectionBlock.compressed_apply_isometry _ _ f

/-- Uniform positive gap for the literal original quotient incidence
projection. The coefficient precedes every sector, weight and root.
Only energies of actual old projections and normalizer rows occur. -/
theorem incidence_indexed_weighted_gap (N : ℕ) (hN : 0<N) :
    ∃ γ : ℝ,0<γ ∧ ∀ (e : Sector N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
      (z : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),
      v∈AsymptoticCongruenceQuotient.quotientSpace N hε ht z →
      γ*‖v-(AsymptoticQuotientIncidence.space N hN hε ht e z).starProjection v‖^2≤
        (∑ i : PrimeOldIndex N,
          ‖(AsymptoticCongruenceOldSpace.space N (oldGroup N hN i.1.val i.2)
            (primeOld_le N hN i) hε ht z).starProjection v‖^2)+
        ∑ i : SectorSignIndex N,‖weightedSectorSignRow N hN e i hε ht z v‖^2 := by
  obtain ⟨γ,hγ,hgap⟩ := countingSectorSpace_gap N hN
  refine ⟨γ,hγ,?_⟩
  intro e ε hε t ht z v hv
  rw [indexed_old_energy_eq]
  obtain ⟨f,rfl⟩ := hv
  simp only [LinearIsometry.coe_toLinearMap,incidence_projection_induction,
    weightedSectorSignRow_induction,← map_sub,LinearIsometry.norm_map,weightedLocalOldEnergy_induction]
  exact hgap e f

#print axioms sectorInduction_range
#print axioms incidence_projection_compression
#print axioms incidence_indexed_weighted_gap

end QuantitativeEulerEndpointPrepared
