module

public import QuantitativeEulerEndpointSectorFamilyV1
public import QuantitativeSpectralExceptionalSourceObservabilityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticCongruenceQuotient AsymptoticRegularBranchFamily
open QuantitativeNewGap QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open QuantitativeSpectralFiniteReduction
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

variable (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
  (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)

theorem sectorSampling_distance_le_detector {Y : ℝ}
    (hY : ∀ i, sectorFamilyB N hN sector S hS i≤Y)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (v : Space)
    (hz : quotientTailStack N (fun i => Y/sectorFamilyC N hN sector S hS i) hε ht
      (sectorFamilySampled N hN sector Y hε ht) x v=0) :
    let b := sectorFamilyBranches N hN
    let c := sectorFamilyCoefficients N hN sector
    let w := sectorFamilyWords N hN sector S hS
    let regions := fun i => wideCompactCover N (Y/sectorFamilyC N hN sector S hS i)
    let hs := fun i => wideCompactCover_compact N hN (Y/sectorFamilyC N hN sector S hS i)
    let hu' := enlargedRegion_compact b w regions hs hu
    ‖fundamentalSampling N hN Y hε ht x v-sectorSampling N hN sector Y hε ht x v‖^2≤
      ((sectorGap N hN)⁻¹*∑ i,(sectorFamilyCost N hN sector S hS Y ε t i)^2)*
        ‖enlargedDetector (signedGenerators S) b c hu' hε t x v‖^2 := by
  have hg := sectorSampling_gap N hN sector Y hε ht x v
  have hg' : sectorGap N hN*
      ‖fundamentalSampling N hN Y hε ht x v-sectorSampling N hN sector Y hε ht x v‖^2≤
      ∑ i,‖sectorFamilySampled N hN sector Y hε ht x i v‖^2 := by
    simpa only [Fintype.sum_sum_type,sectorFamilySampled] using hg
  have he := sectorFamily_energy_le_detector N hN sector S hS hY hu hε ht x v hz
  have hh := mul_le_mul_of_nonneg_left (hg'.trans he) (inv_nonneg.mpr (sectorGap_pos N hN).le)
  simpa only [←mul_assoc,inv_mul_cancel₀ (sectorGap_pos N hN).ne',one_mul] using hh

def sectorObservationCost (W : Finset (List SL(2,ℤ))) (B Y ε : ℝ) (t : ℕ) : ℝ :=
  (terminalObservationConstant S W*(1+B^2*(Y+3)^2)^(2*t))*
    (1+(sectorGap N hN)⁻¹*∑ i,(sectorFamilyCost N hN sector S hS Y ε t i)^2)

theorem sectorObservationCost_nonneg (W : Finset (List SL(2,ℤ))) (B Y ε : ℝ) (t : ℕ) :
    0≤sectorObservationCost N hN sector S hS W B Y ε t := by
  have hL := zero_le_one.trans (terminalObservationConstant_ge_one S W)
  have hγ := (sectorGap_pos N hN).le
  unfold sectorObservationCost
  positivity

/-- Source observability projected onto the literal original-incidence
sector, with actual old and canonical sign residuals and their common tail. -/
theorem exists_sector_source_observability {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      ∀ Y : ℝ, max ε⁻¹ 4≤Y → (∀ i, sectorFamilyB N hN sector S hS i≤Y) →
      ∀ (t : ℕ) (ht : 1≤t) (x : ℍ), fundamentalGood N x → ∀ v : Space,
      v∈AsymptoticOrbitRegion.Space
        (AsymptoticHyperbolicArea.terminal ε\AsymptoticHyperbolicArea.terminal Y) x →
      quotientTailStack N (fun i => Y/sectorFamilyC N hN sector S hS i) hε ht
        (sectorFamilySampled N hN sector Y hε ht) x v=0 →
      let b := sectorFamilyBranches N hN
      let c := sectorFamilyCoefficients N hN sector
      let w := sectorFamilyWords N hN sector S hS
      let regions := fun i => wideCompactCover N (Y/sectorFamilyC N hN sector S hS i)
      let hs := fun i => wideCompactCover_compact N hN (Y/sectorFamilyC N hN sector S hS i)
      let hu := enlargedRegion_compact b w regions hs (wordRegion_compact W hε Y)
      ‖v‖^2≤sectorObservationCost N hN sector S hS W B Y ε t*
        (‖enlargedDetector (signedGenerators S) b c hu hε t x v‖^2+
          ‖sectorSampling N hN sector Y hε ht x v‖^2) := by
  let b := sectorFamilyBranches N hN
  let c := sectorFamilyCoefficients N hN sector
  let w := sectorFamilyWords N hN sector S hS
  let regions := fun Y i => wideCompactCover N (Y/sectorFamilyC N hN sector S hS i)
  let hs := fun Y i => wideCompactCover_compact N hN (Y/sectorFamilyC N hN sector S hS i)
  obtain ⟨W,B,hB,_hW,hobs⟩ := exists_enlarged_source_observability N hN S hS b w c regions hs hε
  refine ⟨W,B,hB,?_⟩
  intro Y hY hdata t ht x hx v hv htail
  have ho := hobs Y hY t ht x hx _ le_rfl v hv
  have hg := sectorSampling_distance_le_detector N hN sector S hS hdata
    (wordRegion_compact W hε Y) hε ht x v htail
  dsimp only at ho hg ⊢
  have hK : 0≤terminalObservationConstant S W*(1+B^2*(Y+3)^2)^(2*t) := by
    have hL := zero_le_one.trans (terminalObservationConstant_ge_one S W)
    positivity
  have hA : 0≤(sectorGap N hN)⁻¹*∑ i,(sectorFamilyCost N hN sector S hS Y ε t i)^2 :=
    mul_nonneg (inv_nonneg.mpr (sectorGap_pos N hN).le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact observability_projected (AsymptoticQuotientIncidence.space N hN hε ht sector x)
    v (fundamentalSampling N hN Y hε ht x v) _ _ _ hK hA ho hg

#print axioms sectorSampling_distance_le_detector
#print axioms exists_sector_source_observability
end QuantitativeEulerEndpointPrepared
