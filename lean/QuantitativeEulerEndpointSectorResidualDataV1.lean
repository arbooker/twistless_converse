module

public import QuantitativeEulerEndpointSectorRegularV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticRegularTrace AsymptoticRegularBranchFamily
open QuantitativeNewGap QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups lp ENNReal Classical

def sectorSampledRow (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (weightedSectorSignRow N hN sector i hε ht x).comp (fundamentalSampling N hN Y hε ht x)

theorem sectorSampledRow_regular (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) (Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix (sectorSampledRow N hN sector i Y hε ht x) g k)) ∧
      Covariant (sectorSampledRow N hN sector i Y hε ht) := by
  have hr := weightedSectorSignRow_regular N hN sector i hε ht
  have hs := fundamentalSampling_regular N hN Y hε ht
  exact ⟨matrix_comp_measurable _ _ hr.1 hs.1,covariant_comp _ _ hr.2 hs.2⟩

theorem sectorSampledRow_norm (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) (Y : ℝ) (hY : 0≤Y)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖sectorSampledRow N hN sector i Y hε ht x‖≤‖sectorSignRow N hN sector i‖*
      (QuantitativeSpectralObservabilitySampling.samplingBound N hN Y ε t*
        (8*QuantitativeSpectralCoverUnweight.coverBound N hN*(Y+3)+5)) := by
  apply (opNorm_comp_le _ _).trans
  exact mul_le_mul (weightedSectorSignRow_norm N hN sector i hε ht x)
    (fundamentalSampling_norm N hN Y hY hε ht x) (norm_nonneg _) (norm_nonneg _)

/-- The discarded signed Fricke row has actual input support rank O(1/H),
not merely output rank; all regularity requirements are discharged. -/
theorem sectorSampledTail_source_rank (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) {Y : ℝ} (hY : 0≤Y)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) {H : ℝ} (hH : 0<H) :
    trace volume (fun x => ((fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp
      (sectorSampledRow N hN sector i Y hε ht x)).kerᗮ.starProjection)≤
      (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal H⁻¹) := by
  have hr := sectorSampledRow_regular N hN sector i Y hε ht
  exact fundamentalTail_source_rank N hN hε ht hH _ hr.1 hr.2 _
    (sectorSampledRow_norm N hN sector i Y hY hε ht)

def sectorTailRow (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) (Y H : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp
    (sectorSampledRow N hN sector i Y hε ht x)

/-- Fixed geometric witnesses supplied by the actual signed Fricke
factorization, independent of every sampling and cap parameter. -/
structure SectorResidualData (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) (S : Finset SL(2,ℤ)) where
  C : ℝ
  B : ℝ
  L : ℝ
  K : ℝ
  n : ℕ
  w : Fin n → Fin 2 → List SL(2,ℤ)
  letters : ∀ j i a, a∈w j i → a∈signedGenerators S
  C_pos : 0<C
  B_pos : 0<B
  L_ge_one : 1≤L
  K_ge_one : 1≤K
  factor : ∀ Y : ℝ, B≤Y → ∀ (ε : ℝ) (hε : 0<ε) (t : ℕ) (ht : 1≤t) (x : ℍ),
    let D := commonResidualStack (signedGenerators S) (sectorSignBranches N hN i) w (sectorSignCoefficients sector i)
      (wideCompactCover_compact N hN (Y/C)) hε t x
    ∃ R : GeneratorData (signedGenerators S) →L[ℂ] ℓ²(OrbitGroup,ℂ),
      ‖R‖≤L*(1+ε*K*(Y/C+3)^2)^(2*t) ∧ ∀ v : ℓ²(OrbitGroup,ℂ),
        sectorSampledRow N hN sector i Y hε ht x v=R (D v)+sectorTailRow N hN sector i Y (Y/C) hε ht x v

def sectorResidualData (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    SectorResidualData N hN sector i S := Classical.choice (by
  obtain ⟨C,B,L,K,n,w,hw,hC,hB,hL,hK,hall⟩ :=
    exists_quotientRow_residual N hN S hS (sectorSignBranches N hN i) (sectorSignCoefficients sector i)
      (fun {_} hε {_} ht => weightedSectorSignRow N hN sector i hε ht)
      (fun {_} hε {_} ht => weightedSectorSignRow_range N hN sector i hε ht)
      (fun {_} hε {_} ht => weightedSectorSignRow_coordinate N hN sector i hε ht)
  refine ⟨⟨C,B,L,K,n,w,hw,hC,hB,hL,hK,?_⟩⟩
  intro Y hY ε hε t ht x
  obtain ⟨R,hR,_htrace,hfac⟩ := hall Y hY ε hε t ht x
  exact ⟨R,hR,hfac⟩)

def SectorResidualData.cost {N : ℕ} {hN : 0<N} {sector : Sector N} {i : SectorSignIndex N} {S : Finset SL(2,ℤ)}
    (d : SectorResidualData N hN sector i S) (Y ε : ℝ) (t : ℕ) : ℝ :=
  d.L*(1+ε*d.K*(Y/d.C+3)^2)^(2*t)

theorem SectorResidualData.cost_nonneg {N : ℕ} {hN : 0<N} {sector : Sector N} {i : SectorSignIndex N} {S : Finset SL(2,ℤ)}
    (d : SectorResidualData N hN sector i S) (Y ε : ℝ) (t : ℕ) : 0≤d.cost Y ε t := by
  have hL := zero_le_one.trans d.L_ge_one
  unfold cost
  rw [Nat.mul_comm 2 t,pow_mul]
  exact mul_nonneg hL (sq_nonneg _)

theorem SectorResidualData.norm_le {N : ℕ} {hN : 0<N} {sector : Sector N} {i : SectorSignIndex N} {S : Finset SL(2,ℤ)}
    (d : SectorResidualData N hN sector i S) {Y : ℝ} (hY : d.B≤Y)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : sectorTailRow N hN sector i Y (Y/d.C) hε ht x v=0) :
    ‖sectorSampledRow N hN sector i Y hε ht x v‖≤d.cost Y ε t*
      ‖commonResidualStack (signedGenerators S) (sectorSignBranches N hN i) d.w (sectorSignCoefficients sector i)
        (wideCompactCover_compact N hN (Y/d.C)) hε t x v‖ := by
  obtain ⟨R,hR,hfac⟩ := d.factor Y hY ε hε t ht x
  rw [hfac v,hv,add_zero]
  exact R.le_of_opNorm_le hR _

#print axioms sectorSampledTail_source_rank
#print axioms sectorResidualData
#print axioms SectorResidualData.norm_le
end QuantitativeEulerEndpointPrepared
