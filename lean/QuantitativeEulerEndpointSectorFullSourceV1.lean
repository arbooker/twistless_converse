module

public import QuantitativeEulerEndpointSectorFullDetectorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDensityGenerators
open AsymptoticRegularObservationRows AsymptoticObservationStack AsymptoticSectorSigns
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- Actual total-new source observability using only original Euler and
ramified observations and the literal total-new sampler. All old-row energies
have been eliminated; the actual old-tail kernel condition remains. -/
theorem exists_sector_source_full_original_observability {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) (hN2 : 2≤N) (sector : Sector N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      ∀ (t : ℕ) (ht : 1≤t) (x : ℍ), fundamentalGood N x →
      ∀ (v : Space), v∈AsymptoticOrbitRegion.Space
        (AsymptoticHyperbolicArea.terminal ε\AsymptoticHyperbolicArea.terminal H) x →
      quotientTailStack N (fun i => H/sectorFamilyC N (NeZero.pos N) sector S hS i) hε ht
        (sectorFamilySampled N (NeZero.pos N) sector H hε ht) x v=0 →
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      ‖v‖^2≤sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H ε t*
        (K*((wideDistortion L R R)^t)^2*
          primeOldOriginalEnergy sector q hqN hs hε t x v+
          ‖sectorSampling N (NeZero.pos N) sector H hε ht x v‖^2) := by
  obtain ⟨W,Bobs,hBobs,hobs⟩ := exists_sector_source_observability N (NeZero.pos N) sector S hS hε
  obtain ⟨Bg,hBg,D,hD,B,hB,K,hK,hdet⟩ := sectorDetector_full_original_energy P hN2 sector S hS W
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro H hH hdata t ht x hx v hv htail
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  obtain ⟨_hqN,hbound⟩ := hdet ε hε H hH0 C hBC q hqGood
  have hd := hbound t x v
  have ho := hobs H hH hdata t ht x hx v hv htail
  change ‖v‖^2≤sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H ε t*
    (‖sectorDetector N (NeZero.pos N) sector S hS W H hε t x v‖^2+
      ‖sectorSampling N (NeZero.pos N) sector H hε ht x v‖^2) at ho
  dsimp only at hd ⊢
  exact ho.trans (mul_le_mul_of_nonneg_left (add_le_add hd le_rfl)
    (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H ε t))

#print axioms exists_sector_source_full_original_observability
end QuantitativeEulerEndpointPrepared
