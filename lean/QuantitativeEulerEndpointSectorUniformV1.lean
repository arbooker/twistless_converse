module

public import QuantitativeEulerEndpointSectorSignCoordinatesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open AsymptoticSectorSigns QuantitativeSpectralObservability QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- Uniform over every old direction and every sector. Constants are fixed
before the geometry, weight, and fresh prime, and the ramified rows retain
the actual sector eigenvalues (zero at repeated primes). -/
theorem wide_sectorSign_rows_original_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) (hN : 2≤N) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (sector : Sector N) (i : SectorSignIndex N)
        {s : Set ℍ} (hs : IsCompact s) {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤R) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖AsymptoticRegularBranchFamily.family (sectorSignBranches N (NeZero.pos N) i)
        (sectorSignCoefficients sector i) hs hε t x v‖^2≤
      K*((wideDistortion L R H)^t)^2*
        primeOldOriginalEnergy sector q hqN (wideFreshRegion_compact L R H hY) hε t x v := by
  let J := Sector N × SectorSignIndex N
  choose B hB K hK hb using fun j : J => sectorSignRingRow_original_control P hN j.1 j.2
  let B₀ := 1+∑ j : J, B j
  let K₀ := ∑ j : J, K j
  have hBn (j : J) : 0≤B j := zero_le_one.trans (hB j)
  have hB₀ : 1≤B₀ := by
    dsimp only [B₀]
    linarith [Finset.sum_nonneg (fun j (_ : j∈(Finset.univ : Finset J)) => hBn j)]
  have hBB (j : J) : B j≤B₀ := by
    have h := Finset.single_le_sum (fun k _ => hBn k) (Finset.mem_univ j)
    dsimp only [B₀]
    linarith
  have hKK (j : J) : K j≤K₀ := Finset.single_le_sum (fun k _ => hK k) (Finset.mem_univ j)
  refine ⟨B₀,hB₀,K₀,Finset.sum_nonneg (fun j _ => hK j),?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro sector i s hs ε R Y H hε hY hre hlo him t x v
  obtain ⟨_hqN,hqbound⟩ := hb (sector,i) C ((hBB _).trans hBC) q hqGood
  have hh := hqbound hs hε hY hre hlo him t x v
  rw [compactAction_sectorSignRingRow] at hh
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (hKK (sector,i)) (sq_nonneg _))
    (localOriginalEnergy_le_primeOld sector (sectorRowPrime N hN i) q hqN _ hε t x v)
    (localOriginalEnergy_nonneg _ _ _ _ _ _ _ _ _ _ _)
    (mul_nonneg (Finset.sum_nonneg (fun j _ => hK j)) (sq_nonneg _)))

#print axioms wide_sectorSign_rows_original_bound
end QuantitativeEulerEndpointPrepared
