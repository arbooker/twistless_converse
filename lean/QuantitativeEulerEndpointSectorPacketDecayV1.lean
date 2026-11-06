module

public import QuantitativeEulerEndpointSectorChainSourceV1
public import QuantitativeEulerEndpointPrimeListV1
public import QuantitativeEulerEndpointPacketTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns AsymptoticHyperbolicArea
open QuantitativeEulerDensityGenerators QuantitativeHolomorphic QuantitativeSpectralObservability QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

/-- The actual fixed-threshold packet of original twist rows has excess
trace O(1/log n)+O(1/H) above the literal sector incidence trace, at fixed epsilon.
This is a regular trace theorem, not a finite classical Euler-count transfer. -/
theorem prepared_sector_packet_trace_decay (N : ℕ) [NeZero N] (hN : 2≤N) (sector : Sector N)
    (excluded : Finset ℕ) (hex : baselineDenominators N⊆excluded) (threshold : ℕ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    let P := prepared N hN excluded threshold
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∃ A0 : ℝ, 0<A0 ∧
      ∀ (C : ℝ), B≤C → ∀ (n : ℕ), 0<n → ∀ H : ℝ, max ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      ∀ (t : ℕ) (ht : 1≤t),
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant P*C)*(n:ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      let A := sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H ε t*
        (K*((wideDistortion L R R)^t)^2)
      let a := (2*(1+2*A))⁻¹
      let c := Real.sqrt a
      let U := closedNewBaselineSurvivor N H sector hs hε t a
      cornerMass (packetChain N (NeZero.pos N) (sign sector.1) hs hε t c U (goodPrimeList P n))≤
        sectorTraceTarget N (NeZero.pos N) sector S hS H hε ht+ε⁻¹*A0/Real.log (n+1:ℝ) := by
  intro P
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    endpoint_sector_chain_trace_bound P hN sector hex S hS hε
  obtain ⟨A0,hA0,hprod⟩ := goodPrimeList_prepared_product N hN excluded threshold
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,A0,hA0,?_⟩
  intro C hBC n hn H hH hdata t ht Y R hZ L hs A a c U
  have hA : 0≤A := mul_nonneg (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H ε t)
    (mul_nonneg hK (sq_nonneg _))
  have hc : 0<c := Real.sqrt_pos.mpr (baseline_threshold_pos (2*A) (by positivity))
  rw [packetChain_mass_eq N (NeZero.pos N) (sign sector.1) hs hε t c hc U (goodPrimeList P n)]
  have hl (p : EligiblePrime N) (hp : p∈goodPrimeList P n) : P.Good p.val ∧ (p.val:ℝ)≤(n:ℝ) := by
    obtain ⟨hg,hpn⟩ := goodPrimeList_mem P n p hp
    exact ⟨hg,by exact_mod_cast hpn⟩
  have hchain := hbound C hBC n H hH hdata t ht (goodPrimeList P n) (goodPrimeList_nodup P n) hl
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  have hmass : cornerMass U≤ε⁻¹ := closedNewBaseline_mass_le N H sector hs hε t a
  have hbase : cornerMass U-sectorTraceTarget N (NeZero.pos N) sector S hS H hε ht≤ε⁻¹ :=
    (sub_le_self _ (sectorTraceTarget_nonneg N (NeZero.pos N) sector S hS hH0 hε ht)).trans hmass
  have hb := (mul_le_mul_of_nonneg_left hbase (primeProduct_nonneg (goodPrimeList P n))).trans
    (mul_le_mul_of_nonneg_right (hprod n hn) (inv_nonneg.mpr hε.le))
  have he : (A0/Real.log (n+1:ℝ))*ε⁻¹=ε⁻¹*A0/Real.log (n+1:ℝ) := by ring
  rw [he] at hb
  exact (sub_le_iff_le_add.mp (hchain.trans hb)).trans_eq (add_comm _ _)

#print axioms prepared_sector_packet_trace_decay
end QuantitativeEulerEndpointPrepared
