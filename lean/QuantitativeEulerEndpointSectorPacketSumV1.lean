module

public import QuantitativeEulerEndpointSectorPacketDecayV1
public import AsymptoticTotalNewTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

structure SectorPacketWitness (N : ℕ) [NeZero N] (hN : 2≤N) (sector : Sector N)
    (excluded : Finset ℕ) (threshold : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) where
  W : Finset (List SL(2,ℤ))
  Bobs : ℝ
  hBobs : 1≤Bobs
  Bg : ℝ
  hBg : 1≤Bg
  D : ℝ
  hD : 1≤D
  B : ℝ
  hB : 1≤B
  K : ℝ
  hK : 0≤K
  A0 : ℝ
  hA0 : 0<A0
  decay : let P := prepared N hN excluded threshold
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
      sectorTraceTarget N (NeZero.pos N) sector S hS H hε ht+ε⁻¹*A0/Real.log (n+1:ℝ)

def sectorPacketWitness (N : ℕ) [NeZero N] (hN : 2≤N) (sector : Sector N)
    (excluded : Finset ℕ) (hex : baselineDenominators N⊆excluded) (threshold : ℕ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) : SectorPacketWitness N hN sector excluded threshold S hS hε :=
  Classical.choice (by
    obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,A0,hA0,hdecay⟩ :=
      prepared_sector_packet_trace_decay N hN sector excluded hex threshold S hS hε
    exact ⟨⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,A0,hA0,hdecay⟩⟩)

variable {N : ℕ} [NeZero N] {hN : 2≤N} {sector : Sector N}
  {excluded : Finset ℕ} {threshold : ℕ} {S : Finset SL(2,ℤ)}
  {hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N}
  {ε : ℝ} {hε : 0<ε}

def SectorPacketWitness.packet
    (d : SectorPacketWitness N hN sector excluded threshold S hS hε)
    (n : ℕ) (H : ℝ) (t : ℕ) : ℍ → ClosedSubmodule ℂ Space :=
  let P := prepared N hN excluded threshold
  let R := d.Bg*(d.D*H+2+1)/min 1 (min ε (1/4))
  let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos d.Bg 2 (d.D*H))
  let L := (2*generatorTransportConstant P*d.B)*(n:ℝ)^4
  let hs := wideFreshRegion_compact L R R hZ
  let A := sectorObservationCost N (NeZero.pos N) sector S hS d.W d.Bobs H ε t*
    (d.K*((wideDistortion L R R)^t)^2)
  let a := (2*(1+2*A))⁻¹
  packetChain N (NeZero.pos N) (sign sector.1) hs hε t (Real.sqrt a)
    (closedNewBaselineSurvivor N H sector hs hε t a) (goodPrimeList P n)

theorem SectorPacketWitness.packet_bound
    (d : SectorPacketWitness N hN sector excluded threshold S hS hε)
    {n : ℕ} (hn : 0<n) {H : ℝ} (hH : max ε⁻¹ 4≤H)
    (hdata : ∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H)
    {t : ℕ} (ht : 1≤t) :
    cornerMass (d.packet n H t)≤sectorTraceTarget N (NeZero.pos N) sector S hS H hε ht+
      ε⁻¹*d.A0/Real.log (n+1:ℝ) :=
  d.decay d.B le_rfl n hn H hH hdata t ht

/-- The literal original-row packets, summed over all original incidence
sectors, have only one total local-new leading coefficient. -/
theorem prepared_sector_packet_sum (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (hex : baselineDenominators N⊆excluded) (threshold : ℕ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) {n : ℕ} (hn : 0<n) {H : ℝ} (hH : max ε⁻¹ 4≤H)
    (hdata : ∀ e i, sectorFamilyB N (NeZero.pos N) e S hS i≤H)
    {t : ℕ} (ht : 1≤t) :
    let d := fun e => sectorPacketWitness N hN e excluded hex threshold S hS hε
    ∑ e : Sector N,cornerMass ((d e).packet n H t)≤
      4*Real.pi*AsymptoticTotalNewCorner.coefficient N (NeZero.pos N)+
        (∑ e : Sector N,sectorTailConstant N (NeZero.pos N) e S hS)/H+
        ε⁻¹*(∑ e : Sector N,(d e).A0)/Real.log (n+1:ℝ) := by
  intro d
  have hb := Finset.sum_le_sum (fun e (_ : e∈(Finset.univ : Finset (Sector N))) =>
    (d e).packet_bound hn hH (hdata e) ht)
  simp only [sectorTraceTarget,Finset.sum_add_distrib,←Finset.sum_div,←Finset.mul_sum] at hb
  exact hb.trans (add_le_add (add_le_add
    (AsymptoticTotalNewCorner.totalTrace_le_coefficient N (NeZero.pos N) hε ht) le_rfl) le_rfl)

#print axioms sectorPacketWitness
#print axioms SectorPacketWitness.packet_bound
#print axioms prepared_sector_packet_sum
end QuantitativeEulerEndpointPrepared
