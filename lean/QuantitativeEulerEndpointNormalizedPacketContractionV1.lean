module

public import QuantitativeEulerEndpointNormalizedCombinedPacketV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularReconstruction QuantitativeHolomorphic
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}

/-- The sharp contraction is now for a single source packet of fixed normalized
rows, including its baseline as the first row. There is no incoming baseline-energy premise. -/
theorem exists_normalized_combined_packet_contraction
    (A : Certificate N Q hQ) (P : Parameters A)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (hex : baselineDenominators N⊆excluded)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ C : ℝ, B≤C → ∀ X H : ℝ, max P'.ε⁻¹ 4≤H →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P'.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*X^4
      let hs := wideFreshRegion_compact L R R hZ
      let J := (countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
        (K*((wideDistortion L R R)^(P'.s+4))^2)
      let a := (2*(1+2*J))⁻¹
      let c := Real.sqrt a
      ∀ (F : ℍ → ClosedSubmodule ℂ Space),
      (∀ g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k)) →
      Covariant (fun x => (F x).toSubmodule.starProjection) →
      ∀ _hF : ∀ x,(F x).toSubmodule≤TerminalSpace A P' x,
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P'.epsilon_pos (by omega : 1≤P'.s+4)+H⁻¹
      ∀ l : List (EligiblePrime N), l.Nodup →
      (∀ p∈l,D₀.Good p.val ∧ (p.val:ℝ)≤X ∧ ¬p.val∣Q) →
      (∀ p∈l,∀ x,Supported (integralGroup p.val) (F x).toSubmodule.starProjection) →
      cornerMass (fun x => QuantitativeSpectralDeflationChain.chain (F x)
        (fun i => normalizedCombinedRows A P sector hs l i x) c (l.length+1))-target ≤
        (l.map primeFactor).prod*(cornerMass F-target) := by
  intro P'
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    endpoint_reconstructed_chain_trace_bound A P D₀ hN2 sector hex S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC X H hH hdata Y R hZ L hs J a c F hmF hcF hF target l hnodup hl hsF
  have hJ : 0≤J := mul_nonneg
    (mul_nonneg (sq_nonneg _) (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)))
    (mul_nonneg hK (sq_nonneg _))
  have ha : 0<a := baseline_threshold_pos (2*J) (mul_nonneg (by norm_num) hJ)
  have hc : 0<c := Real.sqrt_pos.mpr ha
  have hb := hbound C hBC X H hH hdata (fun x => (F x).toSubmodule) hmF hcF hF l hnodup hl hsF
  have he := normalized_source_packet_mass A P sector F hs a c l hF hmF hcF ha hc
  have hbase := reconstructed_baseline_mass_le A P sector (fun x => (F x).toSubmodule)
    hF hmF hcF hs a
  have hchain : (fun x => QuantitativeSpectralDeflationChain.chain (F x)
      (fun i => normalizedCombinedRows A P sector hs l i x) c (l.length+1))=
      normalizedSourcePacket A P sector F hs a c l :=
    funext (normalized_combined_chain A P sector hs l F a)
  rw [hchain,he]
  exact hb.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hbase target) (primeProduct_nonneg l))

#print axioms exists_normalized_combined_packet_contraction
end QuantitativeEulerEndpointPrepared
