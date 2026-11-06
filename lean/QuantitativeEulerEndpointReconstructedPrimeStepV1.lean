module

public import QuantitativeEulerEndpointReconstructedFreshLowV1
public import QuantitativeEulerEndpointReconstructedFiniteV1
public import QuantitativeEulerEndpointSectorPrimeStepV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap QuantitativeEulerDensityGenerators
open AsymptoticRegularTrace AsymptoticSectorSigns AsymptoticCornerKernel AsymptoticOrbitDiagonal
open FinitenessCertificate FinitenessGlobalHeight QuantitativeHolomorphic AsymptoticRegularReconstruction
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction QuantitativeNewGap
open QuantitativeSpectralExceptionalReconstructionTail
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticMixing
open QuantitativeSpectralCornerCutRow
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

/-- Original one-prime trace contraction inside the normalized reconstructed
image, toward literal sector incidence plus geometric tails. Baseline energy,
fresh support and the explicit smallness threshold remain inputs for the
successive spectral-cut construction. No finite-trace premise remains. -/
theorem exists_reconstructed_prime_trace_loss {N Q : ℕ} [NeZero N]
    {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], D₀.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max P'.ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P'.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*(q : ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      ∀ (F : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (F x)],
      ∀ hF : ∀ x,F x≤TerminalSpace A P' x,
      ∀ (V : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (V x)],
      (∀ g k,Measurable (fun x => matrix (V x).starProjection g k)) →
      Covariant (fun x => (V x).starProjection) →
      (∀ x,V x≤reconstructedImage A (NeZero.pos N) P sector F hF x) → ∀ a : ℝ,
      (∀ x,fundamentalGood N x → ∀ y∈V x,
        ‖newBaselineDetector N sector hs P'.epsilon_pos (P'.s+4) x y‖^2≤a*‖y‖^2) →
      (∀ x,Supported (integralGroup q) (V x).starProjection) →
      ∀ (c d : ℝ), 0<c → 0<d → d^2=c^2*(q:ℝ)⁻¹/(2*((q-1:ℕ):ℝ)) →
      (countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
          (K*((wideDistortion L R R)^(P'.s+4))^2)*(a+c^2)<1 →
      (q:ℝ)⁻¹*((trace volume (fun x => (V x).starProjection)).toReal-
        (sectorTraceTarget N (NeZero.pos N) sector S hS H P'.epsilon_pos (by omega : 1≤P'.s+4)+H⁻¹))≤
      (trace volume (fun x => (V x).starProjection)).toReal-
        (trace volume (fun x =>
          (freshStepSource N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V d x).starProjection)).toReal := by
  dsimp only
  let P' := AsymptoticReconstructedCount.parameters A P
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_reconstructed_fresh_low_trace A P D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hbound⟩ := hbound C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata F instF hF V instV hmV hcV hV a hbase hsupport c d hc hd hscale hsmall
  let Y := min P'.ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  have hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*generatorTransportConstant D₀*C)*(q : ℝ)^4
  let hs := wideFreshRegion_compact L R R hZ
  let rows := freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V
  have hHpos : 0<H := (by norm_num : (0:ℝ)<4).trans_le ((le_max_right _ _).trans hH)
  have ht : 1≤P'.s+4 := by omega
  let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P'.epsilon_pos ht+H⁻¹
  have hn : 0≤target := add_nonneg
    (sectorTraceTarget_nonneg N (NeZero.pos N) sector S hS hHpos.le P'.epsilon_pos ht)
    (inv_nonneg.mpr hHpos.le)
  have he : ENNReal.ofReal target =
      trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N) P'.epsilon_pos ht sector x).starProjection)+
        ∑ i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H/sectorFamilyC N (NeZero.pos N) sector S hS i)⁻¹)+
          ENNReal.ofReal H⁻¹ := by
    change ENNReal.ofReal (sectorTraceTarget N (NeZero.pos N) sector S hS H P'.epsilon_pos ht+H⁻¹) = _
    rw [ENNReal.ofReal_add
      (sectorTraceTarget_nonneg N (NeZero.pos N) sector S hS hHpos.le P'.epsilon_pos ht)
      (inv_nonneg.mpr hHpos.le),sectorTraceTarget_ofReal N (NeZero.pos N) sector S hS hHpos P'.epsilon_pos ht]
  have hlow := hbound H hH hdata F hF V hmV hcV hV a hbase c hc hsmall
  rw [←he] at hlow
  have hlowReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlow
  rw [ENNReal.toReal_ofReal hn] at hlowReal
  obtain ⟨M,hM⟩ := fresh_source_stack_bounded N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V
  have hr := fresh_source_rows_regular N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V hmV hcV
  have hf := reconstructed_image_trace_finite A (NeZero.pos N) P sector F V hF hV hmV hcV
  have hq : 1<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hcard : 0<Fintype.card (Fin (q-1)) := by
    simpa only [Fintype.card_fin] using Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  have htheta : (q:ℝ)⁻¹≤1 := (inv_le_one₀ (by linarith)).mpr hq.le
  have hh := fresh_step_of_low_trace volume AsymptoticRationalGroup.measurePreserving
    (integralGroup q) (primeLabels q) (primeLabels_separated q) hcard V hmV hcV rows
    (fun i => (hr i).1) (fun i => (hr i).2)
    (fresh_source_rows_supported N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V hsupport)
    (fresh_source_rows_fixed N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V)
    M hM hf hc hd (inv_pos.mpr (by linarith)) htheta
    (by simpa only [Fintype.card_fin] using hscale) target hlowReal
  have hfactor : (1-(q:ℝ)⁻¹)/(Fintype.card (Fin (q-1)):ℝ)=(q:ℝ)⁻¹ := by
    rw [Fintype.card_fin,Nat.cast_sub (Fact.out : q.Prime).one_lt.le,Nat.cast_one]
    field_simp [ne_of_gt (lt_trans zero_lt_one hq),ne_of_gt (sub_pos.mpr hq)]
  rw [hfactor] at hh
  exact hh

#print axioms exists_reconstructed_prime_trace_loss
end QuantitativeEulerEndpointPrepared
