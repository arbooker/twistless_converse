module

public import QuantitativeEulerEndpointNewFreshLowTraceV1
public import QuantitativeEulerEndpointNewTailTargetV1
public import QuantitativeEulerEndpointFreshLowTraceV1
public import QuantitativeEulerEndpointPrimeStepV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory QuantitativeEulerDensityGenerators
open AsymptoticRegularTrace AsymptoticSectorSigns AsymptoticCornerKernel
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction QuantitativeNewGap
open QuantitativeSpectralCornerCutRow QuantitativeSpectralObservabilitySampling
open QuantitativeSpectralCoverUnweight
open AsymptoticRegularCompactBranch (Space)
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup AsymptoticMixing
open scoped Classical MatrixGroups ENNReal

/-- A proved one-prime trace contraction toward the literal total-new
trace plus a fixed O(1/H) old-tail cost, using only original Euler rows. -/
theorem exists_new_prime_trace_loss {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max ε⁻¹ 4≤H →
      (∀ i, (primeOldData N (NeZero.pos N) S hS i).B≤H) →
      ∀ (sector : Sector N) (t : ℕ) (ht : 1≤t),
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      ∀ (a : ℝ), 0≤a → ∀ (U : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (U x)],
      (∀ g h, Measurable (fun x => matrix (U x).starProjection g h)) →
      Covariant (fun x => (U x).starProjection) →
      (∀ x, U x≤newBaselineSurvivor N H sector hs hε t a x) →
      (∀ x, Supported (integralGroup q) (U x).starProjection) →
      ∀ (c d : ℝ), 0<c → 0<d → d^2=c^2*(q:ℝ)⁻¹/(2*((q-1:ℕ):ℝ)) →
      newObservationCost N (NeZero.pos N) S hS W Bobs H ε t*
        (K*((wideDistortion L R R)^t)^2)*(a+c^2)<1 →
      (q:ℝ)⁻¹*((trace volume (fun x => (U x).starProjection)).toReal-
        newTraceTarget N (NeZero.pos N) S hS H hε ht)≤
      (trace volume (fun x => (U x).starProjection)).toReal-
        (trace volume (fun x =>
          (freshStepSource N q (NeZero.pos N) hqN (sign sector.1) hs hε t U d x).starProjection)).toReal := by
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_new_fresh_low_trace P S hS hε
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro H hH hdata sector t ht
  dsimp only
  intro a ha U instU hmU hcU hU hsupport c d hc hd hscale hsmall
  let Y := min ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  have hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let hs := wideFreshRegion_compact L R R hZ
  let rows := freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs hε t U
  have hHpos : 0<H := (by norm_num : (0:ℝ)<4).trans_le ((le_max_right _ _).trans hH)
  have hlow := hbound H hH hdata sector t ht a ha U hmU hcU hU c hc hsmall
  rw [←newTraceTarget_ofReal N (NeZero.pos N) S hS hHpos hε ht] at hlow
  have hlowReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlow
  rw [ENNReal.toReal_ofReal (newTraceTarget_nonneg N (NeZero.pos N) S hS hHpos.le hε ht)] at hlowReal
  obtain ⟨M,hM⟩ := fresh_source_stack_bounded N q (NeZero.pos N) hqN (sign sector.1) hs hε t U
  have hr := fresh_source_rows_regular N q (NeZero.pos N) hqN (sign sector.1) hs hε t U hmU hcU
  have hf := projection_trace_finite_of_le volume U (newBaselineSurvivor N H sector hs hε t a)
    hU (newBaselineSurvivor_trace_finite N H sector hs hε t a)
  have hq : 1<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hcard : 0<Fintype.card (Fin (q-1)) := by
    simpa only [Fintype.card_fin] using Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  have htheta : (q:ℝ)⁻¹≤1 := (inv_le_one₀ (by linarith)).mpr hq.le
  have hh := fresh_step_of_low_trace volume AsymptoticRationalGroup.measurePreserving
    (integralGroup q) (primeLabels q) (primeLabels_separated q) hcard U hmU hcU rows
    (fun i => (hr i).1) (fun i => (hr i).2)
    (fresh_source_rows_supported N q (NeZero.pos N) hqN (sign sector.1) hs hε t U hsupport)
    (fresh_source_rows_fixed N q (NeZero.pos N) hqN (sign sector.1) hs hε t U)
    M hM hf hc hd (inv_pos.mpr (by linarith)) htheta
    (by simpa only [Fintype.card_fin] using hscale)
    (newTraceTarget N (NeZero.pos N) S hS H hε ht) hlowReal
  have hfactor : (1-(q:ℝ)⁻¹)/(Fintype.card (Fin (q-1)):ℝ)=(q:ℝ)⁻¹ := by
    rw [Fintype.card_fin,Nat.cast_sub (Fact.out : q.Prime).one_lt.le,Nat.cast_one]
    field_simp [ne_of_gt (lt_trans zero_lt_one hq),ne_of_gt (sub_pos.mpr hq)]
  rw [hfactor] at hh
  exact hh

#print axioms exists_new_prime_trace_loss
end QuantitativeEulerEndpointPrepared
