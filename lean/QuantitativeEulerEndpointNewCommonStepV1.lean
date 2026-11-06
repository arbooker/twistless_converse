module

public import QuantitativeEulerEndpointNewPrimeStepV1

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

/-- All good primes up to X use exactly one enlarged observation region.
Rescaling the certificate height parameter makes the region identical,
without a comparison between noncommuting compressed spectral cuts. -/
theorem exists_common_new_prime_trace_loss {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (X : ℝ) (q : ℕ) [Fact q.Prime], P.Good q → (q:ℝ)≤X →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max ε⁻¹ 4≤H →
      (∀ i, (primeOldData N (NeZero.pos N) S hS i).B≤H) →
      ∀ (sector : Sector N) (t : ℕ) (ht : 1≤t),
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant P*C)*X^4
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
    exists_new_prime_trace_loss P S hS hε
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC X q hqPrime hqGood hqX
  have hqpos : 0<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  let Cq := C*(X^4/(q:ℝ)^4)
  have hpow : (q:ℝ)^4≤X^4 := pow_le_pow_left₀ hqpos.le hqX 4
  have hCq : B≤Cq := hBC.trans (by
    have hratio : 1≤X^4/(q:ℝ)^4 := (one_le_div (pow_pos hqpos 4)).mpr hpow
    have hh := mul_le_mul_of_nonneg_left hratio (zero_le_one.trans (hB.trans hBC))
    simpa only [mul_one] using hh)
  have hscale : (2*generatorTransportConstant P*Cq)*(q:ℝ)^4=
      (2*generatorTransportConstant P*C)*X^4 := by
    dsimp only [Cq]
    field_simp
  obtain ⟨hqN,hbound⟩ := hbound Cq hCq q hqGood
  refine ⟨hqN,?_⟩
  simpa only [hscale] using hbound

#print axioms exists_common_new_prime_trace_loss
end QuantitativeEulerEndpointPrepared
