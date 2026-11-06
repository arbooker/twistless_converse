module

public import QuantitativeEulerEndpointReconstructedBaselineStepV1

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

/-- All primes in a finite block use one identical observation region and
one identical reconstructed baseline cut. This preserves the exact spectral
subspace while applying the original one-prime contraction at every prime. -/
theorem exists_common_reconstructed_prime_loss {N Q : ℕ} [NeZero N]
    {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (X : ℝ) (q : ℕ) [Fact q.Prime], D₀.Good q → (q:ℝ)≤X →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max P'.ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P'.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*X^4
      let hs := wideFreshRegion_compact L R R hZ
      ∀ (F : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (F x)],
      ∀ hF : ∀ x,F x≤TerminalSpace A P' x,
      ∀ (V : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (V x)],
      (∀ g k,Measurable (fun x => matrix (V x).starProjection g k)) →
      Covariant (fun x => (V x).starProjection) →
      ∀ a : ℝ, 0≤a →
      (∀ x,V x≤reconstructedBaseline A P sector F hF hs a x) →
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
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_reconstructed_baseline_prime_loss A P D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC X q hqPrime hgood hqX
  have hqpos : 0<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  let Cq := C*(X^4/(q:ℝ)^4)
  have hpow : (q:ℝ)^4≤X^4 := pow_le_pow_left₀ hqpos.le hqX 4
  have hCq : B≤Cq := hBC.trans (by
    have hratio : 1≤X^4/(q:ℝ)^4 := (one_le_div (pow_pos hqpos 4)).mpr hpow
    have hh := mul_le_mul_of_nonneg_left hratio (zero_le_one.trans (hB.trans hBC))
    simpa only [mul_one] using hh)
  have hscale : (2*generatorTransportConstant D₀*Cq)*(q:ℝ)^4=
      (2*generatorTransportConstant D₀*C)*X^4 := by
    dsimp only [Cq]
    field_simp
  obtain ⟨hqN,hbound⟩ := hbound Cq hCq q hgood
  refine ⟨hqN,?_⟩
  simpa only [hscale] using hbound

#print axioms exists_common_reconstructed_prime_loss
end QuantitativeEulerEndpointPrepared
