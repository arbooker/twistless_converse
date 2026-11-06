module

public import QuantitativeEulerEndpointReconstructedEnergyTraceV1
public import QuantitativeEulerEndpointReconstructedPullbackV1

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
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

/-- Original-energy trace control for any regular subspace of the actual
reconstructed image. The geometric tails and leading coefficient one are
preserved by the proved isometric pullback. -/
theorem exists_reconstructed_image_energy_trace {N Q : ℕ} [NeZero N]
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
        primeOldOriginalEnergy sector q hqN hs P'.epsilon_pos (P'.s+4) x y≤a*‖y‖^2) →
      (countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
          (K*((wideDistortion L R R)^(P'.s+4))^2)*a<1 →
      trace volume (fun x => (V x).starProjection)≤
        trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N)
          P'.epsilon_pos (by omega : 1≤P'.s+4) sector x).starProjection)+
          ∑ i,(CongruenceSubgroup.Gamma0 N).index*
            (3*ENNReal.ofReal (H/sectorFamilyC N (NeZero.pos N) sector S hS i)⁻¹)+
          ENNReal.ofReal H⁻¹ := by
  dsimp only
  let P' := AsymptoticReconstructedCount.parameters A P
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_reconstructed_original_energy_trace A P D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hbound⟩ := hbound C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata F instF hF V instV hmV hcV hV a henergy hsmall
  let T := reconstructedPullback A (NeZero.pos N) P sector F V hF hV
  have hreg := reconstructed_pullback_regular A (NeZero.pos N) P sector F V hF hV hmV hcV
  have htrace := reconstructed_pullback_trace A (NeZero.pos N) P sector F V hF hV hmV hcV
  rw [← htrace]
  apply hbound H hH hdata T hreg.1 hreg.2
    (fun x => (reconstructed_pullback_le A (NeZero.pos N) P sector F V hF hV x).trans (hF x))
    a _ hsmall
  intro x hx v hv
  have hf := reconstructed_pullback_forward A (NeZero.pos N) P sector F V hF hV x v hv
  have he := henergy x hx _ hf.1
  simpa only [hf.2] using he

#print axioms exists_reconstructed_image_energy_trace
end QuantitativeEulerEndpointPrepared
