module

public import QuantitativeEulerEndpointReconstructedImageEnergyV1
public import QuantitativeEulerEndpointSectorFreshLowTraceV1

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
open QuantitativeSpectralCornerCutRow
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

/-- The low fresh-stack space inside the actual reconstructed image has
trace at most the literal sector trace plus all explicit geometric tails.
The baseline energy bound is retained as an input for a baseline spectral cut. -/
theorem exists_reconstructed_fresh_low_trace {N Q : ℕ} [NeZero N]
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
      ∀ c : ℝ, 0<c →
      (countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
          (K*((wideDistortion L R R)^(P'.s+4))^2)*(a+c^2)<1 →
      trace volume (fun x =>
        (nextSpace (V x) (AsymptoticPolarIsometry.absolute
          (AsymptoticObservationStack.stack
            (freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V x))) c).starProjection)≤
        trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N)
          P'.epsilon_pos (by omega : 1≤P'.s+4) sector x).starProjection)+
          ∑ i,(CongruenceSubgroup.Gamma0 N).index*
            (3*ENNReal.ofReal (H/sectorFamilyC N (NeZero.pos N) sector S hS i)⁻¹)+
          ENNReal.ofReal H⁻¹ := by
  dsimp only
  let P' := AsymptoticReconstructedCount.parameters A P
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_reconstructed_image_energy_trace A P D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hbound⟩ := hbound C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata F instF hF V instV hmV hcV hV a hbase c hc hsmall
  let Y := min P'.ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  have hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*generatorTransportConstant D₀*C)*(q : ℝ)^4
  let hs := wideFreshRegion_compact L R R hZ
  let rows := freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V
  let T := fun x => AsymptoticPolarIsometry.absolute (AsymptoticObservationStack.stack (rows x))
  let V' := fun x => nextSpace (V x) (T x) c
  obtain ⟨M,hM⟩ := fresh_source_stack_bounded N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V
  have hr := fresh_source_rows_regular N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V hmV hcV
  have hT := stack_absolute_regular rows (fun i => (hr i).1) (fun i => (hr i).2) M hM
  have hMT (x : ℍ) : ‖T x‖≤M := by
    simpa only [T,AsymptoticPolarIsometry.absolute_opNorm] using hM x
  have hreg := (QuantitativeSpectralRegularCornerStep.step_regular V T hmV hcV hT.1 hT.2 M hMT c hc).1
  apply hbound H hH hdata F hF V' hreg.1 hreg.2
    (fun x => (nextSpace_le (V x) (T x) c).trans (hV x)) (a+c^2) _ hsmall
  intro x hx v hv
  have hvV : v∈V x := nextSpace_le _ _ _ hv
  have hb := hbase x hx v hvV
  have he := nextSpace_energy (V x) (T x) c v hv
  have heq : AsymptoticObservationStack.stack (rows x) v=
      AsymptoticObservationStack.stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N)
        hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) i x) v := by
    ext i : 1
    exact fresh_source_rows_apply N q (NeZero.pos N) hqN (sign sector.1) hs P'.epsilon_pos (P'.s+4) V x i v hvV
  change ‖AsymptoticPolarIsometry.absolute (AsymptoticObservationStack.stack (rows x)) v‖^2≤_ at he
  rw [←AsymptoticPolarIsometry.absolute_norm,heq] at he
  rw [primeOldOriginalEnergy_split]
  exact (_root_.add_le_add hb he).trans_eq (by ring)

#print axioms exists_reconstructed_fresh_low_trace
end QuantitativeEulerEndpointPrepared
