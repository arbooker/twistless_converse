module

public import QuantitativeEulerEndpointNewEnergyTraceV1
public import QuantitativeEulerEndpointNewBaselineRegularV1
public import QuantitativeEulerEndpointCompressedRowsV1

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
open scoped Classical MatrixGroups ENNReal

/-- On any regular source below the actual fixed-original cutoff, the
compressed low fresh-stack space is bounded by total-new plus old-tail cost. -/
theorem exists_new_fresh_low_trace {N : ℕ} [NeZero N]
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
      ∀ c : ℝ, 0<c →
      newObservationCost N (NeZero.pos N) S hS W Bobs H ε t*
        (K*((wideDistortion L R R)^t)^2)*(a+c^2)<1 →
      trace volume (fun x =>
        (nextSpace (U x) (AsymptoticPolarIsometry.absolute
          (AsymptoticObservationStack.stack
            (freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs hε t U x))) c).starProjection)≤
      trace volume (fun x => (AsymptoticTotalNewCorner.stripSpace N (NeZero.pos N) hε ht x).starProjection)+
        ∑ i, (CongruenceSubgroup.Gamma0 N).index*
          (3*ENNReal.ofReal (H/(primeOldData N (NeZero.pos N) S hS i).C)⁻¹) := by
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_new_original_energy_trace P S hS hε
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro H hH hdata sector t ht
  dsimp only
  intro a ha U instU hmU hcU hU c hc hsmall
  let Y := min ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  have hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let hs := wideFreshRegion_compact L R R hZ
  let rows := freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs hε t U
  let T := fun x => AsymptoticPolarIsometry.absolute (AsymptoticObservationStack.stack (rows x))
  let F := fun x => nextSpace (U x) (T x) c
  obtain ⟨M,hM⟩ := fresh_source_stack_bounded N q (NeZero.pos N) hqN (sign sector.1) hs hε t U
  have hr := fresh_source_rows_regular N q (NeZero.pos N) hqN (sign sector.1) hs hε t U hmU hcU
  have hT := stack_absolute_regular rows (fun i => (hr i).1) (fun i => (hr i).2) M hM
  have hMT (x : ℍ) : ‖T x‖≤M := by
    simpa only [T,AsymptoticPolarIsometry.absolute_opNorm] using hM x
  have hF := (QuantitativeSpectralRegularCornerStep.step_regular U T hmU hcU hT.1 hT.2 M hMT c hc).1
  apply hbound H hH hdata sector t ht F hF.1 hF.2
    (fun x v hv => nextSpace_le _ _ _ (hU x (nextSpace_le _ _ _ hv))) (a+c^2) _ hsmall
  intro x _hx v hv
  have hvU : v∈U x := nextSpace_le _ _ _ hv
  have hb := newBaselineSurvivor_energy N H sector hs hε t a ha x v (hU x hvU)
  have he := nextSpace_energy (U x) (T x) c v hv
  have heq : AsymptoticObservationStack.stack (rows x) v=
      AsymptoticObservationStack.stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N)
        hqN (sign sector.1) hs hε t i x) v := by
    ext i : 1
    exact fresh_source_rows_apply N q (NeZero.pos N) hqN (sign sector.1) hs hε t U x i v hvU
  change ‖AsymptoticPolarIsometry.absolute (AsymptoticObservationStack.stack (rows x)) v‖^2≤_ at he
  rw [←AsymptoticPolarIsometry.absolute_norm,heq] at he
  rw [primeOldOriginalEnergy_split]
  exact (add_le_add hb he).trans_eq (by ring)

#print axioms exists_new_fresh_low_trace
end QuantitativeEulerEndpointPrepared
