module

public import QuantitativeEulerEndpointNewOriginalRowsV1
public import QuantitativeEulerEndpointGoodInjectionV1
public import QuantitativeSpectralObservabilityOldTailSurvivorV1

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

/-- The actual compressed low space of the original observations has trace
at most the literal total-new space plus the proved old-tail rank cost.
The source is cut before intersecting with the tail kernel. -/
theorem exists_new_original_low_trace {N : ℕ} [NeZero N]
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
      ∀ (F : ℍ → Submodule ℂ Space) [∀ x, CompleteSpace (F x)],
      (∀ g h, Measurable (fun x => matrix (F x).starProjection g h)) →
      Covariant (fun x => (F x).starProjection) →
      (∀ x, F x≤AsymptoticOrbitRegion.Space
        (AsymptoticHyperbolicArea.terminal ε\AsymptoticHyperbolicArea.terminal H) x) →
      ∀ c : ℝ, 0<c →
      newObservationCost N (NeZero.pos N) S hS W Bobs H ε t*
        (K*((wideDistortion L R R)^t)^2)*c^2<1 →
      trace volume (fun x =>
        (nextSpace (F x) (newOriginalDetector N sector q hqN hs hε t x) c).starProjection)≤
      trace volume (fun x => (AsymptoticTotalNewCorner.stripSpace N (NeZero.pos N) hε ht x).starProjection)+
        ∑ i, (CongruenceSubgroup.Gamma0 N).index*
          (3*ENNReal.ofReal (H/(primeOldData N (NeZero.pos N) S hS i).C)⁻¹) := by
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hobs⟩ :=
    exists_new_source_full_original_observability P S hS hε
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hobs⟩ := hobs C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro H hH hdata sector t ht
  dsimp only
  intro F instF hmF hcF hF c hc hsmall
  let Y := min ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  have hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let hs := wideFreshRegion_compact L R R hZ
  let T := newOriginalDetector N sector q hqN hs hε t
  let U := fun x => nextSpace (F x) (T x) c
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  have hHpos : 0<H := (by norm_num : (0:ℝ)<4).trans_le ((le_max_right _ _).trans hH)
  let heights := fun i => H/(primeOldData N (NeZero.pos N) S hS i).C
  let Q := fun x => remaining (U x)
    (oldTailStack N (NeZero.pos N) (primeOldGroup N (NeZero.pos N)) (primeOld_le N (NeZero.pos N))
      H heights hε ht x)
  obtain ⟨MT,_hMT,hMT,hmT,hcT⟩ := newOriginalDetector_regular N sector q hqN hs hε t
  have hU := (QuantitativeSpectralRegularCornerStep.step_regular F T hmF hcF hmT hcT MT hMT c hc).1
  have hQ := oldTailStack_survivor_regular N (NeZero.pos N)
    (primeOldGroup N (NeZero.pos N)) (primeOld_le N (NeZero.pos N)) hH0 heights hε ht U hU.1 hU.2
  have htail := oldTailStack_survivor_trace N (NeZero.pos N)
    (primeOldGroup N (NeZero.pos N)) (primeOld_le N (NeZero.pos N)) hH0 heights
    (fun i => div_pos hHpos (primeOldData N (NeZero.pos N) S hS i).C_pos) hε ht U hU.1 hU.2
  have hC := newSampling_regular N (NeZero.pos N) H hε ht
  let MC := samplingBound N (NeZero.pos N) H ε t*(8*coverBound N (NeZero.pos N)*(H+3)+5)
  have hMC (x : ℍ) : ‖newSampling N (NeZero.pos N) H hε ht x‖≤MC :=
    (newSampling_norm N (NeZero.pos N) H hε ht x).trans
      (fundamentalSampling_norm N (NeZero.pos N) H hH0 hε ht x)
  have htrace : trace volume (fun x => (Q x).starProjection)≤
      trace volume (fun x => (AsymptoticTotalNewCorner.stripSpace N (NeZero.pos N) hε ht x).starProjection) := by
    apply trace_le_of_injective_map_good N (NeZero.pos N) Q
      (AsymptoticTotalNewCorner.stripSpace N (NeZero.pos N) hε ht) hQ.1 hQ.2
      (newSampling N (NeZero.pos N) H hε ht) hC.1 hC.2 MC hMC
    · intro x hx v hv hz
      have ho := hobs H hH hdata sector t ht x hx v (hF x (nextSpace_le _ _ _ hv.1)) hv.2
      dsimp only at ho
      have he := nextSpace_energy (F x) (T x) c v hv.1
      rw [newOriginalDetector_energy] at he
      have hn := newObservationCost_nonneg N (NeZero.pos N) S hS W Bobs H ε t
      have hA : 0≤K*((wideDistortion L R R)^t)^2 := mul_nonneg hK (sq_nonneg _)
      rw [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero] at ho
      have hbound := ho.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hA) hn)
      have hbound' : ‖v‖^2≤
          (newObservationCost N (NeZero.pos N) S hS W Bobs H ε t*
            (K*((wideDistortion L R R)^t)^2)*c^2)*‖v‖^2 := by
        simpa only [L,R,Y,mul_assoc] using hbound
      have hzero : ‖v‖^2=0 := by nlinarith [sq_nonneg ‖v‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
    · intro x _hx v _hv
      exact newSampling_mem N (NeZero.pos N) H hε ht x v
  exact htail.trans (add_le_add htrace le_rfl)

#print axioms exists_new_original_low_trace
end QuantitativeEulerEndpointPrepared
