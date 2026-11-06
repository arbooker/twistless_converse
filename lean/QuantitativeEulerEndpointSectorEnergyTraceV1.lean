module

public import QuantitativeEulerEndpointSectorFullSourceV1
public import QuantitativeEulerEndpointSectorFamilyRegularV1
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

/-- Any regular band source whose actual original-row energy is below
the explicit observation threshold has trace bounded by its literal sector incidence trace plus
the proved combined old-and-sign tail cost. No tail-kernel premise remains. -/
theorem exists_sector_original_energy_trace {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) (hN2 : 2≤N) (sector : Sector N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      ∀ (t : ℕ) (ht : 1≤t),
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
      ∀ a : ℝ,
      (∀ x, fundamentalGood N x → ∀ v∈F x,
        primeOldOriginalEnergy sector q hqN hs hε t x v≤a*‖v‖^2) →
      sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H ε t*
        (K*((wideDistortion L R R)^t)^2)*a<1 →
      trace volume (fun x => (F x).starProjection)≤
      trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N) hε ht sector x).starProjection)+
        ∑ i, (CongruenceSubgroup.Gamma0 N).index*
          (3*ENNReal.ofReal (H/sectorFamilyC N (NeZero.pos N) sector S hS i)⁻¹) := by
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hobs⟩ :=
    exists_sector_source_full_original_observability P hN2 sector S hS hε
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hobs⟩ := hobs C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro H hH hdata t ht
  dsimp only
  intro F instF hmF hcF hF a henergy hsmall
  let Y := min ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  have hHpos : 0<H := (by norm_num : (0:ℝ)<4).trans_le ((le_max_right _ _).trans hH)
  let heights := fun i => H/sectorFamilyC N (NeZero.pos N) sector S hS i
  let rows := sectorFamilySampled N (NeZero.pos N) sector H hε ht
  have hr := sectorFamilySampled_regular N (NeZero.pos N) sector H hε ht
  obtain ⟨M,hM,hb⟩ := sectorFamilySampled_bounded N (NeZero.pos N) sector hH0 hε ht
  let Q := fun x => remaining (F x) (quotientTailStack N heights hε ht rows x)
  have hQ := quotientTailStack_survivor_regular N (NeZero.pos N) heights hε ht rows
    (fun i => (hr i).1) (fun i => (hr i).2) M hM hb F hmF hcF
  have htail := quotientTailStack_survivor_trace N (NeZero.pos N) heights
    (fun i => div_pos hHpos (sectorFamilyC_pos N (NeZero.pos N) sector S hS i))
    hε ht rows (fun i => (hr i).1) (fun i => (hr i).2) M hM hb F hmF hcF
  have hC := sectorSampling_regular N (NeZero.pos N) sector H hε ht
  let MC := samplingBound N (NeZero.pos N) H ε t*(8*coverBound N (NeZero.pos N)*(H+3)+5)
  have hMC (x : ℍ) : ‖sectorSampling N (NeZero.pos N) sector H hε ht x‖≤MC :=
    (sectorSampling_norm N (NeZero.pos N) sector H hε ht x).trans
      (fundamentalSampling_norm N (NeZero.pos N) H hH0 hε ht x)
  have htrace : trace volume (fun x => (Q x).starProjection)≤
      trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N) hε ht sector x).starProjection) := by
    apply trace_le_of_injective_map_good N (NeZero.pos N) Q
      (AsymptoticQuotientIncidence.space N (NeZero.pos N) hε ht sector) hQ.1 hQ.2
      (sectorSampling N (NeZero.pos N) sector H hε ht) hC.1 hC.2 MC hMC
    · intro x hx v hv hz
      have ho := hobs H hH hdata t ht x hx v (hF x hv.1) hv.2
      dsimp only at ho
      have he := henergy x hx v hv.1
      have hn := sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H ε t
      have hA : 0≤K*((wideDistortion L R R)^t)^2 := mul_nonneg hK (sq_nonneg _)
      rw [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero] at ho
      have hbound := ho.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hA) hn)
      have hbound' : ‖v‖^2≤
          (sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H ε t*
            (K*((wideDistortion L R R)^t)^2)*a)*‖v‖^2 := by
        simpa only [L,R,Y,mul_assoc] using hbound
      have hzero : ‖v‖^2=0 := by nlinarith [sq_nonneg ‖v‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
    · intro x _hx v _hv
      exact sectorSampling_mem N (NeZero.pos N) sector H hε ht x v
  exact htail.trans (add_le_add htrace le_rfl)

#print axioms exists_sector_original_energy_trace
end QuantitativeEulerEndpointPrepared
