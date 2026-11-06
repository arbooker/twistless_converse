module

public import QuantitativeEulerEndpointReconstructedOriginalV1
public import QuantitativeEulerEndpointReconstructedQuotientTailV1
public import QuantitativeEulerEndpointGoodInjectionV1
public import QuantitativeEulerEndpointSectorFamilyRegularV1

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

/-- Original-energy trace bound on the actual normalized terminal source.
All boundary, upper-height, and combined old/sign tails are removed with
proved geometric rank costs. The leading sector trace has coefficient ONE.
No band support of the reconstructed vector, or small lower tail, is assumed. -/
theorem exists_reconstructed_original_energy_trace {N Q : ℕ} [NeZero N]
    {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P sector
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
      (∀ g k,Measurable (fun x => matrix (F x).starProjection g k)) →
      Covariant (fun x => (F x).starProjection) →
      (∀ x,F x≤TerminalSpace A P' x) → ∀ a : ℝ,
      (∀ x,fundamentalGood N x → ∀ v∈F x,
        primeOldOriginalEnergy sector q hqN hs P'.epsilon_pos (P'.s+4) x (U x v)≤a*‖v‖^2) →
      (countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
          (K*((wideDistortion L R R)^(P'.s+4))^2)*a<1 →
      trace volume (fun x => (F x).starProjection)≤
        trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N)
          P'.epsilon_pos (by omega : 1≤P'.s+4) sector x).starProjection)+
          ∑ i,(CongruenceSubgroup.Gamma0 N).index*
            (3*ENNReal.ofReal (H/sectorFamilyC N (NeZero.pos N) sector S hS i)⁻¹)+
          ENNReal.ofReal H⁻¹ := by
  dsimp only
  let P' := AsymptoticReconstructedCount.parameters A P
  let U := normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P sector
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hobs⟩ :=
    exists_reconstructed_sector_original_observability A P D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hobs⟩ := hobs C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata F instF hmF hcF hF a henergy hsmall
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  have hHpos : 0<H := (by norm_num : (0:ℝ)<4).trans_le ((le_max_right _ _).trans hH)
  have ht : 1≤P'.s+4 := by omega
  let Vb := fun x => remaining (F x) (row A (NeZero.pos N) P sector (corner (boundary P'.ε)) x)
  have hbreg := survivor_regular A (NeZero.pos N) P sector F hmF hcF (corner (boundary P'.ε))
    (corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
      (boundary_measurable P'.ε)) (corner_covariant _) 1 (AsymptoticOrbitRegion.corner_norm_le _)
  have hbtrace := boundary_survivor_trace A (NeZero.pos N) P sector F hmF hcF P'.epsilon_pos
  let Vh := fun x => remaining (Vb x) (row A (NeZero.pos N) P sector
    (corner (AsymptoticHyperbolicArea.terminal H)) x)
  have hhreg := survivor_regular A (NeZero.pos N) P sector Vb hbreg.1 hbreg.2
    (corner (AsymptoticHyperbolicArea.terminal H))
    (corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
      (AsymptoticHyperbolicArea.terminal_measurable H)) (corner_covariant _) 1
    (AsymptoticOrbitRegion.corner_norm_le _)
  have hhtrace := terminal_survivor_trace A (NeZero.pos N) P sector Vb hbreg.1 hbreg.2 hHpos
  let heights := fun i => H/sectorFamilyC N (NeZero.pos N) sector S hS i
  let rows := sectorFamilySampled N (NeZero.pos N) sector H P'.epsilon_pos ht
  have hr := sectorFamilySampled_regular N (NeZero.pos N) sector H P'.epsilon_pos ht
  obtain ⟨M,hM,hbound⟩ := sectorFamilySampled_bounded N (NeZero.pos N) sector hH0 P'.epsilon_pos ht
  let Vt := fun x => remaining (Vh x)
    (reconstructedQuotientTail A (NeZero.pos N) P sector heights P'.epsilon_pos ht rows x)
  have htreg := reconstructedQuotientTail_survivor_regular A (NeZero.pos N) P sector heights
    P'.epsilon_pos ht rows (fun i => (hr i).1) (fun i => (hr i).2) M hM hbound Vh hhreg.1 hhreg.2
  have httrace := reconstructedQuotientTail_survivor_trace A (NeZero.pos N) P sector heights
    P'.epsilon_pos ht rows (fun i => (hr i).1) (fun i => (hr i).2) M hM hbound Vh hhreg.1 hhreg.2
    (fun i => div_pos hHpos (sectorFamilyC_pos N (NeZero.pos N) sector S hS i))
  let J := fun x => (sectorSampling N (NeZero.pos N) sector H P'.epsilon_pos ht x).comp (U x)
  have hU := normalizedRegularCountReconstruction_regular A (NeZero.pos N) P sector
  have hJ := sectorSampling_regular N (NeZero.pos N) sector H P'.epsilon_pos ht
  let MJ := samplingBound N (NeZero.pos N) H P'.ε (P'.s+4)*
    (8*coverBound N (NeZero.pos N)*(H+3)+5)
  have hMJ (x : ℍ) : ‖J x‖≤MJ := by
    apply (opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left
      (normalizedRegularAmbientCountReconstruction_norm_le A (NeZero.pos N) P sector x) (norm_nonneg _)).trans
    rw [mul_one]
    exact (sectorSampling_norm N (NeZero.pos N) sector H P'.epsilon_pos ht x).trans
      (fundamentalSampling_norm N (NeZero.pos N) H hH0 P'.epsilon_pos ht x)
  have htrace : trace volume (fun x => (Vt x).starProjection)≤
      trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N)
        P'.epsilon_pos ht sector x).starProjection) := by
    apply trace_le_of_injective_map_good N (NeZero.pos N) Vt _ htreg.1 htreg.2 J
      (matrix_comp_measurable _ _ hJ.1 hU.1) (covariant_comp _ _ hJ.2 hU.2) MJ hMJ
    · intro x hx v hv hz
      have hvF : v∈F x := hv.1.1.1
      have ho := hobs H hH hdata x hx v (hF x hvF) hv.1.1.2 hv.1.2 hv.2
      have he := henergy x hx v hvF
      have hn := sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)
      dsimp only at ho
      change sectorSampling N (NeZero.pos N) sector H P'.epsilon_pos ht x (U x v)=0 at hz
      rw [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero] at ho
      have hA : 0≤K*((wideDistortion ((2*generatorTransportConstant D₀*C)*(q:ℝ)^4)
        (Bg*(D*H+2+1)/min 1 (min P'.ε (1/4)))
        (Bg*(D*H+2+1)/min 1 (min P'.ε (1/4))))^(P'.s+4))^2 := by positivity
      have hh := ho.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he hA)
        (mul_nonneg (sq_nonneg (countReconstructionBound A P)) hn))
      have hz0 : ‖v‖^2=0 := by nlinarith [sq_nonneg ‖v‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz0)
    · intro x _hx v _hv
      exact sectorSampling_mem N (NeZero.pos N) sector H P'.epsilon_pos ht x (U x v)
  calc
    _ = trace volume (fun x => (Vb x).starProjection) := hbtrace
    _ ≤ trace volume (fun x => (Vh x).starProjection)+ENNReal.ofReal H⁻¹ := hhtrace
    _ ≤ (trace volume (fun x => (Vt x).starProjection)+
        ∑ i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (heights i)⁻¹))+
        ENNReal.ofReal H⁻¹ := _root_.add_le_add httrace le_rfl
    _ ≤ _ := _root_.add_le_add (_root_.add_le_add htrace le_rfl) le_rfl

#print axioms exists_reconstructed_original_energy_trace
end QuantitativeEulerEndpointPrepared
