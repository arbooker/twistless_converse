module

public import QuantitativeArithmeticRetainedSourceObservationV1
public import QuantitativeEulerEndpointReconstructedEnergyTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedSourceTrace
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticSectorSigns QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open AsymptoticPolarIsometry AsymptoticCornerKernel AsymptoticOrbitDiagonal
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFilterExpression QuantitativeArithmeticRetainedRegularExtension
open QuantitativeArithmeticRetainedPreparedReconstruction QuantitativeArithmeticRetainedSourceObservation
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeEulerEndpointPrepared QuantitativeSpectralObservability
open QuantitativeSpectralExceptionalReconstructionTail
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal MatrixGroups

/-- Pulling an observation back through a regular contraction does not
increase its rank cost. This is independent of either reconstruction model. -/
theorem pullback_survivor
    (U T : ℍ → Space →L[ℂ] Space)
    (hUm : ∀g k,Measurable (fun x => matrix (U x) g k)) (hUc : Covariant U)
    (hUn : ∀x,‖U x‖≤1)
    (hTm : ∀g k,Measurable (fun x => matrix (T x) g k)) (hTc : Covariant T)
    (M : ℝ) (hTn : ∀x,‖T x‖≤M)
    (V : ℍ → Submodule ℂ Space) [∀x,CompleteSpace (V x)]
    (hVm : ∀g k,Measurable (fun x => matrix (V x).starProjection g k))
    (hVc : Covariant (fun x => (V x).starProjection)) :
    (∀g k,Measurable (fun x => matrix (remaining (V x) ((T x).comp (U x))).starProjection g k)) ∧
    Covariant (fun x => (remaining (V x) ((T x).comp (U x))).starProjection) ∧
    trace volume (fun x => (V x).starProjection)≤
      trace volume (fun x => (remaining (V x) ((T x).comp (U x))).starProjection)+
        trace volume (fun x => (T x).kerᗮ.starProjection) := by
  have hm := matrix_comp_measurable _ _ hTm hUm
  have hc := covariant_comp _ _ hTc hUc
  have hn (x : ℍ) : ‖(T x).comp (U x)‖≤M := by
    apply (opNorm_comp_le _ _).trans
    exact (mul_le_mul_of_nonneg_left (hUn x) (norm_nonneg _)).trans (by simpa using hTn x)
  have hr := remaining_regular V hVm hVc _ hm hc M hn
  refine ⟨hr.1,hr.2,?_⟩
  exact (source_trace_le_remaining_add_rank V hVm hVc _ hm hc M hn).trans
    (_root_.add_le_add le_rfl (composition_rank_le T U hTm hTc hUm hUc M hTn hUn))

variable {N Q : ℕ} {R : Finset ℕ} {hQ : 0<Q} (A : Certificate N R Q hQ)
    (P : Parameters A) (hR : ∀p∈R,p.Prime) (hN : 0<N) (e : AsymptoticSectorSigns.Sector N)

def mixedRow (T : ℍ → Space →L[ℂ] Space) (x : ℍ) :=
  (T x).comp (regularAmbient A P hR hN e x)

/-- Simultaneous regularity and geometric rank cost for an actual mixed
reconstruction corner. In particular the boundary costs zero area. -/
theorem corner_survivor
    (V : ℍ → Submodule ℂ Space) [∀x,CompleteSpace (V x)]
    (hmV : ∀g k,Measurable (fun x => matrix (V x).starProjection g k))
    (hcV : Covariant (fun x => (V x).starProjection))
    {s : Set ℍ} (hs : MeasurableSet s) :
    (∀g k,Measurable (fun x => matrix (remaining (V x) (mixedRow A P hR hN e (corner s) x)).starProjection g k)) ∧
    Covariant (fun x => (remaining (V x) (mixedRow A P hR hN e (corner s) x)).starProjection) ∧
    trace volume (fun x => (V x).starProjection)≤
      trace volume (fun x => (remaining (V x) (mixedRow A P hR hN e (corner s) x)).starProjection)+volume s := by
  have hU := regularAmbient_regular A P hR hN e
  have hm := matrix_comp_measurable _ _
    (corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable) hs) hU.1
  have hc := covariant_comp _ _ (corner_covariant s) hU.2
  have hn (x : ℍ) : ‖mixedRow A P hR hN e (corner s) x‖≤1 :=
    (opNorm_comp_le _ _).trans ((mul_le_mul (AsymptoticOrbitRegion.corner_norm_le s x)
      (regularAmbient_norm A P hR hN e x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hr := remaining_regular V hmV hcV _ hm hc 1 hn
  refine ⟨hr.1,hr.2,?_⟩
  exact (source_trace_le_remaining_add_rank V hmV hcV _ hm hc 1 hn).trans
    (_root_.add_le_add le_rfl (QuantitativeSpectralExceptionalRows.omitted_rank_le_area volume
      AsymptoticRationalGroup.measurePreserving hs _ hU.1 hU.2 1 (regularAmbient_norm A P hR hN e)))

variable {I : Type*} [Fintype I]

def mixedQuotientTail (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (B : ℍ → I → Space →L[ℂ] Space) (x : ℍ) :=
  (quotientTailStack N H hε ht B x).comp (regularAmbient A P hR hN e x)

theorem quotient_survivor (H : I → ℝ) (hH : ∀i,0<H i)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (B : ℍ → I → Space →L[ℂ] Space)
    (hm : ∀i g k,Measurable (fun x => matrix (B x i) g k)) (hc : ∀i,Covariant (fun x => B x i))
    (M : I → ℝ) (hM : ∀i,0≤M i) (hb : ∀x i,‖B x i‖≤M i)
    (V : ℍ → Submodule ℂ Space) [∀x,CompleteSpace (V x)]
    (hmV : ∀g k,Measurable (fun x => matrix (V x).starProjection g k))
    (hcV : Covariant (fun x => (V x).starProjection)) :
    (∀g k,Measurable (fun x => matrix (remaining (V x) (mixedQuotientTail A P hR hN e H hε ht B x)).starProjection g k)) ∧
    Covariant (fun x => (remaining (V x) (mixedQuotientTail A P hR hN e H hε ht B x)).starProjection) ∧
    trace volume (fun x => (V x).starProjection)≤
      trace volume (fun x => (remaining (V x) (mixedQuotientTail A P hR hN e H hε ht B x)).starProjection)+
        ∑i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H i)⁻¹) := by
  obtain ⟨K,_hK,hbound,hr⟩ := quotientTailStack_absolute_regular N hN H hε ht B hm hc M hM hb
  have hU := regularAmbient_regular A P hR hN e
  have hh := pullback_survivor (regularAmbient A P hR hN e)
    (fun x => absolute (quotientTailStack N H hε ht B x)) hU.1 hU.2
    (regularAmbient_norm A P hR hN e) hr.1 hr.2 K hbound V hmV hcV
  simp only [remaining,absolute_comp_ker,absolute_ker] at hh
  refine ⟨hh.1,hh.2.1,?_⟩
  exact hh.2.2.trans (_root_.add_le_add le_rfl
    (quotientTailStack_source_rank N hN H hH hε ht B hm hc M hM hb))

open QuantitativeEulerDensityGenerators QuantitativeSpectralFiniteReduction QuantitativeNewGap

/-- Original-energy trace bound on the actual normalized terminal source.
All boundary, upper-height, and combined old/sign tails are removed with
proved geometric rank costs. The leading sector trace has coefficient ONE.
No band support of the reconstructed vector, or small lower tail, is assumed. -/
theorem exists_original_energy_trace [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let U := regularAmbient A P hR (NeZero.pos N) sector
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], D₀.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max P.ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*(q : ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      ∀ (F : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (F x)],
      (∀ g k,Measurable (fun x => matrix (F x).starProjection g k)) →
      Covariant (fun x => (F x).starProjection) →
      (∀ x,F x≤TerminalSpace A P x) → ∀ a : ℝ,
      (∀ x,fundamentalGood N x → ∀ v∈F x,
        primeOldOriginalEnergy sector q hqN hs P.epsilon_pos ((exponent A P+4)) x (U x v)≤a*‖v‖^2) →
      (bound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P.ε ((exponent A P+4))*
          (K*((wideDistortion L R R)^((exponent A P+4)))^2)*a<1 →
      trace volume (fun x => (F x).starProjection)≤
        trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N)
          P.epsilon_pos (by omega : 1≤(exponent A P+4)) sector x).starProjection)+
          ∑ i,(CongruenceSubgroup.Gamma0 N).index*
            (3*ENNReal.ofReal (H/sectorFamilyC N (NeZero.pos N) sector S hS i)⁻¹)+
          ENNReal.ofReal H⁻¹ := by
  dsimp only
  let U := regularAmbient A P hR (NeZero.pos N) sector
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hobs⟩ :=
    exists_original_observability A P hR (NeZero.pos N) D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hobs⟩ := hobs C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata F instF hmF hcF hF a henergy hsmall
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  have hHpos : 0<H := (by norm_num : (0:ℝ)<4).trans_le ((le_max_right _ _).trans hH)
  have ht : 1≤(exponent A P+4) := by omega
  let Vb := fun x => remaining (F x) (mixedRow A P hR (NeZero.pos N) sector (corner (boundary P.ε)) x)
  have hb := corner_survivor A P hR (NeZero.pos N) sector F hmF hcF (boundary_measurable P.ε)
  have hbtrace : trace volume (fun x => (F x).starProjection)≤
      trace volume (fun x => (Vb x).starProjection) := by
    simpa only [boundary_area P.epsilon_pos,add_zero] using hb.2.2
  let Vh := fun x => remaining (Vb x) (mixedRow A P hR (NeZero.pos N) sector
    (corner (AsymptoticHyperbolicArea.terminal H)) x)
  have hh := corner_survivor A P hR (NeZero.pos N) sector Vb hb.1 hb.2.1
    (AsymptoticHyperbolicArea.terminal_measurable H)
  have hhtrace : trace volume (fun x => (Vb x).starProjection)≤
      trace volume (fun x => (Vh x).starProjection)+ENNReal.ofReal H⁻¹ := by
    simpa only [AsymptoticHyperbolicArea.terminal_area hHpos] using hh.2.2
  let heights := fun i => H/sectorFamilyC N (NeZero.pos N) sector S hS i
  let rows := sectorFamilySampled N (NeZero.pos N) sector H P.epsilon_pos ht
  have hr := sectorFamilySampled_regular N (NeZero.pos N) sector H P.epsilon_pos ht
  obtain ⟨M,hM,hbound⟩ := sectorFamilySampled_bounded N (NeZero.pos N) sector hH0 P.epsilon_pos ht
  let Vt := fun x => remaining (Vh x)
    (mixedQuotientTail A P hR (NeZero.pos N) sector heights P.epsilon_pos ht rows x)
  have htail := quotient_survivor A P hR (NeZero.pos N) sector heights
    (fun i => div_pos hHpos (sectorFamilyC_pos N (NeZero.pos N) sector S hS i))
    P.epsilon_pos ht rows (fun i => (hr i).1) (fun i => (hr i).2) M hM hbound Vh hh.1 hh.2.1
  let J := fun x => (sectorSampling N (NeZero.pos N) sector H P.epsilon_pos ht x).comp (U x)
  have hU := regularAmbient_regular A P hR (NeZero.pos N) sector
  have hJ := sectorSampling_regular N (NeZero.pos N) sector H P.epsilon_pos ht
  let MJ := samplingBound N (NeZero.pos N) H P.ε ((exponent A P+4))*
    (8*coverBound N (NeZero.pos N)*(H+3)+5)
  have hMJ (x : ℍ) : ‖J x‖≤MJ := by
    apply (opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left
      (regularAmbient_norm A P hR (NeZero.pos N) sector x) (norm_nonneg _)).trans
    rw [mul_one]
    exact (sectorSampling_norm N (NeZero.pos N) sector H P.epsilon_pos ht x).trans
      (fundamentalSampling_norm N (NeZero.pos N) H hH0 P.epsilon_pos ht x)
  have htrace : trace volume (fun x => (Vt x).starProjection)≤
      trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N)
        P.epsilon_pos ht sector x).starProjection) := by
    apply trace_le_of_injective_map_good N (NeZero.pos N) Vt _ htail.1 htail.2.1 J
      (matrix_comp_measurable _ _ hJ.1 hU.1) (covariant_comp _ _ hJ.2 hU.2) MJ hMJ
    · intro x hx v hv hz
      have hvF : v∈F x := hv.1.1.1
      have ho := hobs H hH hdata x hx v (hF x hvF) hv.1.1.2 hv.1.2 hv.2
      have he := henergy x hx v hvF
      have hn := sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P.ε ((exponent A P+4))
      dsimp only at ho
      change sectorSampling N (NeZero.pos N) sector H P.epsilon_pos ht x (U x v)=0 at hz
      rw [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero] at ho
      have hA : 0≤K*((wideDistortion ((2*generatorTransportConstant D₀*C)*(q:ℝ)^4)
        (Bg*(D*H+2+1)/min 1 (min P.ε (1/4)))
        (Bg*(D*H+2+1)/min 1 (min P.ε (1/4))))^((exponent A P+4)))^2 := by positivity
      have hh := ho.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he hA)
        (mul_nonneg (sq_nonneg (bound A P)) hn))
      have hz0 : ‖v‖^2=0 := by nlinarith [sq_nonneg ‖v‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz0)
    · intro x _hx v _hv
      exact sectorSampling_mem N (NeZero.pos N) sector H P.epsilon_pos ht x (U x v)
  calc
    _ ≤ trace volume (fun x => (Vb x).starProjection) := hbtrace
    _ ≤ trace volume (fun x => (Vh x).starProjection)+ENNReal.ofReal H⁻¹ := hhtrace
    _ ≤ (trace volume (fun x => (Vt x).starProjection)+
        ∑ i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (heights i)⁻¹))+
        ENNReal.ofReal H⁻¹ := _root_.add_le_add htail.2.2 le_rfl
    _ ≤ _ := _root_.add_le_add (_root_.add_le_add htrace le_rfl) le_rfl

#print axioms exists_original_energy_trace
#print axioms pullback_survivor
#print axioms corner_survivor
#print axioms quotient_survivor
end QuantitativeArithmeticRetainedSourceTrace
