module

public import QuantitativeArithmeticRetainedSourceTraceV1
public import QuantitativeArithmeticIsometricSourceV1
public import QuantitativeEulerEndpointSectorFreshLowTraceV1
public import QuantitativeEulerEndpointSectorPrimeStepV1
public import QuantitativeEulerEndpointNewChainIterationV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedImageTrace
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticSectorSigns QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open AsymptoticOrbitDiagonal QuantitativeEulerEndpointIsometricImage
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFilterExpression QuantitativeArithmeticRetainedRegularExtension
open QuantitativeArithmeticRetainedPreparedReconstruction QuantitativeArithmeticRetainedSourceObservation
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeEulerEndpointPrepared QuantitativeSpectralObservability
open QuantitativeEulerDensityGenerators QuantitativeSpectralFiniteReduction QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal MatrixGroups

variable {N Q : ℕ} {R : Finset ℕ} {hQ : 0<Q} (A : Certificate N R Q hQ)
    (P : Parameters A) (hR : ∀p∈R,p.Prime)

def image (hN : 0<N) (sector : Sector N) (x : ℍ) : Submodule ℂ Space :=
  imageSpace (regularAmbient A P hR hN sector x) (TerminalSpace A P x)
    (reconstructed_norm_on_terminal A P hR hN sector x)

instance image_complete (hN : 0<N) (sector : Sector N) (x : ℍ) :
    CompleteSpace (image A P hR hN sector x) := imageSpace_complete _ _ _

theorem ambient_gram (hN : 0<N) (sector : Sector N) (x : ℍ) :
    (regularAmbient A P hR hN sector x).adjoint.comp (regularAmbient A P hR hN sector x)=
      (TerminalSpace A P x).starProjection := by
  rw [regularAmbient_gram]
  exact (QuantitativeSpectralExceptionalRows.region_projection _ _).symm

theorem image_trace (hN : 0<N) (sector : Sector N) :
    trace volume (fun x => (image A P hR hN sector x).starProjection)=ENNReal.ofReal P.ε⁻¹ := by
  have hU := regularAmbient_regular A P hR hN sector
  have hm : ∀g k,Measurable (fun x => matrix (TerminalSpace A P x).starProjection g k) := by
    simp only [TerminalSpace,QuantitativeSpectralExceptionalRows.region_projection]
    exact corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
      (AsymptoticCertificateOperators.highStrip_measurable _)
  have hc : Covariant (fun x => (TerminalSpace A P x).starProjection) := by
    simp only [TerminalSpace,QuantitativeSpectralExceptionalRows.region_projection]
    exact corner_covariant _
  have he := QuantitativeEulerEndpointIsometricImage.image_trace volume AsymptoticRationalGroup.measurePreserving
    (regularAmbient A P hR hN sector) (TerminalSpace A P)
    (reconstructed_norm_on_terminal A P hR hN sector) hU.1 hU.2 hm hc
  change trace volume (fun x => (image A P hR hN sector x).starProjection)=_ at he
  rw [he]
  simp only [TerminalSpace,QuantitativeSpectralExceptionalRows.region_projection]
  rw [trace_corner _ (AsymptoticCertificateOperators.highStrip_measurable _)]
  exact AsymptoticHyperbolicArea.closed_terminal_area P.epsilon_pos

theorem image_subspace_trace_finite (hN : 0<N) (sector : Sector N)
    (V : ℍ → Submodule ℂ Space) [∀x,CompleteSpace (V x)]
    (hV : ∀x,V x ≤ image A P hR hN sector x) :
    trace volume (fun x => (V x).starProjection)<∞ := by
  apply (projection_trace_mono volume V _ hV).trans_lt
  rw [image_trace]
  exact ENNReal.ofReal_lt_top

/-- The mixed reconstruction image has the same coefficient-one source
trace bound. The pullback is a proved isometry, with no admissible-level
certificate or assumed inverse. -/
theorem exists_image_energy_trace [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
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
      (∀ x,F x≤ image A P hR (NeZero.pos N) sector x) → ∀ a : ℝ,
      (∀ x,fundamentalGood N x → ∀ v∈F x,
        primeOldOriginalEnergy sector q hqN hs P.epsilon_pos ((exponent A P+4)) x v≤a*‖v‖^2) →
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
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    QuantitativeArithmeticRetainedSourceTrace.exists_original_energy_trace A P hR D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hbound⟩ := hbound C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata V instV hmV hcV hV a henergy hsmall
  let U := regularAmbient A P hR (NeZero.pos N) sector
  let T := TerminalSpace A P
  let hi := reconstructed_norm_on_terminal A P hR (NeZero.pos N) sector
  let hg := ambient_gram A P hR (NeZero.pos N) sector
  let F := fun x => QuantitativeArithmeticIsometricSource.pullback (U x) (T x) (hi x) (hg x) (V x) (hV x)
  let : ∀x,CompleteSpace (F x) := fun x =>
    QuantitativeArithmeticIsometricSource.pullback_complete (U x) (T x) (hi x) (hg x) (V x) (hV x)
  have hU := regularAmbient_regular A P hR (NeZero.pos N) sector
  have hr := QuantitativeArithmeticIsometricSource.pullback_regular U T V hi hg hV hU.1 hU.2 hmV hcV
  have ht := QuantitativeArithmeticIsometricSource.pullback_trace U T V hi hg hV hU.1 hU.2 hmV hcV
    volume AsymptoticRationalGroup.measurePreserving
  rw [← ht]
  apply hbound H hH hdata F hr.1 hr.2
    (fun x => QuantitativeArithmeticIsometricSource.pullback_le (U x) (T x) (hi x) (hg x) (V x) (hV x))
    a _ hsmall
  intro x hx v hv
  have hf := QuantitativeArithmeticIsometricSource.pullback_forward (U x) (T x) (hi x) (hg x) (V x) (hV x) hv
  have he := henergy x hx _ hf.1
  simpa only [hf.2] using he

#print axioms ambient_gram
#print axioms image_trace
#print axioms image_subspace_trace_finite
#print axioms exists_image_energy_trace
end QuantitativeArithmeticRetainedImageTrace


namespace QuantitativeArithmeticRetainedFreshLow
open UpperHalfPlane MeasureTheory ContinuousLinearMap QuantitativeEulerDensityGenerators
open AsymptoticRegularTrace AsymptoticSectorSigns AsymptoticCornerKernel AsymptoticOrbitDiagonal
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedPreparedReconstruction QuantitativeArithmeticRetainedRegularExtension
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeArithmeticRetainedImageTrace QuantitativeEulerEndpointPrepared
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction QuantitativeNewGap
open QuantitativeSpectralExceptionalReconstructionTail QuantitativeSpectralCornerCutRow
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

/-- The low fresh-stack space inside the actual reconstructed image has
trace at most the literal sector trace plus all explicit geometric tails.
The baseline energy bound is retained as an input for a baseline spectral cut. -/
theorem exists_image_fresh_low_trace {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N]
    {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
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
      ∀ (V : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (V x)],
      (∀ g k,Measurable (fun x => matrix (V x).starProjection g k)) →
      Covariant (fun x => (V x).starProjection) →
      (∀ x,V x≤ image A P hR₀ (NeZero.pos N) sector x) → ∀ a : ℝ,
      (∀ x,fundamentalGood N x → ∀ y∈V x,
        ‖newBaselineDetector N sector hs P.epsilon_pos (exponent A P+4) x y‖^2≤a*‖y‖^2) →
      ∀ c : ℝ, 0<c →
      (bound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)*
          (K*((wideDistortion L R R)^(exponent A P+4))^2)*(a+c^2)<1 →
      trace volume (fun x =>
        (nextSpace (V x) (AsymptoticPolarIsometry.absolute
          (AsymptoticObservationStack.stack
            (freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V x))) c).starProjection)≤
        trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N)
          P.epsilon_pos (by omega : 1≤exponent A P+4) sector x).starProjection)+
          ∑ i,(CongruenceSubgroup.Gamma0 N).index*
            (3*ENNReal.ofReal (H/sectorFamilyC N (NeZero.pos N) sector S hS i)⁻¹)+
          ENNReal.ofReal H⁻¹ := by
  dsimp only
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_image_energy_trace A P hR₀ D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hbound⟩ := hbound C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata V instV hmV hcV hV a hbase c hc hsmall
  let Y := min P.ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  have hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*generatorTransportConstant D₀*C)*(q : ℝ)^4
  let hs := wideFreshRegion_compact L R R hZ
  let rows := freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V
  let T := fun x => AsymptoticPolarIsometry.absolute (AsymptoticObservationStack.stack (rows x))
  let V' := fun x => nextSpace (V x) (T x) c
  obtain ⟨M,hM⟩ := fresh_source_stack_bounded N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V
  have hr := fresh_source_rows_regular N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V hmV hcV
  have hT := stack_absolute_regular rows (fun i => (hr i).1) (fun i => (hr i).2) M hM
  have hMT (x : ℍ) : ‖T x‖≤M := by
    simpa only [T,AsymptoticPolarIsometry.absolute_opNorm] using hM x
  have hreg := (QuantitativeSpectralRegularCornerStep.step_regular V T hmV hcV hT.1 hT.2 M hMT c hc).1
  apply hbound H hH hdata V' hreg.1 hreg.2
    (fun x => (nextSpace_le (V x) (T x) c).trans (hV x)) (a+c^2) _ hsmall
  intro x hx v hv
  have hvV : v∈V x := nextSpace_le _ _ _ hv
  have hb := hbase x hx v hvV
  have he := nextSpace_energy (V x) (T x) c v hv
  have heq : AsymptoticObservationStack.stack (rows x) v=
      AsymptoticObservationStack.stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N)
        hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) i x) v := by
    ext i : 1
    exact fresh_source_rows_apply N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V x i v hvV
  change ‖AsymptoticPolarIsometry.absolute (AsymptoticObservationStack.stack (rows x)) v‖^2≤_ at he
  rw [←AsymptoticPolarIsometry.absolute_norm,heq] at he
  rw [primeOldOriginalEnergy_split]
  exact (_root_.add_le_add hb he).trans_eq (by ring)

#print axioms exists_image_fresh_low_trace
end QuantitativeArithmeticRetainedFreshLow


namespace QuantitativeArithmeticRetainedPrimeStep
open UpperHalfPlane MeasureTheory ContinuousLinearMap QuantitativeEulerDensityGenerators
open AsymptoticRegularTrace AsymptoticSectorSigns AsymptoticCornerKernel AsymptoticOrbitDiagonal
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedPreparedReconstruction QuantitativeArithmeticRetainedRegularExtension
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeArithmeticRetainedImageTrace QuantitativeEulerEndpointPrepared
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction QuantitativeNewGap
open QuantitativeSpectralExceptionalReconstructionTail QuantitativeSpectralCornerCutRow
open QuantitativeSpectralObservabilitySampling QuantitativeSpectralCoverUnweight
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

open QuantitativeArithmeticRetainedFreshLow AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticMixing

/-- Original one-prime trace contraction inside the normalized reconstructed
image, toward literal sector incidence plus geometric tails. Baseline energy,
fresh support and the explicit smallness threshold remain inputs for the
successive spectral-cut construction. No finite-trace premise remains. -/
theorem exists_image_prime_trace_loss {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N]
    {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
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
      ∀ (V : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (V x)],
      (∀ g k,Measurable (fun x => matrix (V x).starProjection g k)) →
      Covariant (fun x => (V x).starProjection) →
      (∀ x,V x≤ image A P hR₀ (NeZero.pos N) sector x) → ∀ a : ℝ,
      (∀ x,fundamentalGood N x → ∀ y∈V x,
        ‖newBaselineDetector N sector hs P.epsilon_pos (exponent A P+4) x y‖^2≤a*‖y‖^2) →
      (∀ x,Supported (integralGroup q) (V x).starProjection) →
      ∀ (c d : ℝ), 0<c → 0<d → d^2=c^2*(q:ℝ)⁻¹/(2*((q-1:ℕ):ℝ)) →
      (bound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)*
          (K*((wideDistortion L R R)^(exponent A P+4))^2)*(a+c^2)<1 →
      (q:ℝ)⁻¹*((trace volume (fun x => (V x).starProjection)).toReal-
        (sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤exponent A P+4)+H⁻¹))≤
      (trace volume (fun x => (V x).starProjection)).toReal-
        (trace volume (fun x =>
          (freshStepSource N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V d x).starProjection)).toReal := by
  dsimp only
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_image_fresh_low_trace A P hR₀ D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hbound⟩ := hbound C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata V instV hmV hcV hV a hbase hsupport c d hc hd hscale hsmall
  let Y := min P.ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  have hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*generatorTransportConstant D₀*C)*(q : ℝ)^4
  let hs := wideFreshRegion_compact L R R hZ
  let rows := freshSourceRows N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V
  have hHpos : 0<H := (by norm_num : (0:ℝ)<4).trans_le ((le_max_right _ _).trans hH)
  have ht : 1≤exponent A P+4 := by omega
  let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos ht+H⁻¹
  have hn : 0≤target := add_nonneg
    (sectorTraceTarget_nonneg N (NeZero.pos N) sector S hS hHpos.le P.epsilon_pos ht)
    (inv_nonneg.mpr hHpos.le)
  have he : ENNReal.ofReal target =
      trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N) P.epsilon_pos ht sector x).starProjection)+
        ∑ i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H/sectorFamilyC N (NeZero.pos N) sector S hS i)⁻¹)+
          ENNReal.ofReal H⁻¹ := by
    change ENNReal.ofReal (sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos ht+H⁻¹) = _
    rw [ENNReal.ofReal_add
      (sectorTraceTarget_nonneg N (NeZero.pos N) sector S hS hHpos.le P.epsilon_pos ht)
      (inv_nonneg.mpr hHpos.le),sectorTraceTarget_ofReal N (NeZero.pos N) sector S hS hHpos P.epsilon_pos ht]
  have hlow := hbound H hH hdata V hmV hcV hV a hbase c hc hsmall
  rw [←he] at hlow
  have hlowReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlow
  rw [ENNReal.toReal_ofReal hn] at hlowReal
  obtain ⟨M,hM⟩ := fresh_source_stack_bounded N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V
  have hr := fresh_source_rows_regular N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V hmV hcV
  have hf := image_subspace_trace_finite A P hR₀ (NeZero.pos N) sector V hV
  have hq : 1<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hcard : 0<Fintype.card (Fin (q-1)) := by
    simpa only [Fintype.card_fin] using Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  have htheta : (q:ℝ)⁻¹≤1 := (inv_le_one₀ (by linarith)).mpr hq.le
  have hh := fresh_step_of_low_trace volume AsymptoticRationalGroup.measurePreserving
    (integralGroup q) (primeLabels q) (primeLabels_separated q) hcard V hmV hcV rows
    (fun i => (hr i).1) (fun i => (hr i).2)
    (fresh_source_rows_supported N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V hsupport)
    (fresh_source_rows_fixed N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V)
    M hM hf hc hd (inv_pos.mpr (by linarith)) htheta
    (by simpa only [Fintype.card_fin] using hscale) target hlowReal
  have hfactor : (1-(q:ℝ)⁻¹)/(Fintype.card (Fin (q-1)):ℝ)=(q:ℝ)⁻¹ := by
    rw [Fintype.card_fin,Nat.cast_sub (Fact.out : q.Prime).one_lt.le,Nat.cast_one]
    field_simp [ne_of_gt (lt_trans zero_lt_one hq),ne_of_gt (sub_pos.mpr hq)]
  rw [hfactor] at hh
  exact hh

#print axioms exists_image_prime_trace_loss
/-- A whole block of fresh primes uses one observation region and one
small-energy threshold. Only the given averaged equation is cut at each step. -/
theorem exists_common_image_prime_loss {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N]
    {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (X : ℝ) (q : ℕ) [Fact q.Prime], D₀.Good q → (q:ℝ)≤X →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max P.ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*X^4
      let hs := wideFreshRegion_compact L R R hZ
      ∀ (V : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (V x)],
      (∀ g k,Measurable (fun x => matrix (V x).starProjection g k)) →
      Covariant (fun x => (V x).starProjection) →
      (∀ x,V x≤ image A P hR₀ (NeZero.pos N) sector x) → ∀ a : ℝ,
      (∀ x,fundamentalGood N x → ∀ y∈V x,
        ‖newBaselineDetector N sector hs P.epsilon_pos (exponent A P+4) x y‖^2≤a*‖y‖^2) →
      (∀ x,Supported (integralGroup q) (V x).starProjection) →
      ∀ (c d : ℝ), 0<c → 0<d → d^2=c^2*(q:ℝ)⁻¹/(2*((q-1:ℕ):ℝ)) →
      (bound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)*
          (K*((wideDistortion L R R)^(exponent A P+4))^2)*(a+c^2)<1 →
      (q:ℝ)⁻¹*((trace volume (fun x => (V x).starProjection)).toReal-
        (sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤exponent A P+4)+H⁻¹))≤
      (trace volume (fun x => (V x).starProjection)).toReal-
        (trace volume (fun x =>
          (freshStepSource N q (NeZero.pos N) hqN (sign sector.1) hs P.epsilon_pos (exponent A P+4) V d x).starProjection)).toReal := by
  dsimp only
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_image_prime_trace_loss A P hR₀ D₀ hN2 sector S hS
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

#print axioms exists_common_image_prime_loss
/-- Iteration uses only the averaged fresh-prime equations. The initial
small baseline energy remains explicit for the polynomial-filter construction. -/
theorem exists_image_chain_trace_bound
    {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ C : ℝ, B≤C → ∀ X H : ℝ, max P.ε⁻¹ 4≤H →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*X^4
      let hs := wideFreshRegion_compact L R R hZ
      let J := (bound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)*
        (K*((wideDistortion L R R)^(exponent A P+4))^2)
      let a := (2*(1+2*J))⁻¹
      let c := Real.sqrt a
      ∀ (U : ℍ → ClosedSubmodule ℂ Space),
      (∀ g k,Measurable (fun x => matrix (U x).toSubmodule.starProjection g k)) →
      Covariant (fun x => (U x).toSubmodule.starProjection) →
      (∀x,(U x).toSubmodule ≤ image A P hR₀ (NeZero.pos N) sector x) →
      (∀x,fundamentalGood N x → ∀v∈(U x).toSubmodule,
        ‖newBaselineDetector N sector hs P.epsilon_pos (exponent A P+4) x v‖^2≤a*‖v‖^2) →
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤exponent A P+4)+H⁻¹
      ∀ l : List (EligiblePrime N), l.Nodup →
      (∀ p∈l,D₀.Good p.val ∧ (p.val:ℝ)≤X) →
      (∀ p∈l,∀ x,Supported (integralGroup p.val) (U x).toSubmodule.starProjection) →
      cornerMass (primeChain N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) c U l)-target ≤
        (l.map primeFactor).prod*(cornerMass U-target) := by
  dsimp only
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_common_image_prime_loss A P hR₀ D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC X H hH hdata
  let Y := min P.ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  have hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*generatorTransportConstant D₀*C)*X^4
  let hs := wideFreshRegion_compact L R R hZ
  let J := (bound A P)^2*sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)*
    (K*((wideDistortion L R R)^(exponent A P+4))^2)
  let a := (2*(1+2*J))⁻¹
  let c := Real.sqrt a
  intro U hmU hcU hU hbase l hnodup hl hsU
  let : ∀x,CompleteSpace (U x).toSubmodule := fun x => (U x).isClosed.completeSpace_coe
  have hJ : 0≤J := mul_nonneg
    (mul_nonneg (sq_nonneg _) (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)))
    (mul_nonneg hK (sq_nonneg _))
  have h2J : 0≤2*J := mul_nonneg (by norm_num) hJ
  have ha : 0<a := baseline_threshold_pos (2*J) h2J
  have hc : 0<c := Real.sqrt_pos.mpr ha
  have hsmall : J*(a+c^2)<1 := by
    have he : c^2=a := Real.sq_sqrt ha.le
    rw [he]
    have hh := baseline_threshold_small (2*J) h2J
    change 2*J*a≤(1:ℝ)/2 at hh
    nlinarith only [hh]
  let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤exponent A P+4)+H⁻¹
  have hf := image_subspace_trace_finite A P hR₀ (NeZero.pos N) sector (fun x => (U x).toSubmodule) hU
  apply primeChain_trace_bound_of_step N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) c hc
    target (fun x => (U x).toSubmodule) U hmU hcU hf (fun _ => le_rfl) l hnodup hsU
  intro p hp V hmV hcV _hfV hV hsupport
  let : ∀x,CompleteSpace (V x).toSubmodule := fun x => (V x).isClosed.completeSpace_coe
  obtain ⟨_hqN,hstep⟩ := hbound C hBC X p.val (hl p hp).1 (hl p hp).2
  exact hstep H hH hdata (fun x => (V x).toSubmodule) hmV hcV
    (fun x => (hV x).trans (hU x)) a
    (fun x hx v hv => hbase x hx v (hV x hv)) hsupport
    c (primeCut c p.val) hc (primeCut_pos c hc p.val) (primeCut_sq c p.val) hsmall

#print axioms exists_image_chain_trace_bound

end QuantitativeArithmeticRetainedPrimeStep
