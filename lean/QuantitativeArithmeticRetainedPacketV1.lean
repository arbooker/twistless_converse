module

public import QuantitativeArithmeticRetainedIntegralSupportV1
public import QuantitativeEulerEndpointIsometricChainV1
public import QuantitativeEulerEndpointPacketChainV1
public import QuantitativeEulerEndpointPacketRegularV1
public import QuantitativeSpectralRegularPacketV1
public import QuantitativeEulerEndpointNormalizedCombinedPacketV1
public import QuantitativeEulerEndpointNormalizedGramExpansionV1
public import QuantitativeArithmeticRetainedTerminalAlgebraV1
public import QuantitativeEulerEndpointBlockNormalizationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedPacket
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticSectorSigns
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedRegularExtension QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedImageTrace QuantitativeArithmeticRetainedFilterExpression
open QuantitativeArithmeticRetainedIntegralSupport QuantitativeEulerEndpointPrepared
open QuantitativeArithmeticRetainedSourceObservation
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeSpectralCornerCutRow QuantitativeSpectralRegularCornerStep QuantitativeSpectralDeflationChain
open QuantitativeEulerEndpointIsometricImage AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

local instance closed_complete (F : ClosedSubmodule ℂ Space) : CompleteSpace F.toSubmodule :=
  F.isClosed.completeSpace_coe

private theorem extended_source_identity
    {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V I : G →L[ℂ] H) (T : H →L[ℂ] H)
    (hi : I.adjoint.comp I=1) (hp : I.comp I.adjoint=T) :
    (V.comp I.adjoint).comp T=V.comp I.adjoint := by
  have hright : I.adjoint.comp (I.comp I.adjoint)=I.adjoint := by
    rw [←comp_assoc,hi]
    exact id_comp _
  rw [←hp,comp_assoc,hright]

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) (l : List (EligiblePrime N))
local notation "U" => regularAmbient A P hR₀ (NeZero.pos N) sector
local notation "Dbase" => newBaselineDetector N sector hs P.epsilon_pos (exponent A P+4)

def rows : ℕ → ℍ → Space →L[ℂ] Space
  | 0,x => Dbase x*U x
  | j+1,x => packetSequence N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) l j x*U x

def rowBound : ℕ → ℝ
  | 0 => ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : NewBaselineIndex N => Space)).symm.toContinuousLinearMap‖ *
      ∑ i,newBaselineRowBound N sector hs P.epsilon_pos (exponent A P+4) i
  | j+1 => packetSequenceBound N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) l j

theorem rows_regular (i : ℕ) :
    (∀g k,Measurable (fun x => matrix (rows A P hR₀ sector hs l i x) g k)) ∧
      Covariant (rows A P hR₀ sector hs l i) := by
  have hu := regularAmbient_regular A P hR₀ (NeZero.pos N) sector
  cases i with
  | zero =>
    obtain ⟨M,_hM,_hn,hm,hc⟩ := newBaselineDetector_regular N sector hs P.epsilon_pos (exponent A P+4)
    exact ⟨matrix_comp_measurable _ _ hm hu.1,covariant_comp _ _ hc hu.2⟩
  | succ i =>
    have hb := packet_sequence_regular N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) l i
    exact ⟨matrix_comp_measurable _ _ hb.1 hu.1,covariant_comp _ _ hb.2 hu.2⟩

theorem rows_norm (i : ℕ) (x : ℍ) : ‖rows A P hR₀ sector hs l i x‖≤rowBound A P sector hs l i := by
  have hu := regularAmbient_norm A P hR₀ (NeZero.pos N) sector x
  cases i with
  | zero =>
    apply (norm_mul_le_of_le (le_refl _) hu).trans
    rw [mul_one,newBaselineDetector,AsymptoticPolarIsometry.absolute_opNorm]
    exact AsymptoticObservationStack.stack_norm_le _ _
      (newBaselineRowBound_nonneg N sector hs P.epsilon_pos (exponent A P+4))
      (newBaselineRows_norm N sector hs P.epsilon_pos (exponent A P+4) x)
  | succ i =>
    exact (norm_mul_le_of_le
      (packet_sequence_norm N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) l i x) hu).trans_eq (mul_one _)

def sourcePacket (F : ℍ → ClosedSubmodule ℂ Space) (c : ℝ) (x : ℍ) : ClosedSubmodule ℂ Space :=
  chain (F x) (fun i => rows A P hR₀ sector hs l i x) c (l.length+1)

theorem sourcePacket_le (F : ℍ → ClosedSubmodule ℂ Space) (c : ℝ) (x : ℍ) :
    sourcePacket A P hR₀ sector hs l F c x≤F x := chain_antitone _ _ _ (Nat.zero_le _)

theorem sourcePacket_regular (F : ℍ → ClosedSubmodule ℂ Space)
    (hmF : ∀g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k))
    (hcF : Covariant (fun x => (F x).toSubmodule.starProjection)) (c : ℝ) (hc : 0<c) :
    (∀g k,Measurable (fun x => matrix (sourcePacket A P hR₀ sector hs l F c x).toSubmodule.starProjection g k)) ∧
      Covariant (fun x => (sourcePacket A P hR₀ sector hs l F c x).toSubmodule.starProjection) :=
  QuantitativeSpectralRegularPacket.projection_regular F (rows A P hR₀ sector hs l) c hmF hcF
    (fun i => (rows_regular A P hR₀ sector hs l i).1)
    (fun i => (rows_regular A P hR₀ sector hs l i).2) (rowBound A P sector hs l)
    (rows_norm A P hR₀ sector hs l) hc (l.length+1)

variable (F : ℍ → ClosedSubmodule ℂ Space)
    (hF : ∀x,(F x).toSubmodule≤TerminalSpace A P x)

def sourceImage (x : ℍ) : ClosedSubmodule ℂ Space :=
  closedImage (U x) (F x) (fun v hv => reconstructed_norm_on_terminal A P hR₀ (NeZero.pos N) sector x v (hF x hv))

def baseline (c : ℝ) (x : ℍ) : ClosedSubmodule ℂ Space := step (sourceImage A P hR₀ sector F hF x) (Dbase x) c

theorem sourceImage_le (x : ℍ) :
    (sourceImage A P hR₀ sector F hF x).toSubmodule ≤ image A P hR₀ (NeZero.pos N) sector x := by
  rintro v ⟨w,hw⟩
  exact ⟨⟨w,hF x w.property⟩,hw⟩

theorem sourceImage_regular
    (hmF : ∀g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k))
    (hcF : Covariant (fun x => (F x).toSubmodule.starProjection)) :
    (∀g k,Measurable (fun x => matrix (sourceImage A P hR₀ sector F hF x).toSubmodule.starProjection g k)) ∧
      Covariant (fun x => (sourceImage A P hR₀ sector F hF x).toSubmodule.starProjection) := by
  have hu := regularAmbient_regular A P hR₀ (NeZero.pos N) sector
  simp only [sourceImage,closedImage,image_projection]
  exact ⟨matrix_comp_measurable _ _ hu.1 (matrix_comp_measurable _ _ hmF (matrix_adjoint_measurable _ hu.1)),
    covariant_comp _ _ hu.2 (covariant_comp _ _ hcF (covariant_adjoint _ hu.2))⟩

theorem baseline_regular
    (hmF : ∀g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k))
    (hcF : Covariant (fun x => (F x).toSubmodule.starProjection)) (c : ℝ) (hc : 0<c) :
    (∀g k,Measurable (fun x => matrix (baseline A P hR₀ sector hs F hF c x).toSubmodule.starProjection g k)) ∧
      Covariant (fun x => (baseline A P hR₀ sector hs F hF c x).toSubmodule.starProjection) := by
  have hr := sourceImage_regular A P hR₀ sector F hF hmF hcF
  obtain ⟨M,_hM,hM,hm,hcov⟩ := newBaselineDetector_regular N sector hs P.epsilon_pos (exponent A P+4)
  exact (step_regular _ _ hr.1 hr.2 hm hcov M hM c hc).1

theorem baseline_supported (q : ℕ) [Fact q.Prime]
    (hqN : ¬q∣N) (hqQ : ¬q∣Q) (hqR : ∀p∈R₀,¬q∣p)
    (hqfixed : ∀b : UnitResidue N,¬q∣(primeLift N b).q)
    (hsF : ∀x,Supported (integralGroup q) (F x).toSubmodule.starProjection)
    (c : ℝ) (hc : 0<c) (x : ℍ) :
    Supported (integralGroup q) (baseline A P hR₀ sector hs F hF c x).toSubmodule.starProjection := by
  apply (step_supported _ _ _ _
    (newBaselineDetector_supported N sector q hqN hqfixed hs P.epsilon_pos (exponent A P+4) x) c hc).1
  simp only [sourceImage,closedImage,image_projection]
  have hu := normalized_supported q A hR₀ (NeZero.pos N) hqN hqQ hqR P sector x
  exact supported_comp _ _ _ hu (supported_comp _ _ _ (hsF x) (supported_adjoint _ _ hu))

theorem packet_image (c : ℝ) (hc : 0<c) (x : ℍ) :
    closedImage (U x) (sourcePacket A P hR₀ sector hs l F c x)
      (fun v hv => reconstructed_norm_on_terminal A P hR₀ (NeZero.pos N) sector x v
        (hF x (sourcePacket_le A P hR₀ sector hs l F c x hv)))=
      primeChain N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) c
        (baseline A P hR₀ sector hs F hF c) l x := by
  let B : ℕ → Space →L[ℂ] Space := fun i => match i with
    | 0 => Dbase x
    | j+1 => packetSequence N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) l j x
  have he : (fun i => rows A P hR₀ sector hs l i x)=fun i => B i*U x := by
    funext i
    cases i <;> rfl
  unfold sourcePacket
  simp only [he]
  rw [closed_image_chain (U x) (F x)
    (fun v hv => reconstructed_norm_on_terminal A P hR₀ (NeZero.pos N) sector x v (hF x hv)) B c (l.length+1)]
  dsimp only [B]
  refine (chain_prepend (sourceImage A P hR₀ sector F hF x) (Dbase x)
    (fun i => packetSequence N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos
      (exponent A P+4) l i x) c l.length).trans ?_
  exact (primeChain_eq_packet N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) c hc
    (baseline A P hR₀ sector hs F hF c) l x).symm

theorem packet_mass
    (hmF : ∀g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k))
    (hcF : Covariant (fun x => (F x).toSubmodule.starProjection)) (c : ℝ) (hc : 0<c) :
    cornerMass (sourcePacket A P hR₀ sector hs l F c)=
      cornerMass (primeChain N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) c
        (baseline A P hR₀ sector hs F hF c) l) := by
  have hu := regularAmbient_regular A P hR₀ (NeZero.pos N) sector
  have hr := sourcePacket_regular A P hR₀ sector hs l F hmF hcF c hc
  have ht := image_trace volume AsymptoticRationalGroup.measurePreserving U
    (fun x => (sourcePacket A P hR₀ sector hs l F c x).toSubmodule)
    (fun x v hv => reconstructed_norm_on_terminal A P hR₀ (NeZero.pos N) sector x v
      (hF x (sourcePacket_le A P hR₀ sector hs l F c x hv))) hu.1 hu.2 hr.1 hr.2
  have he := fun x => congrArg (fun V : ClosedSubmodule ℂ Space => V.toSubmodule.starProjection)
    (packet_image A P hR₀ sector hs l F hF c hc x)
  change trace volume (fun x => (closedImage (U x) _ _).toSubmodule.starProjection)=_ at ht
  simp only [he] at ht
  exact congrArg ENNReal.toReal ht.symm

theorem baseline_mass_le
    (hmF : ∀g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k))
    (hcF : Covariant (fun x => (F x).toSubmodule.starProjection)) (c : ℝ) :
    cornerMass (baseline A P hR₀ sector hs F hF c)≤cornerMass F := by
  have hu := regularAmbient_regular A P hR₀ (NeZero.pos N) sector
  have ht := image_trace volume AsymptoticRationalGroup.measurePreserving U (fun x => (F x).toSubmodule)
    (fun x v hv => reconstructed_norm_on_terminal A P hR₀ (NeZero.pos N) sector x v (hF x hv)) hu.1 hu.2 hmF hcF
  have hm := projection_trace_mono volume (fun x => (baseline A P hR₀ sector hs F hF c x).toSubmodule)
    (fun x => (sourceImage A P hR₀ sector F hF x).toSubmodule) (fun _ => nextSpace_le _ _ _)
  have hf := image_subspace_trace_finite A P hR₀ (NeZero.pos N) sector
    (fun x => (sourceImage A P hR₀ sector F hF x).toSubmodule) (sourceImage_le A P hR₀ sector F hF)
  exact (ENNReal.toReal_mono hf.ne hm).trans_eq (congrArg ENNReal.toReal ht)

/-- The original averaged rows form one fixed packet on every terminal
subspace, with the full mixed reconstruction and no baseline-energy premise. -/
theorem exists_packet_contraction
    {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (hex : baselineDenominators N⊆excluded)
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
      ∀ (F : ℍ → ClosedSubmodule ℂ Space),
      (∀g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k)) →
      Covariant (fun x => (F x).toSubmodule.starProjection) →
      (∀x,(F x).toSubmodule≤TerminalSpace A P x) →
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤exponent A P+4)+H⁻¹
      ∀ l : List (EligiblePrime N), l.Nodup →
      (∀ p∈l,D₀.Good p.val ∧ (p.val:ℝ)≤X ∧ ¬p.val∣Q ∧ ∀r∈R₀,¬p.val∣r) →
      (∀ p∈l,∀ x,Supported (integralGroup p.val) (F x).toSubmodule.starProjection) →
      cornerMass (sourcePacket A P hR₀ sector hs l F c)-target ≤
        (l.map primeFactor).prod*(cornerMass F-target) := by
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    QuantitativeArithmeticRetainedPrimeStep.exists_image_chain_trace_bound A P hR₀ D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC X H hH hdata Y R hZ L hs J a c F hmF hcF hF target l hnodup hl hsF
  have hJ : 0≤J := mul_nonneg
    (mul_nonneg (sq_nonneg _) (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)))
    (mul_nonneg hK (sq_nonneg _))
  have ha : 0<a := baseline_threshold_pos (2*J) (mul_nonneg (by norm_num) hJ)
  have hc : 0<c := Real.sqrt_pos.mpr ha
  have hr := baseline_regular A P hR₀ sector hs F hF hmF hcF c hc
  have hb := hbound C hBC X H hH hdata (baseline A P hR₀ sector hs F hF c) hr.1 hr.2
    (fun x => (nextSpace_le _ _ _).trans (sourceImage_le A P hR₀ sector F hF x))
    (fun x _ v hv => by
      have hc2 : c^2=a := Real.sq_sqrt ha.le
      exact (nextSpace_energy _ _ c v hv).trans_eq
        (congrArg (fun r : ℝ => r*‖v‖^2) hc2))
    l hnodup (fun p hp => ⟨(hl p hp).1,(hl p hp).2.1⟩)
    (fun p hp x => baseline_supported A P hR₀ sector hs F hF p.val p.property.2
      (hl p hp).2.2.1 (hl p hp).2.2.2
      (good_prime_avoids_baseline D₀ hex p.val (hl p hp).1) (hsF p hp) c hc x)
  rw [packet_mass A P hR₀ sector hs l F hF hmF hcF c hc]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (baseline_mass_le A P hR₀ sector hs F hF hmF hcF c) target) (primeProduct_nonneg l))

set_option backward.isDefEq.respectTransparency true in
/-- The packet rows are genuinely supported on the full terminal source. -/
theorem rows_source (i : ℕ) (x : ℍ) :
    rows A P hR₀ sector hs l i x*(TerminalSpace A P x).starProjection=rows A P hR₀ sector hs l i x := by
  let I := (TerminalSpace A P x).subtypeL
  have hi : I.adjoint.comp I=1 := AsymptoticOrbitRegion.adjoint_comp_subtype _ x
  have hp : I.comp I.adjoint=(TerminalSpace A P x).starProjection := by
    rw [Submodule.adjoint_subtypeL]
    rfl
  have hu : U x*(TerminalSpace A P x).starProjection=U x := by
    unfold regularAmbient
    exact extended_source_identity _ I _ hi hp
  cases i <;> simp only [rows,mul_assoc,hu]

/-- Square-root detectors cancel from the polynomial energy: the input
is a finite Gram sum of the original fixed rows and averaged prime twists. -/
theorem gram_expansion (x : ℍ) :
    (∑ i : Fin (l.length+1),star (rows A P hR₀ sector hs l i x)*rows A P hR₀ sector hs l i x)=
      (∑ i : NewBaselineIndex N,star (newBaselineRows N sector hs P.epsilon_pos (exponent A P+4) x i*U x)*
        (newBaselineRows N sector hs P.epsilon_pos (exponent A P+4) x i*U x))+
      ∑ i : Fin l.length,star (packetSequence N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) l i x*U x)*
        (packetSequence N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) l i x*U x) := by
  rw [Fin.sum_univ_succ]
  change star (Dbase x*U x)*(Dbase x*U x)+_= _
  rw [newBaselineDetector,absolute_stack_composed_gram]
  rfl

open QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeEulerEndpointRegularBase
open QuantitativeSpectralSourceGram
variable (C : ℕ → ℝ) (hC : ∀ i x,‖rows A P hR₀ sector hs l i x‖≤C i)
local notation "r" => QuantitativeEulerEndpointBlockNormalization.factor C (l.length+1)

def scaledRows (i : ℕ) (x : Base) : Space →L[ℂ] Space :=
  ((r:ℝ):ℂ) • rows A P hR₀ sector hs l i x

theorem scaledRows_regular (i : ℕ) :
    (∀g k,Measurable (fun x => matrix (scaledRows A P hR₀ sector hs l C i x) g k)) ∧
      Covariant (scaledRows A P hR₀ sector hs l C i) := by
  have hr := rows_regular A P hR₀ sector hs l i
  exact ⟨matrix_smul_measurable _ _ hr.1,covariant_smul _ _ hr.2⟩

include hC in
theorem scaledRows_norm (i : ℕ) (x : Base) :
    ‖scaledRows A P hR₀ sector hs l C i x‖≤r*C i := by
  rw [scaledRows,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (QuantitativeEulerEndpointBlockNormalization.factor_pos _ _)]
  exact mul_le_mul_of_nonneg_left (hC i x)
    (QuantitativeEulerEndpointBlockNormalization.factor_pos _ _).le

theorem scaledRows_source (i : ℕ) (x : Base) :
    scaledRows A P hR₀ sector hs l C i x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=
      scaledRows A P hR₀ sector hs l C i x := by
  have he : AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=(TerminalSpace A P x).starProjection :=
    (QuantitativeSpectralExceptionalRows.region_projection _ x).symm
  rw [scaledRows,smul_mul_assoc,he,rows_source]

/-- The actual normalized packet Gram in the finite terminal algebra. -/
def gram : Algebra A P := ∑ i : Fin (l.length+1),
  gramElement action_measurable (terminalRegion A P) (terminal_measurable A P)
    (scaledRows A P hR₀ sector hs l C i)
    (scaledRows_regular A P hR₀ sector hs l C i).1
    (scaledRows_regular A P hR₀ sector hs l C i).2
    (r*C i) (scaledRows_norm A P hR₀ sector hs l C hC i)
    (scaledRows_source A P hR₀ sector hs l C i)

theorem gram_order : 0≤gram A P hR₀ sector hs l C hC ∧ gram A P hR₀ sector hs l C hC≤1 := by
  have hg : 0≤gram A P hR₀ sector hs l C hC :=
    Finset.sum_nonneg (fun _ _ => gramElement_nonneg _ _ _ _ _ _ _ _ _)
  refine ⟨hg,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hg).mp ?_⟩
  apply (norm_sum_le _ _).trans
  exact (Finset.sum_le_sum (fun _ _ => gramElement_norm_le _ _ _ _ _ _ _ _ _)).trans
    (QuantitativeEulerEndpointBlockNormalization.normalized_square_sum _ _)

theorem rep_gram (x : Base) :
    rep A P (gram A P hR₀ sector hs l C hC) x=
      ∑ i : Fin (l.length+1),star (scaledRows A P hR₀ sector hs l C i x)*scaledRows A P hR₀ sector hs l C i x := by
  simp only [gram,map_sum,Finset.sum_apply]
  rfl

#print axioms rows_source
#print axioms gram_expansion
#print axioms gram_order
#print axioms rep_gram

#print axioms rows_regular
#print axioms rows_norm
#print axioms packet_image
#print axioms packet_mass
#print axioms exists_packet_contraction
end QuantitativeArithmeticRetainedPacket
