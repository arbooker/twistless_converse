module

public import QuantitativeArithmeticRetainedImageStepV1
public import QuantitativeEulerEndpointNormalizedSupportV1
public import QuantitativeEulerEndpointNewBaselineRegularV1
public import QuantitativeEulerEndpointBaselineExclusionsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedIntegralSupport
open UpperHalfPlane ContinuousLinearMap MeasureTheory Filter
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedRegularOperators QuantitativeArithmeticRetainedRegularExtension
open QuantitativeArithmeticRetainedDilationBranches
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticRationalBranches
open AsymptoticCertificateBranches (residues)
open AsymptoticFiniteBranch (regular)
open AsymptoticRegularFoldedLow (Space)
open QuantitativeArithmeticRetainedFilterExpression QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedRegularNormalization QuantitativeHolomorphic AsymptoticSectorSigns
open QuantitativeArithmeticRetainedSectorReconstruction
open QuantitativeArithmeticRetainedCylinderNormalization (bound gramLower gramLower_pos gramLower_le_one)
open scoped Topology

variable (q : ℕ) [Fact q.Prime]
variable {N Q : ℕ} {R : Finset ℕ} {hQ : 0<Q} (A : Certificate N R Q hQ)
    (hR : ∀p∈R,p.Prime)

theorem input_integral (hqQ : ¬q∣Q) (j : Fin Q) (u : ℤ) :
    padicNorm q (shiftQ j u)≤1 := by
  unfold shiftQ
  rw [padicNorm.div,(padicNorm.nat_eq_one_iff Q).mpr hqQ,div_one]
  exact padicNorm.sub.trans (max_le (padicNorm.of_int _) (padicNorm.of_nat _))

/-- The retained dilation only adds its own prime to the fixed denominators. -/
theorem affine_integral (p : ℕ) (hp : 0<p) (hqp : ¬q∣p) (b : ℚ)
    (hb : padicNorm q b≤1) :
    rationalAffine (p:ℚ) b (by exact_mod_cast hp)∈integralGL q := by
  apply integralGL_of_entries_det
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rationalAffine,Matrix.GeneralLinearGroup.mkOfDetNeZero,padicNorm.of_nat,hb]
  · simpa [rationalAffine,Matrix.GeneralLinearGroup.mkOfDetNeZero,Matrix.det_fin_two] using
      (padicNorm.nat_eq_one_iff p).mpr hqp

theorem primitive_fold_integral (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (j : Fin Q) (i : SpanningIntegerRows.RowIndex N Q) (d : residues i.val.1) (n : ℤ) :
    fold (level_pos (hQ:=hQ) hN i) (shiftQ j i.val.2) ((d.val:ℚ)/i.val.1) n∈integralGroup q := by
  have hqi : ¬q∣i.val.1 := fun hd => hqQ (hd.trans i.property.1)
  apply ofMatrix_mem
  apply reconstruction_integral q (Nat.lcm N (i.val.1^2))
    (Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos i.property.1 hQ) 2)).ne'
    (not_dvd_level q N i.val.1 hqN hqi)
  · exact input_integral q hqQ j i.val.2
  · apply padicNorm.sub.trans
    apply max_le _ (padicNorm.of_int n)
    rw [padicNorm.div,(padicNorm.nat_eq_one_iff i.val.1).mpr hqi,div_one]
    exact padicNorm.of_nat _

theorem retained_fold_integral (hqQ : ¬q∣Q) (hqR : ∀p∈R,¬q∣p)
    (j : Fin Q) (p : R) (u n : ℤ) :
    AsymptoticRationalBranches.compactFold
      (rationalAffine (p.val:ℚ) ((p.val:ℚ)*shiftQ j u) (retained_pos hR p))
      (det_positive _ _ (retained_pos hR p)) n∈integralGroup q := by
  apply compactFold_mem
  apply affine_integral q p.val (hR p.val p.property).pos (hqR p.val p.property)
  rw [padicNorm.mul,(padicNorm.nat_eq_one_iff p.val).mpr (hqR p.val p.property),one_mul]
  exact input_integral q hqQ j u

theorem primitiveLow_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (j : Fin Q) (i : SpanningIntegerRows.RowIndex N Q)
    {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Supported (integralGroup q) (primitiveLow A hN P j i t z) := by
  unfold primitiveLow
  apply supported_sum
  intro d
  apply supported_tsum
  · exact Summable.of_norm (AsymptoticRegularFoldedLow.term_norm_summable _ _ _ _ _ _ _ _ _ ht z)
  · intro n
    exact supported_weighted_branch _ _ (primitive_fold_integral (hQ:=hQ) q hN hqN hqQ j i d n) _ _ _ z

theorem retainedLow_supported (hqQ : ¬q∣Q) (hqR : ∀p∈R,¬q∣p)
    (P : Parameters A) (j : Fin Q) (p : R) (u : ℤ) (t : ℕ) (z : ℍ) :
    Supported (integralGroup q) (retainedLow A hR P j p u t z) := by
  unfold retainedLow
  apply supported_finsetSum
  intro n _
  exact supported_weighted_branch _ _ (retained_fold_integral q hR hqQ hqR j p u n) _ _ _ z

theorem low_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (hqR : ∀p∈R,¬q∣p) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Supported (integralGroup q) (low A hR hN P χ β t z) := by
  unfold low
  apply supported_sum
  intro j
  apply supported_finsetSum
  intro i _
  apply supported_smul
  cases i with
  | inl i => exact supported_smul _ _ (primitiveLow_supported q A hN hqN hqQ P j i ht z) _
  | inr i => exact supported_smul _ _ (retainedLow_supported q A hR hqQ hqR P j i.1 i.2 t z) _

theorem primitiveTerminal_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (j : Fin Q) (i : SpanningIntegerRows.RowIndex N Q)
    {t : ℕ} (ht : 2≤t) (z : ℍ) :
    Supported (integralGroup q) (primitiveTerminal A hN P j i ht z) := by
  unfold primitiveTerminal
  apply supported_sum
  intro d
  apply supported_tsum
  · exact Summable.of_norm (AsymptoticRegularFoldedTerminal.term_norm_summable _ _ _ _ _ _ _ _ _ _ ht z)
  · intro n
    exact supported_weighted_branch _ _ (primitive_fold_integral (hQ:=hQ) q hN hqN hqQ j i d n) _ _ _ z

theorem retainedTerminal_supported (hqQ : ¬q∣Q) (hqR : ∀p∈R,¬q∣p)
    (P : Parameters A) (j : Fin Q) (p : R) (u : ℤ) (t : ℕ) (z : ℍ) :
    Supported (integralGroup q) (retainedTerminal A hR P j p u t z) := by
  unfold retainedTerminal
  apply supported_finsetSum
  intro n _
  exact supported_weighted_branch _ _ (retained_fold_integral q hR hqQ hqR j p u n) _ _ _ z

theorem terminal_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (hqR : ∀p∈R,¬q∣p) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) :
    Supported (integralGroup q) (terminal A hR hN P χ β ht z) := by
  unfold terminal
  apply supported_sum
  intro j
  apply supported_finsetSum
  intro i _
  apply supported_smul
  cases i with
  | inl i => exact supported_smul _ _ (primitiveTerminal_supported q A hN hqN hqQ P j i ht z) _
  | inr i => exact supported_smul _ _ (retainedTerminal_supported q A hR hqQ hqR P j i.1 i.2 t z) _

/-- The actual infinite Neumann extension has the same fixed arithmetic
support as its branches. Its length introduces no new bad primes. -/
theorem extension_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (hqR : ∀p∈R,¬q∣p) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (hK : ‖low A hR hN P χ β t z‖<1) :
    Supported (integralGroup q) ((extension A hR hN P χ β ht z).comp
      (TerminalSpace A P z).subtypeL.adjoint) := by
  unfold extension AsymptoticReconstruction.low
  rw [comp_assoc,comp_assoc,AsymptoticOrbitRegion.subtype_comp_adjoint]
  apply supported_comp
  · apply supported_tsum _ _ (summable_geometric_of_norm_lt_one hK)
    intro n
    exact supported_pow _ _ (low_supported q A hR hN hqN hqQ hqR P χ β (by omega) z) n
  · exact supported_comp _ _ _
      (supported_add _ _ _ (supported_one _) (terminal_supported q A hR hN hqN hqQ hqR P χ β ht z))
      (supported_corner _ _ _)

set_option backward.isDefEq.respectTransparency true in
/-- Extending the normalized map by zero preserves every fresh-prime
subgroup. Both the Neumann and Newton limits are justified in operator norm. -/
theorem normalized_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (hqR : ∀p∈R,¬q∣p) (P : Parameters A) (e : Sector N) (z : ℍ) :
    Supported (integralGroup q) (regularAmbient A P hR hN e z) := by
  let I := (TerminalSpace A P z).subtypeL
  let B := scaled A hR hN P (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) z
  have hI : I.adjoint.comp I=1 := AsymptoticOrbitRegion.adjoint_comp_subtype _ z
  have hB : Supported (integralGroup q) (B.comp I.adjoint) := by
    dsimp only [B,scaled,reconstruction]
    rw [smul_comp,comp_assoc]
    have he := extension_supported q A hR hN hqN hqQ hqR P (multiplier e) (ramifiedParameter e)
      (by omega : 2≤exponent A P+3) z ((regular_contraction A P hR hN e z).trans (by norm_num))
    have hi := supported_weighted_branch (integralGroup q) 1 (integralGroup q).one_mem
      (fun w => (AsymptoticRegularInclusion.weight P.ε w:ℂ)) zero_le_one
      (AsymptoticRegularInclusion.weight_norm_le P.epsilon_pos) z
    have hh := supported_comp _ _ _ hi he
    let T := (AsymptoticRegularInclusion.inclusion P.epsilon_pos z).comp
      ((extension A hR hN P (multiplier e) (ramifiedParameter e)
        (by omega : 2≤exponent A P+3) z).comp I.adjoint)
    have hT : Supported (integralGroup q) T := hh
    change Supported (integralGroup q) ((bound A P)⁻¹ • T)
    have heq := RCLike.real_smul_eq_coe_smul (K:=ℂ) ((bound A P)⁻¹) T
    exact (congrArg (fun F => Supported (integralGroup q) F) heq).mpr
      (supported_smul (integralGroup q) T hT (((bound A P)⁻¹:ℝ):ℂ))
  have ht (n : ℕ) : polynomialNormalizedReconstruction (B.comp I.adjoint) n=
      (polynomialNormalizedReconstruction B n).comp I.adjoint := by
    simpa only [one_def,id_comp] using polynomialNormalizedReconstruction_transport I hI
      (1 : Space →L[ℂ] Space)
      ((norm_map_iff_adjoint_comp_self (1 : Space →L[ℂ] Space)).1 (fun _ => rfl)) B n
  apply supported_strong_limit (integralGroup q)
    (fun n => polynomialNormalizedReconstruction (B.comp I.adjoint) n) _
    (fun n => QuantitativeEulerEndpointPrepared.polynomial_normalization_supported _ _ hB n)
  have he : Tendsto (fun n : ℕ => (1-gramLower A P)^(2^n)/Real.sqrt (gramLower A P))
      atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (sub_nonneg.mpr (gramLower_le_one A P)) (by linarith [gramLower_pos A P])
    have hn := hp.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℕ)<2))
    simpa using hn.div_const (Real.sqrt (gramLower A P))
  have hn : Tendsto (fun n => polynomialNormalizedReconstruction B n) atTop
      (𝓝 (normalizedReconstruction B)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => polynomial_error A hR hN P (multiplier e) (ramifiedParameter e)
        (fun r _ => multiplier_norm e r) (fun p _ => ramifiedParameter_norm e p)
        (by omega : 2≤exponent A P+3) z (regular_contraction A P hR hN e z) n) he
  intro v
  simp only [ht,comp_apply]
  change Tendsto (fun n => (polynomialNormalizedReconstruction B n) (I.adjoint v)) atTop
    (𝓝 ((normalizedReconstruction B) (I.adjoint v)))
  exact ((ContinuousLinearMap.apply ℂ Space (I.adjoint v)).continuous.tendsto _).comp hn

theorem image_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (hqR : ∀p∈R,¬q∣p) (P : Parameters A) (e : Sector N) (z : ℍ) :
    Supported (integralGroup q) (QuantitativeArithmeticRetainedImageTrace.image A P hR hN e z).starProjection := by
  unfold QuantitativeArithmeticRetainedImageTrace.image
  rw [QuantitativeEulerEndpointIsometricImage.image_projection]
  have hu := normalized_supported q A hR hN hqN hqQ hqR P e z
  apply supported_comp _ _ _ hu
  apply supported_comp _ _ _ _ (supported_adjoint _ _ hu)
  rw [QuantitativeSpectralExceptionalRows.region_projection]
  exact supported_corner _ _ _

#print axioms primitive_fold_integral
#print axioms retained_fold_integral
#print axioms low_supported
#print axioms terminal_supported
#print axioms extension_supported
#print axioms normalized_supported
#print axioms image_supported
end QuantitativeArithmeticRetainedIntegralSupport

namespace QuantitativeArithmeticRetainedBaseline
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticSectorSigns
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedRegularExtension QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedImageTrace QuantitativeArithmeticRetainedFilterExpression
open QuantitativeArithmeticRetainedIntegralSupport QuantitativeEulerEndpointPrepared
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeSpectralCornerCutRow QuantitativeSpectralRegularCornerStep
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup AsymptoticOrbitDiagonal
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s)

/-- Start inside the actual full mixed reconstruction image and cut only
fixed original twist and ramified rows. Individual fresh rows are not imposed. -/
def baseline (a : ℝ) (x : ℍ) : Submodule ℂ Space :=
  nextSpace (image A P hR₀ (NeZero.pos N) sector x)
    (newBaselineDetector N sector hs P.epsilon_pos (exponent A P+4) x) (Real.sqrt a)

instance baseline_complete (a : ℝ) (x : ℍ) :
    CompleteSpace (baseline A P hR₀ sector hs a x) := by
  unfold baseline
  infer_instance

def closedBaseline (a : ℝ) (x : ℍ) : ClosedSubmodule ℂ Space where
  toSubmodule := baseline A P hR₀ sector hs a x
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (baseline A P hR₀ sector hs a x))).isClosed

theorem baseline_le (a : ℝ) (x : ℍ) :
    baseline A P hR₀ sector hs a x ≤ image A P hR₀ (NeZero.pos N) sector x :=
  nextSpace_le _ _ _

theorem baseline_energy (a : ℝ) (ha : 0≤a) (x : ℍ) (v : Space)
    (hv : v∈baseline A P hR₀ sector hs a x) :
    ‖newBaselineDetector N sector hs P.epsilon_pos (exponent A P+4) x v‖^2≤a*‖v‖^2 := by
  simpa only [Real.sq_sqrt ha] using nextSpace_energy _ _ (Real.sqrt a) v hv

theorem image_regular :
    (∀g k,Measurable (fun x => matrix (image A P hR₀ (NeZero.pos N) sector x).starProjection g k)) ∧
      Covariant (fun x => (image A P hR₀ (NeZero.pos N) sector x).starProjection) := by
  have hU := regularAmbient_regular A P hR₀ (NeZero.pos N) sector
  have hm : ∀g k,Measurable (fun x => matrix (TerminalSpace A P x).starProjection g k) := by
    simp only [TerminalSpace,QuantitativeSpectralExceptionalRows.region_projection]
    exact corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
      (AsymptoticCertificateOperators.highStrip_measurable _)
  have hc : Covariant (fun x => (TerminalSpace A P x).starProjection) := by
    simp only [TerminalSpace,QuantitativeSpectralExceptionalRows.region_projection]
    exact corner_covariant _
  simp only [image,QuantitativeEulerEndpointIsometricImage.image_projection]
  exact ⟨matrix_comp_measurable _ _ hU.1
    (matrix_comp_measurable _ _ hm (matrix_adjoint_measurable _ hU.1)),
    covariant_comp _ _ hU.2 (covariant_comp _ _ hc (covariant_adjoint _ hU.2))⟩

theorem baseline_regular (a : ℝ) (ha : 0<a) :
    (∀g k,Measurable (fun x => matrix (baseline A P hR₀ sector hs a x).starProjection g k)) ∧
      Covariant (fun x => (baseline A P hR₀ sector hs a x).starProjection) := by
  have hr := image_regular A P hR₀ sector
  obtain ⟨M,_hM,hM,hm,hc⟩ := newBaselineDetector_regular N sector hs P.epsilon_pos (exponent A P+4)
  exact (step_regular _ _ hr.1 hr.2 hm hc M hM (Real.sqrt a) (Real.sqrt_pos.mpr ha)).1

theorem baseline_supported (q : ℕ) [Fact q.Prime]
    (hqN : ¬q∣N) (hqQ : ¬q∣Q) (hqR : ∀p∈R₀,¬q∣p)
    (hqfixed : ∀b : UnitResidue N,¬q∣(primeLift N b).q)
    (a : ℝ) (ha : 0<a) (x : ℍ) :
    Supported (integralGroup q) (baseline A P hR₀ sector hs a x).starProjection :=
  (step_supported _ _ _
    (image_supported q A hR₀ (NeZero.pos N) hqN hqQ hqR P sector x)
    (newBaselineDetector_supported N sector q hqN hqfixed hs P.epsilon_pos (exponent A P+4) x)
    (Real.sqrt a) (Real.sqrt_pos.mpr ha)).1

theorem baseline_kernel_survives (a : ℝ) (x : ℍ) (v : Space)
    (hv : v∈image A P hR₀ (NeZero.pos N) sector x)
    (hz : newBaselineDetector N sector hs P.epsilon_pos (exponent A P+4) x v=0) :
    v∈baseline A P hR₀ sector hs a x := kernel_survives _ _ _ hv hz

/-- The mixed prime-chain estimate with baseline energy and arithmetic support
fully discharged. Only a finite set of fixed denominators is excluded. -/
theorem exists_baseline_chain_trace_bound
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
      let U := closedBaseline A P hR₀ sector hs a
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤exponent A P+4)+H⁻¹
      ∀ l : List (EligiblePrime N), l.Nodup →
      (∀ p∈l,D₀.Good p.val ∧ (p.val:ℝ)≤X ∧ ¬p.val∣Q ∧ ∀r∈R₀,¬p.val∣r) →
      cornerMass (primeChain N (NeZero.pos N) (sign sector.1) hs P.epsilon_pos (exponent A P+4) c U l)-target ≤
        (l.map primeFactor).prod*(cornerMass U-target) := by
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    QuantitativeArithmeticRetainedPrimeStep.exists_image_chain_trace_bound A P hR₀ D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC X H hH hdata Y R hZ L hs J a c U target l hnodup hl
  have hJ : 0≤J := mul_nonneg
    (mul_nonneg (sq_nonneg _) (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)))
    (mul_nonneg hK (sq_nonneg _))
  have ha : 0<a := baseline_threshold_pos (2*J) (mul_nonneg (by norm_num) hJ)
  have hr := baseline_regular A P hR₀ sector hs a ha
  apply hbound C hBC X H hH hdata U hr.1 hr.2 (baseline_le A P hR₀ sector hs a)
    (fun x _ v hv => baseline_energy A P hR₀ sector hs a ha.le x v hv) l hnodup
    (fun p hp => ⟨(hl p hp).1,(hl p hp).2.1⟩)
  intro p hp x
  exact baseline_supported A P hR₀ sector hs p.val p.property.2
    (hl p hp).2.2.1 (hl p hp).2.2.2
    (good_prime_avoids_baseline D₀ hex p.val (hl p hp).1) a ha x

#print axioms baseline_energy
#print axioms baseline_regular
#print axioms baseline_supported
#print axioms baseline_kernel_survives
#print axioms exists_baseline_chain_trace_bound
end QuantitativeArithmeticRetainedBaseline
