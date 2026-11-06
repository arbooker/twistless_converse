module

public import QuantitativeEulerEndpointReconstructedCommonStepV1
public import QuantitativeEulerEndpointNewChainIterationV1
public import QuantitativeEulerEndpointBaselineExclusionsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularReconstruction QuantitativeHolomorphic
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}

def closedReconstructedBaseline (A : Certificate N Q hQ) (P : Parameters A) (sector : Sector N)
    (F : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (F x)]
    (hF : ∀ x,F x≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x)
    {s : Set ℍ} (hs : IsCompact s) (a : ℝ) (x : ℍ) : ClosedSubmodule ℂ Space where
  toSubmodule := reconstructedBaseline A P sector F hF hs a x
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (reconstructedBaseline A P sector F hF hs a x))).isClosed

/-- Successive original-prime cuts in the actual reconstructed image multiply
the excess trace by the product of (1-1/q). Baseline energy, finite trace and
each one-prime contraction are discharged. The initial terminal source and
the list's fresh-prime support remain explicit structural inputs. -/
theorem endpoint_reconstructed_chain_trace_bound
    (A : Certificate N Q hQ) (P : Parameters A)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (hex : baselineDenominators N⊆excluded)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ C : ℝ, B≤C → ∀ X H : ℝ, max P'.ε⁻¹ 4≤H →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P'.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*X^4
      let hs := wideFreshRegion_compact L R R hZ
      let J := (countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
        (K*((wideDistortion L R R)^(P'.s+4))^2)
      let a := (2*(1+2*J))⁻¹
      let c := Real.sqrt a
      ∀ (F : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (F x)],
      (∀ g k,Measurable (fun x => matrix (F x).starProjection g k)) →
      Covariant (fun x => (F x).starProjection) →
      ∀ hF : ∀ x,F x≤TerminalSpace A P' x,
      let U := closedReconstructedBaseline A P sector F hF hs a
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P'.epsilon_pos (by omega : 1≤P'.s+4)+H⁻¹
      ∀ l : List (EligiblePrime N), l.Nodup →
      (∀ p∈l,D₀.Good p.val ∧ (p.val:ℝ)≤X ∧ ¬p.val∣Q) →
      (∀ p∈l,∀ x,Supported (integralGroup p.val) (F x).starProjection) →
      cornerMass (primeChain N (NeZero.pos N) (sign sector.1) hs P'.epsilon_pos (P'.s+4) c U l)-target ≤
        (l.map primeFactor).prod*(cornerMass U-target) := by
  intro P'
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_common_reconstructed_prime_loss A P D₀ hN2 sector S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC X H hH hdata Y R hZ L hs J a c F instF hmF hcF hF U target l hnodup hl hsF
  have hJ : 0≤J := mul_nonneg
    (mul_nonneg (sq_nonneg _) (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)))
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
  have hreg := reconstructed_baseline_regular A P sector F hF hs hmF hcF a ha
  have hf := reconstructed_image_trace_finite A (NeZero.pos N) P sector F
    (reconstructedBaseline A P sector F hF hs a) hF
    (reconstructed_baseline_le A P sector F hF hs a) hreg.1 hreg.2
  apply primeChain_trace_bound_of_step N (NeZero.pos N) (sign sector.1) hs P'.epsilon_pos (P'.s+4) c hc
    target (reconstructedBaseline A P sector F hF hs a) U hreg.1 hreg.2 hf (fun _ => le_rfl) l hnodup
  · intro p hp x
    exact reconstructed_baseline_supported A P sector F hF hs p.val p.property.2 (hl p hp).2.2
      (good_prime_avoids_baseline D₀ hex p.val (hl p hp).1) (hsF p hp) a ha x
  · intro p hp V hmV hcV _hfV hV hsupport
    obtain ⟨_hqN,hstep⟩ := hbound C hBC X p.val (hl p hp).1 (hl p hp).2.1
    exact hstep H hH hdata F hF (fun x => (V x).toSubmodule) hmV hcV a ha.le hV hsupport
      c (primeCut c p.val) hc (primeCut_pos c hc p.val) (primeCut_sq c p.val) hsmall

#print axioms endpoint_reconstructed_chain_trace_bound
end QuantitativeEulerEndpointPrepared
