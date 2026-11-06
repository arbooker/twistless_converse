module

public import QuantitativeEulerEndpointSectorCommonStepV1
public import QuantitativeEulerEndpointNewPacketDecayV1
public import QuantitativeEulerEndpointNewChainIterationV1
public import QuantitativeEulerEndpointBaselineExclusionsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups ENNReal

/-- Actual successive cuts of original twist rows, starting from the
fixed original and ramified cutoff, contract toward sector incidence plus the
explicit geometric tail cost. All one-prime loss premises are discharged. -/
theorem endpoint_sector_chain_trace_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) (hN2 : 2≤N) (sector : Sector N)
    (hex : baselineDenominators N⊆excluded)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (X H : ℝ), max ε⁻¹ 4≤H →
      (∀ i, sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      ∀ (t : ℕ) (ht : 1≤t),
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant P*C)*X^4
      let hs := wideFreshRegion_compact L R R hZ
      let A := sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H ε t*
        (K*((wideDistortion L R R)^t)^2)
      let a := (2*(1+2*A))⁻¹
      let c := Real.sqrt a
      let U := closedNewBaselineSurvivor N H sector hs hε t a
      ∀ l : List (EligiblePrime N), l.Nodup → (∀ p∈l, P.Good p.val ∧ (p.val:ℝ)≤X) →
      cornerMass (primeChain N (NeZero.pos N) (sign sector.1) hs hε t c U l)-
        sectorTraceTarget N (NeZero.pos N) sector S hS H hε ht≤
      (l.map primeFactor).prod*(cornerMass U-sectorTraceTarget N (NeZero.pos N) sector S hS H hε ht) := by
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_common_sector_prime_trace_loss P hN2 sector S hS hε
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC X H hH hdata t ht Y R hZ L hs A a c U l hnodup hl
  have hA : 0≤A := mul_nonneg (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H ε t)
    (mul_nonneg hK (sq_nonneg _))
  have h2A : 0≤2*A := mul_nonneg (by norm_num) hA
  have ha : 0<a := baseline_threshold_pos (2*A) h2A
  have hc : 0<c := Real.sqrt_pos.mpr ha
  have hsmall : A*(a+c^2)<1 := by
    have he : c^2=a := Real.sq_sqrt ha.le
    rw [he]
    have hh := baseline_threshold_small (2*A) h2A
    change 2*A*a≤(1:ℝ)/2 at hh
    nlinarith only [hh]
  have hreg := newBaselineSurvivor_regular N H sector hs hε t a ha
  have hf := newBaselineSurvivor_trace_finite N H sector hs hε t a
  apply primeChain_trace_bound_of_step N (NeZero.pos N) (sign sector.1) hs hε t c hc
    (sectorTraceTarget N (NeZero.pos N) sector S hS H hε ht)
    (newBaselineSurvivor N H sector hs hε t a) U hreg.1 hreg.2 hf (fun _ => le_rfl) l hnodup
  · intro p hp x
    exact newBaselineSurvivor_supported N p.val p.property.2
      (good_prime_avoids_baseline P hex p.val (hl p hp).1) H sector hs hε t x a ha
  · intro p hp F hmF hcF _hfF hF hsupport
    obtain ⟨_hqN,hstep⟩ := hbound C hBC X p.val (hl p hp).1 (hl p hp).2
    exact hstep H hH hdata t ht a ha.le (fun x => (F x).toSubmodule) hmF hcF hF hsupport
      c (primeCut c p.val) hc (primeCut_pos c hc p.val) (primeCut_sq c p.val) hsmall

#print axioms endpoint_sector_chain_trace_bound
end QuantitativeEulerEndpointPrepared
