module

public import QuantitativeEulerEndpointNormalizedPacketContractionV1
public import QuantitativeEulerEndpointNormalizedThresholdV1
public import QuantitativeEulerEndpointWideCombinedNormV1
public import QuantitativeEulerEndpointBoundedIterationV1
public import QuantitativeEulerEndpointBoundedIterationBoundV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularReconstruction QuantitativeHolomorphic
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBlocks
open scoped Classical MatrixGroups ENNReal
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}

/-- Construct the actual normalized terminal polynomial sequence from identity.
All hard contractions, scalar schedules, propagated defects, future-prime
supports and exact solution invariants are discharged. The normalization uses explicit geometric row bounds. The prime-product
budget is the remaining arithmetic input to this interface. -/
theorem exists_prepared_bounded_iteration
    (A : Certificate N Q hQ) (P : Parameters A)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (hex : baselineDenominators N⊆excluded)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (n : ℕ) (C X : ℕ → ℝ), (∀ j,j<n → B≤C j) →
      ∀ H : ℝ,max P'.ε⁻¹ 4≤H →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P'.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := fun j => (2*generatorTransportConstant D₀*C j)*(X j)^4
      let hs := fun j => wideFreshRegion_compact (L j) R R hZ
      let J := fun j => (countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
        (K*((wideDistortion (L j) R R)^(P'.s+4))^2)
      let c := fun j => Real.sqrt ((2*(1+2*J j))⁻¹)
      let Z := Y/wideDistortion Bg 2 (D*H)
      let height := fun j => L j*(R+R+1)/min 1 Z
      let low := fun j => Z/wideDistortion (L j) R R
      ∀ l : ℕ → List (EligiblePrime N),
      let b : ℕ → Block A P sector := fun j => ⟨_,hs j,l j,c j,
        wideCombinedBound A P sector (height j+1) (low j) (height j) (l j),
        combined_rows_wide_norm A P sector (hs j)
          (div_pos hZ (wideDistortion_pos (L j) R R))
          (fun _ hz => hz.1) (fun _ hz => hz.2.1) (fun _ hz => hz.2.2) (l j)⟩
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P'.epsilon_pos (by omega : 1≤P'.s+4)+H⁻¹
      (∀ j,j<n → (l j).Nodup) →
      (∀ j,j<n → ∀ p∈l j,D₀.Good p.val ∧ (p.val:ℝ)≤X j ∧ ¬p.val∣Q) →
      (∀ i j,i<j → j<n → ∀ r∈l j,r∉l i) →
      ∀ (bad : ℕ → ℝ) (Cbad : ℝ), (∀ j,0≤bad j) →
      (∑ j∈Finset.range n,bad j)≤Cbad →
      (∀ j,j<n → ((l j).map primeFactor).prod≤Real.exp (bad j)/4) →
      ∃ (F : ℕ → Algebra A P) (z : ℕ → ℝ[X]),F 0=1 ∧
        (∀ j,j≤n → Valid A P sector n b j (F j)) ∧
        (∀ j,j<n → Step A P sector n b target j (F j) (z j) ∧
          F (j+1)=nextAt A P sector n b j (F j) (z j)) ∧
        (∀ E : Algebra A P,
          (∀ j,j<n → ∀ i : Fin ((l j).length+1),∀ x,
            normalizedCombinedRows A P sector (hs j) (l j) i x*rep A P E x=0) →
          ∀ j,j≤n → F j*E=E) ∧
        tr A P (F n)≤target+Real.exp (Cbad+8)*
          (P'.ε⁻¹+4*(1+P'.ε⁻¹*Real.log 2))/(4:ℝ)^n := by
  intro P'
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_normalized_combined_packet_contraction
      A P D₀ hN2 sector hex S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro n C X hC H hH hdata Y R hZ L hs J c Z height low l b target hnodup hgood hdisjoint bad Cbad hbad hbudget hprime
  have hprimes : ∀ j,j<n → ∀ r∈(b j).primes,
      ¬r.val∣Q ∧ ∀ a : UnitResidue N,¬r.val∣(primeLift N a).q := by
    intro j hj r hr
    exact ⟨(hgood j hj r hr).2.2,good_prime_avoids_baseline D₀ hex r.val (hgood j hj r hr).1⟩
  have hstep (j : ℕ) (hj : j<n) (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1)
      (hsF : ∀ r∈(b j).primes,∀ x,Supported (integralGroup r.val) (rep A P F x))
      (hdef : tr A P (F-F^2)≤4*P'.ε⁻¹/(sharpnessAt A P sector n b j:ℝ)) :
      ∃ z,Step A P sector n b target j F z := by
    have hJ : 0≤J j := mul_nonneg
      (mul_nonneg (sq_nonneg _) (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)))
      (mul_nonneg hK (sq_nonneg _))
    have hc : 0<(b j).cutoff := QuantitativeEulerEndpointNormalizedThreshold.threshold_pos hJ
    have hu := (QuantitativeEulerEndpointNormalizedThreshold.normalized_range
      (b j).bound ((b j).primes.length+1) hJ).2
    have hregular := half_regular A P F (IsSelfAdjoint.of_nonneg hF0)
    have hsupport : ∀ p∈l j,∀ x,Supported (integralGroup p.val) (half A P F x).toSubmodule.starProjection := by
      intro p hp x
      exact half_supported A P F (IsSelfAdjoint.of_nonneg hF0) (integralGroup p.val) (hsF p hp) x
    have hchain := hbound (C j) (hC j hj) (X j) H hH hdata (half A P F)
      hregular.1 hregular.2 (half_le_terminal A P F hF0 hF1)
      (l j) (hnodup j hj) (hgood j hj) hsupport
    exact exists_step A P sector n b j hj.le F hF0 hF1 target hc hu hchain hdef
  obtain ⟨F,z,hzero,hvalid,hsteps,hfixed⟩ :=
    exists_iteration A P sector n b hprimes hdisjoint target hstep
  refine ⟨F,z,hzero,hvalid,hsteps,hfixed,?_⟩
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  have htarget : 0≤target := add_nonneg
    (sectorTraceTarget_nonneg N (NeZero.pos N) sector S hS hH0 P'.epsilon_pos (by omega))
    (inv_nonneg.mpr hH0)
  exact finite_trace_bound A P sector n b target F z hzero htarget hsteps bad hbad hbudget hprime

#print axioms exists_prepared_bounded_iteration
end QuantitativeEulerEndpointBoundedIteration
