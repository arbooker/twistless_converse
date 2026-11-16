module

public import QuantitativeMaassMajorantCompactCanonicalTraceV1
public import QuantitativeMaassCompactMajorantCanonicalMainV1
public import QuantitativeMaassMajorantRawCompactGeometryV1
public import QuantitativeMaassMajorantRegularRecoveryV1
public import QuantitativeMaassCanonicalRegularityV1
public import QuantitativeArithmeticMaassCanonicalLocalTraceV1
public import QuantitativeMaassCappedColumnTraceV1
public import QuantitativeMaassCanonicalProjectionSumV1
public import QuantitativeMaassMajorantSharpProjectionMainV1
public import QuantitativeArithmeticMaassMajorantSmoothingTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter MeasureTheory ContinuousLinearMap QuantitativeNinaMaass AsymptoticSectorSigns
open AsymptoticClassicalPetersson QuantitativeArithmeticRepeatedTwoBands
open QuantitativeArithmeticNewBandProjections
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩


/-- The finite-filter physical excess has zero normalized limit: its geometric
error, regular recovery error, and canonical trace error cancel against the
same sharp main term. The filter hypotheses are supplied by the constructed
weighted canonical filter. -/
theorem originalMajorant_compact_filter_excess_limit {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ q : ↥N.primeFactors, CuspEnergySpectrum (N/q.val)
      (prime_quotient_pos N q.val hN (Nat.prime_of_mem_primeFactors q.property)
        (Nat.dvd_of_mem_primeFactors q.property)))
    (cover : AdmissibleScalarCover N hAd) (e : Sector N) (ν : ℕ) (hν : 1≤ν)
    (δ C : ℝ) (hδ : 0<δ) (hC : 1≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (E : ℕ→AsymptoticFiniteBranch.Expression) (B A D Kreg I : ℝ)
    (hB : 0≤B) (hD : 0≤D) (hKreg : 0≤Kreg) (hI : 0≤I)
    (hmass : ∀ n,AsymptoticFiniteBranch.expressionBound (E n)≤Real.exp (Real.exp (B*(4:ℝ)^n)))
    (hmatrix : ∀ n,QuantitativeHolomorphic.ExpressionMatrixBound (E n) (Real.exp (Real.exp (B*(4:ℝ)^n))))
    (hE : ∀ n x,‖AsymptoticFiniteBranch.regularSum (E n) x‖≤A)
    (hQ : ∀ x,‖cover.regularProjection hδ hν e x‖≤A)
    (hweighted : ∀ n (B : UpperHalfPlane→AsymptoticRegularCompactBranch.Space→L[ℂ]AsymptoticRegularCompactBranch.Space)
      (L : ℝ),0≤L →
      (∀ a b,Measurable (fun x => AsymptoticRegularTrace.matrix (B x) a b)) → AsymptoticRegularTrace.Covariant B →
      (∀ x,‖B x‖≤L) →
      |AsymptoticRegularTrace.signedTrace volume (fun x => B x*(AsymptoticFiniteBranch.regularSum (E n) x-
        cover.regularProjection hδ hν e x))|≤L*(D/(2:ℝ)^n+4*Real.sqrt (Kreg/(2:ℝ)^n)*I)) :
    Tendsto (fun t =>
      let R := C*radius ε t
      let J := ⌈(ν:ℝ)*R+1⌉₊
      let a := movingLowerEdge δ C ε t
      let Ω := cutoffRectangle a t
      let Pc := AsymptoticRegionL2.projection (quotientMeasure 0) Ω
        (upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)).measurableSet
      let L := (terminalInverseWeightBand δ ν J).comp (cover.metric hδ hν).change.symm.toContinuousLinearMap
      let Q := cover.physicalNewSignProjection hδ hν (sectorCharacter N hAd.1 e)
        (sectorCharacter_norm N hAd.1 e)
      let Z := cylinderZeroExtension.toContinuousLinearMap
      let F := Z.adjoint.comp ((AsymptoticFiniteBranch.holomorphicSum (E (rawBlockHorizon t)) 0).comp Z)
      columnLinearTrace (quotientMeasure 0) (fun z => Pc (originalMajorantColumn K hc he ε t z))
        (L.comp ((F-Q).comp L.adjoint))/(t*ε t)) atTop (𝓝 0) := by
  have hC0 : 0≤C := zero_le_one.trans hC
  have hg := originalMajorant_raw_compact_geometry_limit basis N (cover.metric hδ hν) δ C hδ hC ν
    E B hB hmass hmatrix K hc he ε hε hp
  have hr := originalMajorant_regular_recovery_limit (cover.metric hδ hν) δ C hδ hC ν E
    (cover.regularProjection hδ hν e) A D Kreg I hD hKreg hI
    ((cover.regularProjection_regular hδ hν e).1 1 1) hE hQ hweighted K hc he hK hm ε hε hp
  have hcmain := originalMajorant_compact_canonical_main_decay basis N p hN hAd hpN hNp hpres a b hab T S
    cover e ν hν δ C hδ hC0 K hc he hK hm ε hε hp 0
  simp only [zero_mul,Real.exp_zero,one_mul] at hcmain
  have hh := (hg.add hr).sub hcmain
  simp only [add_zero,sub_zero] at hh
  convert hh using 1
  funext t
  dsimp only [originalMajorantCompactMetricTraceError,compactMetricRegularDifference,
    cutoffRectangle,originalMajorantColumn]
  rw [sub_comp,comp_sub,columnLinearTrace_sub (quotientMeasure 0) _
    (cylinderTimeColumn_compact_input_memLp (originalWindowMajorant K hc ε t)
      (originalWindowMajorant_compact K hc ε t) (originalWindowMajorant_even K he hc ε t)
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (originalMajorant_support K hc ε t) (movingLowerEdge_pos hδ C ε t)
      (Real.exp (Strong.strongScale t/2)))]
  have hmain := cover.originalMajorant_regular_canonical_main hδ hν e C hC0 K hc ε t
  change (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2 *
    (∫ z in cutoffRectangle (movingLowerEdge δ C ε t) t,
      (metricCapCoefficient (cover.metric hδ hν) δ ν ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊ z *
        star (metricCapCoefficient (cover.metric hδ hν) δ ν ⌈(ν:ℝ)*(C*radius ε t)+1⌉₊ z) *
        AsymptoticRegularTrace.matrix (cover.regularProjection hδ hν e z) 1 1 *
        windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
          (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))).re)=
      originalMajorantSharpSectorProjectionMain N hN e δ C K hc ε t at hmain
  dsimp only [cutoffRectangle] at hmain
  rw [←hmain]
  simp only [starRingEnd_apply,mul_assoc,mul_left_comm,mul_comm]
  ring

#print axioms originalMajorant_compact_filter_excess_limit
end QuantitativeMaass.Scheduled
