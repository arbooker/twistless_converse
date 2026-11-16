module

public import QuantitativeMaassMajorantCompactFilterLimitV1
public import QuantitativeMaassMajorantPositiveExcessV1
public import QuantitativeMaassCanonicalWeightedFilterV1
public import QuantitativeMaassJointMetricFullWindowCountV1
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


/-- The finite filter is constructed internally. Its regular cancellation,
physical recovery, centering and height tail give decay of the exact
full-terminal excess used in the original two-parity counting bound. -/
theorem originalMajorant_joint_metric_excess_limit {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ q : ↥N.primeFactors, CuspEnergySpectrum (N/q.val)
      (prime_quotient_pos N q.val hN (Nat.prime_of_mem_primeFactors q.property)
        (Nat.dvd_of_mem_primeFactors q.property)))
    (cover : AdmissibleScalarCover N hAd) (e : Sector N)
    {Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (hN2 : 2≤N)
    (C : ℝ) (hC : 1≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hCs : supportRadius K hc≤C) (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => RawOriginalWindow.jointMetricSectorExcess A hAd cover P e
      (originalWindowMajorant K hc ε t) (originalWindowMajorant_compact K hc ε t)
      (originalWindowMajorant_even K he hc ε t) (C*radius ε t)
      (mul_nonneg (zero_le_one.trans hC) (radius_pos ε t).le)
      (originalMajorant_support_enlarged K hc ε t C hCs)/(t*ε t)) atTop (𝓝 0) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let δ := P'.ε
  let ν := P'.s+3
  have hδ : 0<δ := P'.epsilon_pos
  have hν : 1≤ν := by dsimp only [ν]; omega
  let M := cover.metric hδ hν
  let Qcan := cover.regularProjection hδ hν e
  let I := (AsymptoticRegularTrace.trace volume Qcan).toReal
  obtain ⟨B,D,Kerr,Kreg,hB,hD,hKerr,hKreg,hfilter⟩ :=
    RawCommonReconstruction.exists_bounded_weighted_canonical_filter A P hN2 e cover
  choose E hmass hmatrix hphysical hregular hfinite hsource hweighted using hfilter
  have hEn (n : ℕ) (x : UpperHalfPlane) : ‖AsymptoticFiniteBranch.regularSum (E n) x‖≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hregular n x).1).mpr (hregular n x).2
  have hQn (x : UpperHalfPlane) : ‖Qcan x‖≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (cover.regularProjection_isProjection hδ hν e x).nonneg).mpr
      (cover.regularProjection_isProjection hδ hν e x).le_one
  have hcompact := originalMajorant_compact_filter_excess_limit basis N p hN hAd hpN hNp hpres a b hab T S
    cover e ν hν δ C hδ hC K hc he hK hm ε hε hp E B 1 D Kreg I hB hD hKreg
    ENNReal.toReal_nonneg hmass hmatrix hEn hQn hweighted
  let Z := cylinderZeroExtension.toContinuousLinearMap
  let F := fun n => Z.adjoint.comp ((AsymptoticFiniteBranch.holomorphicSum (E n) 0).comp Z)
  let Dm := M.change.symm.toContinuousLinearMap
  let W := RawCommonReconstruction.metricCylinderSource A P e M.change
  let Qphys := cover.physicalNewSignProjection hδ hν (sectorCharacter N hAd.1 e)
    (sectorCharacter_norm N hAd.1 e)
  have hF (n : ℕ) : 0≤F n :=
    nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp (hphysical n).1).adjoint_conj Z)
  have herr (n : ℕ) : ‖F n*W.starProjection-W.starProjection‖≤Real.sqrt (Kerr/(2:ℝ)^n) :=
    RawCommonReconstruction.physical_filter_cylinder_error A P e M
      (AsymptoticFiniteBranch.holomorphicSum (E n) 0) (Real.le_sqrt_of_sq_le (hsource n))
  have hpositive : (Dm*W.starProjection*Dm.adjoint-Dm*Qphys*Dm.adjoint).IsPositive :=
    cover.physical_source_excess_positive A P e
  have hh := originalMajorant_positive_excess_limit basis W F Qphys Dm hF Kerr hKerr herr hpositive
    δ hδ ν C hC K hc he hK hm hCs ε hε hp
    (by simpa only [mul_def,comp_assoc] using hcompact)
  let U := (fullTerminalTranslationIsometry A hAd.1 P e).toContinuousLinearMap
  let O := U.comp (fullTerminalColumnOutput A hAd.1 P e)
  have hscaled := hh.const_mul (‖M.change.toContinuousLinearMap‖^2*‖O‖^2)
  rw [mul_zero] at hscaled
  simpa only [RawOriginalWindow.jointMetricSectorExcess,mul_div_assoc,mul_def,comp_assoc]
    using hscaled

#print axioms originalMajorant_joint_metric_excess_limit
end QuantitativeMaass.Scheduled
