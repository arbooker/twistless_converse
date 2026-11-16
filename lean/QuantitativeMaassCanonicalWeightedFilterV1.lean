module

public import QuantitativeMaassFreeWeightedExcessV1
public import QuantitativeMaassBoundedFullCanonicalV1
public import QuantitativeMaassCanonicalRegularityV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped ENNReal
namespace QuantitativeMaass.RawCommonReconstruction
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticFiniteBranch AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticRegularCompactBranch (Space)

/-- One constructed finite filter has physical recovery and weighted regular
canonical excess tending to zero. The canonical coefficient remains exactly one. -/
theorem exists_bounded_weighted_canonical_filter {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A) (hN2 : 2≤N) (e : Sector N)
    {hN : GridAdmissibleGap.Admissible N} (cover : AdmissibleScalarCover N hN) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let M := cover.metric P'.epsilon_pos (by omega : 1≤P'.s+3)
    let Qcan := cover.regularProjection P'.epsilon_pos (by omega : 1≤P'.s+3) e
    let I := (trace volume Qcan).toReal
    ∃ C D K Kreg : ℝ,0≤C ∧ 0≤D ∧ 0≤K ∧ 0≤Kreg ∧ ∀ n : ℕ,∃ E : Expression,
      expressionBound E≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound E (Real.exp (Real.exp (C*(4:ℝ)^n))) ∧
      (0≤holomorphicSum E 0 ∧ holomorphicSum E 0≤1) ∧
      (∀ x,0≤regularSum E x ∧ regularSum E x≤1) ∧
      trace volume (regularSum E)<∞ ∧
      ‖holomorphicSum E 0*(physicalMetricSource A P e M).starProjection-
        (physicalMetricSource A P e M).starProjection‖^2≤K/(2:ℝ)^n ∧
      ∀ (B : ℍ→Space→L[ℂ]Space) (L : ℝ),0≤L →
        (∀ a b,Measurable (fun x => matrix (B x) a b)) → Covariant B →
        (∀ x,‖B x‖≤L) →
        |signedTrace volume (fun x => B x*(regularSum E x-Qcan x))|≤
          L*(D/(2:ℝ)^n+4*Real.sqrt (Kreg/(2:ℝ)^n)*I) := by
  intro P' M Qcan I
  obtain ⟨C,D,K,Kreg,hC,hD,hK,hKreg,hfilter⟩ := exists_bounded_full_canonical_filter A P hN2 e cover
  have hQr := cover.regularProjection_regular P'.epsilon_pos (by omega : 1≤P'.s+3) e
  have hQp := cover.regularProjection_isProjection P'.epsilon_pos (by omega : 1≤P'.s+3) e
  have hQf := cover.regularProjection_trace_finite P'.epsilon_pos (by omega : 1≤P'.s+3) e
  have hI : (trace volume (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N)
      P'.epsilon_pos (by omega : 1≤P'.s+3) e x).starProjection)).toReal=I := by
    dsimp only [I,Qcan]
    rw [cover.regularProjection_trace]
  refine ⟨C,D,K,Kreg,hC,hD,hK,hKreg,?_⟩
  intro n
  obtain ⟨E,hmass,hmatrix,hphysical,hregular,hfinite,htrace,hsource,hfix⟩ := hfilter n
  refine ⟨E,hmass,hmatrix,hphysical,hregular,hfinite,hsource,?_⟩
  intro B L hL hmB hcB hnB
  have herror (x : ℍ) (hx : FreeRegularFamily.free x) :
      ‖regularSum E x*Qcan x-Qcan x‖≤Real.sqrt (Kreg/(2:ℝ)^n) :=
    Real.le_sqrt_of_sq_le (hfix x hx)
  have hh := FreeRegularFamily.weighted_excess B (regularSum E) Qcan hmB
    (regularSum_matrix_measurable E) hQr.1 hcB (regularSum_covariant E) hQr.2
    hregular hQp hfinite hQf hL (Real.sqrt_nonneg _) hnB herror
  rw [hI] at htrace
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hL
  change signedTrace volume (regularSum E)-I+4*Real.sqrt (Kreg/(2:ℝ)^n)*I≤_
  linarith

#print axioms exists_bounded_weighted_canonical_filter
end QuantitativeMaass.RawCommonReconstruction
