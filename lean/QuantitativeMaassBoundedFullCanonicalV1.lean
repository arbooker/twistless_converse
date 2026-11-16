module

public import QuantitativeMaassCanonicalFullTraceV1
public import QuantitativeMaassMetricHorizonCostV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped ENNReal
namespace QuantitativeMaass.RawCommonReconstruction
open MeasureTheory ContinuousLinearMap AsymptoticFiniteBranch AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic

/-- The entire common metric filter, including reconstruction and polynomial
transport, has the required finite coefficient and matrix bounds. This is an
original-source/canonical-regular/trace endpoint, not yet the counting asymptotic. -/
theorem exists_bounded_full_canonical_filter {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A) (hN2 : 2≤N) (e : Sector N)
    {hN : GridAdmissibleGap.Admissible N} (cover : AdmissibleScalarCover N hN) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let M := cover.metric P'.epsilon_pos (by omega : 1≤P'.s+3)
    let I := (trace volume (fun x =>
      (AsymptoticQuotientIncidence.space N (NeZero.pos N) P'.epsilon_pos
        (by omega : 1≤P'.s+3) e x).starProjection)).toReal
    ∃ C D K Kreg : ℝ,0≤C ∧ 0≤D ∧ 0≤K ∧ 0≤Kreg ∧ ∀ n : ℕ,∃ E : Expression,
      expressionBound E≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound E (Real.exp (Real.exp (C*(4:ℝ)^n))) ∧
      (0≤holomorphicSum E 0 ∧ holomorphicSum E 0≤1) ∧
      (∀ x,0≤regularSum E x ∧ regularSum E x≤1) ∧
      trace volume (regularSum E)<∞ ∧
      signedTrace volume (regularSum E)≤I+D/(2:ℝ)^n ∧
      ‖holomorphicSum E 0*(physicalMetricSource A P e M).starProjection-
        (physicalMetricSource A P e M).starProjection‖^2≤K/(2:ℝ)^n ∧
      ∀ x : UpperHalfPlane,Function.Injective (fun a : AsymptoticRationalGroup.Group => a • x) →
        let Qcan := cover.regularProjection P'.epsilon_pos (by omega : 1≤P'.s+3) e x
        ‖regularSum E x*Qcan-Qcan‖^2≤Kreg/(2:ℝ)^n := by
  intro P' M I
  obtain ⟨Ka,Kc,K,D,Kreg,hKa,hKc,hK,hD,hKreg,hfilter⟩ := exists_canonical_full_metric_expression A P hN2 e cover
  obtain ⟨B,hB,hsandwich⟩ := exists_horizon_sandwich_cost A P hKa hKc
  obtain ⟨C,hC,hmetric⟩ := exists_metric_horizon_cost [M.branch] hB
  refine ⟨C,D,K,Kreg,hC,hD,hK,hKreg,?_⟩
  intro n
  obtain ⟨T,hT,hTm,horder,hregular,hfinite,htrace,hsource,hcanonical⟩ := hfilter n
  let s := Real.exp ((Ka+1)*(4:ℝ)^n)
  let F := reconstructedFilterExpression A P e s T
  let E := physicalMetricFilterExpression A P e M s T (2^n)
  have hF := hsandwich n e T hT hTm
  have hE := hmetric n F hF.1 hF.2
  exact ⟨E,hE.1,hE.2,horder,hregular,hfinite,htrace,hsource,hcanonical⟩

#print axioms exists_bounded_full_canonical_filter
end QuantitativeMaass.RawCommonReconstruction
