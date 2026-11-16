module

public import QuantitativeMaassRawActualCommonBudgetV1
public import QuantitativeMaassCanonicalRegularMetricErrorV1
public import QuantitativeMaassRawMetricRegularTraceV1
public import QuantitativeMaassRawFinalDefectV1
public import QuantitativeMaassMetricHorizonBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open MeasureTheory ContinuousLinearMap AsymptoticFiniteBranch AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeEulerDensityGenerators RawBoundedIteration
open scoped Classical MatrixGroups ENNReal

/-- A common metric polynomial simultaneously recovers the actual original
source and has incidence-leading regular trace. The degree is chosen from
the same arithmetic horizon. Costs of the terminal input expression remain
explicit, and the same filter recovers the actual canonical regular projection. -/
theorem exists_canonical_full_metric_expression {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A) (hN2 : 2≤N) (e : Sector N)
    {hN : GridAdmissibleGap.Admissible N} (cover : AdmissibleScalarCover N hN) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let M := cover.metric P'.epsilon_pos (by omega : 1≤P'.s+3)
    let I := (trace volume (fun x =>
      (AsymptoticQuotientIncidence.space N (NeZero.pos N) P'.epsilon_pos
        (by omega : 1≤P'.s+3) e x).starProjection)).toReal
    ∃ Ka Kc C D Kreg : ℝ,0≤Ka ∧ 0≤Kc ∧ 0≤C ∧ 0≤D ∧ 0≤Kreg ∧ ∀ n : ℕ,∃ T : Expression,
      expressionBound T≤Real.exp (Real.exp (Kc*(4:ℝ)^n)) ∧
      ExpressionMatrixBound T (Real.exp (Real.exp (Kc*(4:ℝ)^n))) ∧
      let E := physicalMetricFilterExpression A P e M (Real.exp ((Ka+1)*(4:ℝ)^n)) T (2^n)
      (0≤holomorphicSum E 0 ∧ holomorphicSum E 0≤1) ∧
      (∀ x,0≤regularSum E x ∧ regularSum E x≤1) ∧
      trace volume (regularSum E)<∞ ∧
      signedTrace volume (regularSum E)≤I+D/(2:ℝ)^n ∧
      ‖holomorphicSum E 0*(physicalMetricSource A P e M).starProjection-
        (physicalMetricSource A P e M).starProjection‖^2≤C/(2:ℝ)^n ∧
      ∀ x : UpperHalfPlane,Function.Injective (fun a : AsymptoticRationalGroup.Group => a • x) →
        let Qcan := cover.regularProjection P'.epsilon_pos (by omega : 1≤P'.s+3) e x
        ‖regularSum E x*Qcan-Qcan‖^2≤Kreg/(2:ℝ)^n := by
  intro P' M I
  let S := observedGenerators N
  have hS := observedGenerators_closure N
  let H₀ := max (max P'.ε⁻¹ 4) (∑ i,|sectorFamilyB N (NeZero.pos N) e S hS i|)
  have hH₀ : max P'.ε⁻¹ 4≤H₀ := le_max_left _ _
  have hHpos : 0<H₀ := lt_of_lt_of_le (by norm_num : (0:ℝ)<4)
    ((le_max_right P'.ε⁻¹ 4).trans hH₀)
  have hdata (i) : sectorFamilyB N (NeZero.pos N) e S hS i≤H₀ := by
    apply (le_abs_self _).trans
    apply le_trans (Finset.single_le_sum (fun j _ => abs_nonneg (sectorFamilyB N (NeZero.pos N) e S hS j))
      (Finset.mem_univ i))
    exact le_max_right _ _
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D₀,hD₀,C₀,hC₀,Kobs,hKobs,hfilters⟩ :=
    exists_actual_common_filter_budget A P hN2 e 0 S hS
  obtain ⟨Ka,Kc,hKa,hKc,hall⟩ := hfilters H₀ hH₀ hdata
  let J := Real.exp ((8:ℝ)/3+8)*(P'.ε⁻¹+4*(1+P'.ε⁻¹*Real.log 2))
  let Dbase := (sectorTailConstant N (NeZero.pos N) e S hS+1)/H₀+J
  have hJ : 0≤J := by
    have he := P'.epsilon_pos
    have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [J]
    positivity
  have hDb : 0≤Dbase := by
    have ht := sectorTailConstant_nonneg N (NeZero.pos N) e S hS
    dsimp only [Dbase]
    positivity
  let K := ‖M.physicalChange.symm.toContinuousLinearMap‖^2
  let B := ‖M.physicalChange.toContinuousLinearMap‖^2
  let C := K/expressionMetricScale [M.branch]+9*K*B
  let D := Dbase+8+50*‖tr A P‖
  have hC : 0≤C := by
    dsimp only [C,K,B]
    exact add_nonneg (div_nonneg (sq_nonneg _) (expressionMetricScale_pos _).le) (by positivity)
  have hD : 0≤D := by dsimp only [D]; positivity
  let Kr := (M.lower⁻¹)^2
  let Br := M.upper^2
  let Kreg := Kr/expressionMetricScale [M.branch]+9*Kr*Br
  have hKreg : 0≤Kreg := by
    dsimp only [Kreg,Kr,Br]
    exact add_nonneg (div_nonneg (sq_nonneg _) (expressionMetricScale_pos _).le) (by positivity)
  refine ⟨Ka,Kc,C,D,Kreg,hKa,hKc,hC,hD,hKreg,?_⟩
  intro n
  obtain ⟨F,z,hi,hvalid,hrec,hfix,htrace,hbudget,hmass,hmatrix,happrox,hphysical⟩ := hall n
  let excluded := reconstructionExclusions N Q
  let G := generatorTransportConstant (QuantitativeEulerEndpointPrepared.prepared N hN2 excluded 0)
  let s := Real.exp ((Ka+1)*(4:ℝ)^n)
  let bs := actualBlock A P hN2 excluded 0 e S hS W Bobs Bg D₀ H₀ G C₀ Kobs n
  let T := actualFiniteExpression A P e hN2 excluded 0 S hS W Bobs Bg D₀ H₀ G C₀ Kobs n s z
  have ho (x : UpperHalfPlane) := actualFiniteExpression_regular_order A P e hN2 excluded 0 S hS
    W Bobs Bg D₀ H₀ G C₀ Kobs n s z (fun j hj => (hrec j hj).1.scalar) x
  have hl (x) : AsymptoticOrbitDiagonal.corner (terminalRegion A P) x*regularSum T x=regularSum T x := by
    have hh := (ho x).2.2.2.1
    rw [QuantitativeEulerEndpointTerminalExpression.unit_regular] at hh
    exact hh
  have hr (x) : regularSum T x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum T x := by
    have hh := (ho x).2.2.2.2
    rw [QuantitativeEulerEndpointTerminalExpression.unit_regular] at hh
    exact hh
  refine ⟨T,hmass,hmatrix,physicalMetricFilterExpression_order A P e M s T hphysical.1.1 hphysical.1.2.1 (2^n),
    physicalMetricFilterExpression_regular_order A P e M s T (fun x => ⟨(ho x).1,(ho x).2.1⟩) (2^n),
    physicalMetricFilterExpression_regular_finite A P e M s T (fun x => ⟨(ho x).1,(ho x).2.1⟩) hl hr (2^n),?_,?_,?_⟩
  · have hrange := actualBlock_range A P hN2 excluded 0 e S hS W Bobs Bg D₀ H₀ G C₀ Kobs hKobs n n
    have hdef := valid_final_defect A P e n bs hrange.1 hrange.2 (F n) (hvalid n le_rfl)
    have htr : tr A P (F n)≤I+Dbase/(4:ℝ)^n := by
      apply htrace.trans
      change I+sectorTailConstant N (NeZero.pos N) e S hS/(H₀*(4:ℝ)^n)+
        (H₀*(4:ℝ)^n)⁻¹+J/(4:ℝ)^n≤I+Dbase/(4:ℝ)^n
      dsimp only [Dbase]
      exact le_of_eq (by ring)
    have hh := physicalMetricFilterExpression_regular_trace A P e M s T
      (fun x => ⟨(ho x).1,(ho x).2.1⟩) hl hr (F n) (hvalid n le_rfl).nonneg
      (hvalid n le_rfl).le_one (show 0≤2/(4:ℝ)^n by positivity)
      (fun x => by simpa only [norm_sub_rev] using happrox x) (2^n)
    apply hh.trans
    have hd := mul_le_mul_of_nonneg_left hdef (show 0≤4*(((2^n:ℕ):ℝ)+1) by positivity)
    have hb := metric_horizon_trace_error hDb (norm_nonneg (tr A P)) n
    dsimp only [D]
    calc
      _ ≤ (I+Dbase/(4:ℝ)^n)+4*(((2^n:ℕ):ℝ)+1)*(1/(4:ℝ)^n)+
          (12*((2^n:ℕ):ℝ)+13)*‖tr A P‖*(2/(4:ℝ)^n) :=
        add_le_add (add_le_add htr hd) le_rfl
      _ = I+(Dbase/(4:ℝ)^n+4*(((2^n:ℕ):ℝ)+1)/(4:ℝ)^n+
          (12*((2^n:ℕ):ℝ)+13)*‖tr A P‖*(2/(4:ℝ)^n)) := by ring
      _ ≤ _ := add_le_add le_rfl hb
  · have hh := physicalMetricFilterExpression_source_error A P e M s T
      hphysical.1.1 hphysical.1.2.1 hphysical.2 (2^n)
    have hs : Real.exp (-8*s)≤1/(4:ℝ)^n := horizon_reconstruction_error hKa n
    have he : 2/(4:ℝ)^n+Real.exp (-8*s)≤3/(4:ℝ)^n := by
      calc
        _ ≤ 2/(4:ℝ)^n+1/(4:ℝ)^n := add_le_add le_rfl hs
        _ = _ := by ring
    have he' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (show 0≤3*K by dsimp only [K]; positivity))
      (show 0≤B by dsimp only [B]; positivity)
    have hb := metric_horizon_source_error (show 0≤K by dsimp only [K]; positivity)
      (show 0≤B by dsimp only [B]; positivity) (expressionMetricScale_pos [M.branch]) n
    exact hh.trans ((add_le_add le_rfl he').trans hb)

  · intro x hx Qcan
    have hh := actualFiniteExpression_canonical_metric_error A P e hN2 excluded 0 S hS
      W Bobs Bg D₀ H₀ G C₀ Kobs cover n hKa z
      (fun j hj => (hrec j hj).1.scalar) hbudget x hx (2^n)
    have hs : Real.exp (-8*s)≤1/(4:ℝ)^n := horizon_reconstruction_error hKa n
    have he : 2/(4:ℝ)^n+Real.exp (-8*s)≤3/(4:ℝ)^n := by
      calc
        _ ≤ 2/(4:ℝ)^n+1/(4:ℝ)^n := add_le_add le_rfl hs
        _ = _ := by ring
    have he' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (show 0≤3*Kr by dsimp only [Kr]; positivity))
      (show 0≤Br by dsimp only [Br]; positivity)
    have hb := metric_horizon_source_error (show 0≤Kr by dsimp only [Kr]; positivity)
      (show 0≤Br by dsimp only [Br]; positivity) (expressionMetricScale_pos [M.branch]) n
    exact hh.trans ((add_le_add le_rfl he').trans hb)

#print axioms exists_canonical_full_metric_expression
end QuantitativeMaass.RawCommonReconstruction
