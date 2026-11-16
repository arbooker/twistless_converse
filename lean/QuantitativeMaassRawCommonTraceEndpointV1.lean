module

public import QuantitativeMaassRawCommonRegularTraceV1
public import QuantitativeMaassRawReconstructedFilterCostV1
public import QuantitativeEulerDensityGeneratorsV1

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open MeasureTheory ContinuousLinearMap AsymptoticFiniteBranch AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeEulerDensityGenerators RawBoundedIteration
open scoped Classical MatrixGroups

theorem horizon_reconstruction_error {K : ℝ} (hK : 0≤K) (n : ℕ) :
    Real.exp (-8*Real.exp ((K+1)*(4:ℝ)^n))≤1/(4:ℝ)^n := by
  have hx : 0<(4:ℝ)^n := by positivity
  have he := Real.add_one_le_exp ((K+1)*(4:ℝ)^n)
  have hs : (4:ℝ)^n≤Real.exp ((K+1)*(4:ℝ)^n) := by
    nlinarith only [he,mul_nonneg hK hx.le]
  have hh := Real.add_one_le_exp (8*Real.exp ((K+1)*(4:ℝ)^n))
  have hl : (4:ℝ)^n≤Real.exp (8*Real.exp ((K+1)*(4:ℝ)^n)) := by
    nlinarith only [hh,hs,hx]
  rw [show -8*Real.exp ((K+1)*(4:ℝ)^n)=-(8*Real.exp ((K+1)*(4:ℝ)^n)) by ring,
    Real.exp_neg,←one_div]
  exact one_div_le_one_div_of_le hx hl

/-- A literal finite expression simultaneously controls the physical
original source and the regular incidence trace. All arithmetic blocks,
generators, reconstruction accuracies and filters have been constructed.
The canonical projection is retained exactly; this is not yet its finite
trace approximation or the original counting asymptotic. -/
theorem exists_common_trace_expression {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A) (hN2 : 2≤N) (e : Sector N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let V := (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).toContinuousLinearMap
    let M := (trace volume (fun x =>
      (AsymptoticQuotientIncidence.space N (NeZero.pos N) P'.epsilon_pos
        (by omega : 1≤P'.s+3) e x).starProjection)).toReal
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀ n : ℕ,∃ E : Expression,
      expressionBound E≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound E (Real.exp (Real.exp (C*(4:ℝ)^n))) ∧
      (∀ Y H : ℝ,signedTrace volume (regularSum (retainedExpression Y H E))≤M+D/(4:ℝ)^n) ∧
      ∀ (μ : Measure UpperHalfPlane) (c : UpperHalfPlane→AsymptoticHyperbolicSlash.Space),
        MemLp c 2 μ →
        ∀ Qtarget : AsymptoticHyperbolicSlash.Space→L[ℂ]AsymptoticHyperbolicSlash.Space,
        columnLinearTrace μ c (V.comp ((terminalSourceProjection A P e).comp V.adjoint)-Qtarget)≤
          columnLinearTrace μ c (holomorphicSum E 0-Qtarget)+
            (7/(4:ℝ)^n)*(∫ x,‖c x‖^2 ∂μ) := by
  intro P' V M
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
    exists_actual_common_filter A P hN2 e 0 S hS
  obtain ⟨Ka,Kc,hKa,hKc,hall⟩ := hfilters H₀ hH₀ hdata
  obtain ⟨C,hC,hcost⟩ := exists_horizon_sandwich_cost A P hKa hKc
  let J := Real.exp ((8:ℝ)/3+8)*(P'.ε⁻¹+4*(1+P'.ε⁻¹*Real.log 2))
  let D := (sectorTailConstant N (NeZero.pos N) e S hS+1)/H₀+J+2*P'.ε⁻¹
  have hJ : 0≤J := by
    have he := P'.epsilon_pos
    have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [J]
    positivity
  have hD : 0≤D := by
    have ht := sectorTailConstant_nonneg N (NeZero.pos N) e S hS
    have he := P'.epsilon_pos
    dsimp only [D]
    positivity
  refine ⟨C,D,hC,hD,?_⟩
  intro n
  obtain ⟨F,z,hi,hvalid,hrec,hfix,htrace,hmass,hmatrix,happrox,hphysical⟩ := hall n
  let excluded := reconstructionExclusions N Q
  let G := generatorTransportConstant (QuantitativeEulerEndpointPrepared.prepared N hN2 excluded 0)
  let s := Real.exp ((Ka+1)*(4:ℝ)^n)
  let T := actualFiniteExpression A P e hN2 excluded 0 S hS W Bobs Bg D₀ H₀ G C₀ Kobs n s z
  let E := reconstructedFilterExpression A P e s T
  have hcost' := hcost n e T hmass hmatrix
  refine ⟨E,hcost'.1,hcost'.2,?_,?_⟩
  · intro Y H
    have ho (x : UpperHalfPlane) : 0≤regularSum T x ∧ regularSum T x≤1 := by
      have hh := actualFiniteExpression_regular_order A P e hN2 excluded 0 S hS W Bobs Bg D₀ H₀ G C₀ Kobs
        n s z (fun j hj => (hrec j hj).1.scalar) x
      exact ⟨hh.1,hh.2.1⟩
    have ht := retained_regular_le_terminal A P (NeZero.pos N) s e (F n)
      ⟨(hvalid n le_rfl).nonneg,(hvalid n le_rfl).le_one⟩ T ho (2/(4:ℝ)^n) happrox Y H
    change signedTrace volume (regularSum (retainedExpression Y H E))≤_ at ht
    apply ht.trans
    apply (add_le_add htrace le_rfl).trans
    change M+sectorTailConstant N (NeZero.pos N) e S hS/(H₀*(4:ℝ)^n)+
      (H₀*(4:ℝ)^n)⁻¹+J/(4:ℝ)^n+(2/(4:ℝ)^n)*P'.ε⁻¹≤M+D/(4:ℝ)^n
    dsimp only [D]
    exact le_of_eq (by ring)
  · intro μ c hc Qtarget
    have hn : ‖holomorphicSum T 0‖≤1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hphysical.1.1).mpr hphysical.1.2.1
    have hh := original_source_finite_column_trace A P e μ c hc s T hphysical.1.1 hn Qtarget hphysical.2
    apply hh.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ => sq_nonneg _))
    have he := horizon_reconstruction_error hKa n
    change 3*(2/(4:ℝ)^n)+Real.exp (-8*s)≤7/(4:ℝ)^n
    dsimp only [s]
    calc
      _ ≤ 3*(2/(4:ℝ)^n)+1/(4:ℝ)^n := add_le_add le_rfl he
      _ = _ := by ring

#print axioms horizon_reconstruction_error
#print axioms exists_common_trace_expression
end QuantitativeMaass.RawCommonReconstruction
