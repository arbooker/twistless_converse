module

public import QuantitativeMaassApproximateSandwichTraceV1
public import QuantitativeMaassRawOriginalProjectionStructureV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns ContinuousLinearMap
open AsymptoticFiniteBranch MeasureTheory
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

def reconstructedFilterExpression (s : ℝ) (T : Expression) : Expression :=
  composeExpression (expression A P (NeZero.pos N) s e)
    (composeExpression T (adjointExpression (expression A P (NeZero.pos N) s e)))

theorem reconstructedFilterExpression_physical (s : ℝ) (T : Expression) :
    holomorphicSum (reconstructedFilterExpression A P e s T) 0=
      (holomorphicSum (expression A P (NeZero.pos N) s e) 0).comp
        ((holomorphicSum T 0).comp (holomorphicSum (expression A P (NeZero.pos N) s e) 0).adjoint) := by
  simp only [reconstructedFilterExpression,holomorphicSum_compose,holomorphicSum_adjoint]

theorem reconstructedFilterExpression_regular (s : ℝ) (T : Expression) (x : UpperHalfPlane) :
    regularSum (reconstructedFilterExpression A P e s T) x=
      (regularSum (expression A P (NeZero.pos N) s e) x).comp
        ((regularSum T x).comp (regularSum (expression A P (NeZero.pos N) s e) x).adjoint) := by
  simp only [reconstructedFilterExpression,regularSum_compose,regularSum_adjoint]

/-- The exact original source excess is bounded by the actual reconstructed
finite expression minus the unchanged canonical target. -/
theorem original_source_finite_column_trace {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α→AsymptoticHyperbolicSlash.Space) (hc : MemLp c 2 μ)
    (s : ℝ) (T : Expression) (hT : 0≤holomorphicSum T 0) (hTn : ‖holomorphicSum T 0‖≤1)
    (Qtarget : AsymptoticHyperbolicSlash.Space→L[ℂ]AsymptoticHyperbolicSlash.Space)
    {δ : ℝ} (hδ : ‖holomorphicSum T 0*originalSourceProjection A P e-originalSourceProjection A P e‖≤δ) :
    let V := (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).toContinuousLinearMap
    columnLinearTrace μ c (V.comp ((terminalSourceProjection A P e).comp V.adjoint)-Qtarget)≤
      columnLinearTrace μ c (holomorphicSum (reconstructedFilterExpression A P e s T) 0-Qtarget)+
        (3*δ+Real.exp (-8*s))*(∫ x,‖c x‖^2 ∂μ) := by
  intro V
  rw [physicalExact_terminalSource_conjugate,reconstructedFilterExpression_physical]
  have he := physical_error A P (NeZero.pos N) s e
  change ‖holomorphicSum (expression A P (NeZero.pos N) s e) 0-physicalExact A P (NeZero.pos N) e‖≤Real.exp (-8*s)/2 at he
  rw [norm_sub_rev] at he
  have hh := columnLinearTrace_sandwich_approx_fixed μ c hc
    (originalSourceProjection A P e) (holomorphicSum T 0)
    (physicalExact A P (NeZero.pos N) e) (holomorphicSum (expression A P (NeZero.pos N) s e) 0) Qtarget
    (isSelfAdjoint_starProjection (originalSourceKernel A P e))
    (originalSourceKernel A P e).isIdempotentElem_starProjection
    (originalSourceProjection_norm A P e) hT hTn (physicalExact_norm A P (NeZero.pos N) e)
    (physical_norm A P (NeZero.pos N) s e) hδ he
  convert hh using 1
  ring

#print axioms reconstructedFilterExpression_physical
#print axioms reconstructedFilterExpression_regular
#print axioms original_source_finite_column_trace
end QuantitativeMaass.RawCommonReconstruction
