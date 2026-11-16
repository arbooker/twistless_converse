module

public import QuantitativeMaassRectangularColumnTraceV1
public import QuantitativeMaassMetricExcessPullbackV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
namespace QuantitativeMaass
variable {α H E ι : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem nested_projection_excess_cogram (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hVU : V≤U) :
    (U.starProjection-V.starProjection).comp (U.starProjection-V.starProjection).adjoint=
      U.starProjection-V.starProjection := by
  have hp : U.starProjection.comp V.starProjection=V.starProjection := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (hVU (V.starProjection_apply_mem x))
  have hq : V.starProjection.comp U.starProjection=V.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le hVU
  rw [map_sub,(isSelfAdjoint_starProjection U).adjoint_eq,
    (isSelfAdjoint_starProjection V).adjoint_eq,sub_comp,comp_sub,comp_sub,hp,hq]
  have hU : U.starProjection.comp U.starProjection=U.starProjection := U.isIdempotentElem_starProjection
  have hV : V.starProjection.comp V.starProjection=V.starProjection := V.isIdempotentElem_starProjection
  rw [hU,hV,sub_self,sub_zero]

/-- Pullback of the actual positive excess has a linear cogram, so it can
be compared to finite branches using the original square-integrable columns. -/
theorem metric_projection_excess_cogram (L : H≃L[ℂ]H)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hVU : V≤U) :
    let D := L.symm.toContinuousLinearMap
    (D.comp (U.starProjection-V.starProjection)).comp
      (D.comp (U.starProjection-V.starProjection)).adjoint=
      (D.comp U.starProjection).comp D.adjoint-(D.comp V.starProjection).comp D.adjoint := by
  intro D
  rw [adjoint_comp,comp_assoc,←comp_assoc (U.starProjection-V.starProjection),
    nested_projection_excess_cogram U V hVU]
  simp only [comp_sub,sub_comp,comp_assoc]

/-- Finite-energy output version of the metric excess estimate. It does
not assume the unrestricted cylinder wave operator is Hilbert--Schmidt. -/
theorem metric_column_excess_bound [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ) (b : HilbertBasis ι ℂ H)
    (L : H≃L[ℂ]H) (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hVU : V≤U)
    (C : Lp ℂ 2 μ→L[ℂ]E) :
    (∑' i,‖C (finiteEnergyColumnOperator μ c hc
      (L.symm ((U.starProjection-V.starProjection) (b i))))‖^2)≤
      ‖C‖^2*columnLinearTrace μ c
        ((L.symm.toContinuousLinearMap.comp U.starProjection).comp L.symm.toContinuousLinearMap.adjoint-
          (L.symm.toContinuousLinearMap.comp V.starProjection).comp L.symm.toContinuousLinearMap.adjoint) := by
  have hh := rectangular_column_output_bound μ c hc b
    (L.symm.toContinuousLinearMap.comp (U.starProjection-V.starProjection)) C
  rw [metric_projection_excess_cogram L U V hVU] at hh
  exact hh

#print axioms nested_projection_excess_cogram
#print axioms metric_projection_excess_cogram
#print axioms metric_column_excess_bound
end QuantitativeMaass
