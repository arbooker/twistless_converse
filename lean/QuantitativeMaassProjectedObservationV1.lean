module

public import QuantitativeMaassColumnParityGramV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
namespace QuantitativeMaass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An observed Gram operator with both input and output supported in the
specified closed subspace. The filter need not preserve that subspace. -/
def projectedObservation (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (F O : H→L[ℂ]H) : H→L[ℂ]H :=
  P.starProjection.comp (F.adjoint.comp (O.comp (F.comp P.starProjection)))

theorem projectedObservation_left (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (F O : H→L[ℂ]H) :
    P.starProjection * projectedObservation P F O = projectedObservation P F O := by
  change P.starProjection.comp (projectedObservation P F O)=_
  unfold projectedObservation
  rw [←comp_assoc,Submodule.starProjection_comp_starProjection_of_le (le_refl P)]

theorem projectedObservation_right (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (F O : H→L[ℂ]H) :
    projectedObservation P F O * P.starProjection = projectedObservation P F O := by
  change (projectedObservation P F O).comp P.starProjection=_
  unfold projectedObservation
  simp only [comp_assoc,Submodule.starProjection_comp_starProjection_of_le (le_refl P)]

theorem projectedObservation_norm (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (F O : H→L[ℂ]H) (hO : ‖O‖≤1) :
    ‖projectedObservation P F O‖≤‖F‖^2 := by
  apply opNorm_le_bound _ (sq_nonneg ‖F‖)
  intro v
  calc
    _ ≤ ‖F.adjoint (O (F (P.starProjection v)))‖ := P.norm_starProjection_apply_le _
    _ ≤ ‖F.adjoint‖*‖O (F (P.starProjection v))‖ := F.adjoint.le_opNorm _
    _ ≤ ‖F‖*(‖O‖*(‖F‖*‖v‖)) := by
      rw [adjoint.norm_map]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg F)
      apply (O.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg O)
      exact (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (P.norm_starProjection_apply_le v) (norm_nonneg F))
    _ ≤ ‖F‖*(1*(‖F‖*‖v‖)) := by gcongr
    _ = _ := by ring

theorem columnLinearTrace_projectedObservation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α→H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (F O : H→L[ℂ]H) :
    columnLinearTrace μ c (projectedObservation P F O) =
      columnLinearTrace μ (fun z => F (P.starProjection (c z))) O := by
  rw [columnLinearTrace_filtered,columnLinearTrace_filtered]
  simp only [projectedObservation,(isSelfAdjoint_starProjection P).adjoint_eq,
    comp_assoc]

#print axioms projectedObservation_left
#print axioms projectedObservation_right
#print axioms projectedObservation_norm
#print axioms columnLinearTrace_projectedObservation
end QuantitativeMaass
