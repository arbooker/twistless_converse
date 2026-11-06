module

public import QuantitativeEulerEndpointTerminalGramV1
public import QuantitativeEulerEndpointNestedPhysicalV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointTerminalAlgebra
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointRegularBase QuantitativeHolomorphic
open AsymptoticRegularTrace AsymptoticFiniteBranch AsymptoticCompactObservationCount
open MeasureTheory

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A) (e : Sector N)

/-- The regular realization of the same original observation used in the physical filter. -/
def observation (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s) :=
  regularSum (rowExpression hN r e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4))

theorem observation_norm (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s) (z : Base) :
    ‖observation A hN P e r hs z‖≤rowBound hN r hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) := by
  rw [observation,regularSum_rowExpression]
  exact regular_row_norm_le_physical_bound _ _ _ _ _ _ _

def observationGram (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s) : Algebra A P :=
  normalizedGram A hN P e (observation A hN P e r hs)
    (regularSum_matrix_measurable _) (regularSum_covariant _)
    (rowBound hN r hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4)) (observation_norm A hN P e r hs)

theorem observationGram_nonneg (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s) :
    0≤observationGram A hN P e r hs := normalizedGram_nonneg _ _ _ _ _ _ _ _ _

theorem observationGram_norm (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s) :
    ‖observationGram A hN P e r hs‖≤(rowBound hN r hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4))^2 :=
  normalizedGram_norm _ _ _ _ _ _ _ _ _

variable {ι : Type*} (qs : Finset ι) (r : ι → Row N)
  (s : ι → Set UpperHalfPlane) (hs : ∀ i,IsCompact (s i))

def observationEnergy : Algebra A P :=
  (normalizedObservationBound A hN P qs r s hs)⁻¹ • ∑ i∈qs,observationGram A hN P e (r i) (hs i)

theorem observation_energy_order :
    0≤observationEnergy A hN P e qs r s hs ∧ observationEnergy A hN P e qs r s hs≤1 := by
  let G : Algebra A P := ∑ i∈qs,observationGram A hN P e (r i) (hs i)
  have hG0 : 0≤G := Finset.sum_nonneg (fun i _ => observationGram_nonneg A hN P e (r i) (hs i))
  have hn : ‖G‖≤normalizedObservationBound A hN P qs r s hs := by
    apply (norm_sum_le _ _).trans
    have hh := Finset.sum_le_sum (fun i (_ : i∈qs) => observationGram_norm A hN P e (r i) (hs i))
    exact hh.trans (by unfold normalizedObservationBound; linarith)
  have hG1 : G≤normalizedObservationBound A hN P qs r s hs • 1 := by
    calc
      G≤algebraMap ℝ (Algebra A P) ‖G‖ := IsSelfAdjoint.le_algebraMap_norm_self _ (IsSelfAdjoint.of_nonneg hG0)
      _ = ‖G‖ • (1 : Algebra A P) := _root_.Algebra.algebraMap_eq_smul_one _
      _ ≤ _ := smul_le_smul_of_nonneg_right hn zero_le_one
  exact QuantitativeEulerEndpointNestedOperator.scaled_energy_order G _
    (normalizedObservationBound_pos A hN P qs r s hs) ⟨hG0,hG1⟩

/-- The energy has the exact original-row Gram representation; normalization
acts only on terminal coordinates, and the outputs are not cut to a band. -/
theorem rep_observationEnergy (z : Base) : rep A P (observationEnergy A hN P e qs r s hs) z=
    (normalizedObservationBound A hN P qs r s hs)⁻¹ •
      ∑ i∈qs,(normalizedRow A hN P e (observation A hN P e (r i) (hs i)) z).adjoint.comp
        (normalizedRow A hN P e (observation A hN P e (r i) (hs i)) z) := by
  simp only [observationEnergy,map_smul,map_sum,Pi.smul_apply,Finset.sum_apply]
  rfl

#print axioms observationGram_nonneg
#print axioms observationGram_norm
#print axioms observation_energy_order
#print axioms rep_observationEnergy
end QuantitativeEulerEndpointTerminalAlgebra
