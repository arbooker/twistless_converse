module

public import QuantitativeMaassCanonicalParitySpaceV1
public import QuantitativeMaassProjectedObservationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
namespace QuantitativeMaass

/-- Taking adjoints turns left support into right support. -/
theorem selfAdjoint_support_right {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P Q : H→L[ℂ]H)
    (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q) (h : P.comp Q=Q) :
    Q.comp P=Q := by
  have hh := congrArg (fun A : H→L[ℂ]H => A.adjoint) h
  simpa only [adjoint_comp,hP.adjoint_eq,hQ.adjoint_eq] using hh

variable (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) (σ : ℝ)

theorem canonicalParityProjection_cusp_left :
    (localCuspidalSpace N hN).starProjection.comp
      (completedNewSignParitySpace N hN χ σ).starProjection=
      (completedNewSignParitySpace N hN χ σ).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact (localCuspidalSpace N hN).starProjection_eq_self_iff.mpr
    (((completedNewSignParitySpace N hN χ σ).starProjection_apply_mem x).1.1)

theorem canonicalParityProjection_cusp_right :
    (completedNewSignParitySpace N hN χ σ).starProjection.comp
      (localCuspidalSpace N hN).starProjection=
      (completedNewSignParitySpace N hN χ σ).starProjection :=
  selfAdjoint_support_right _ _ (isSelfAdjoint_starProjection _)
    (isSelfAdjoint_starProjection _) (canonicalParityProjection_cusp_left N hN χ σ)

theorem canonicalParityProjection_parity_left :
    (parityProjection N σ).comp (completedNewSignParitySpace N hN χ σ).starProjection=
      (completedNewSignParitySpace N hN χ σ).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact (mem_completedParitySpace N σ _).mp
    (((completedNewSignParitySpace N hN χ σ).starProjection_apply_mem x).2)

theorem canonicalParityProjection_parity_right :
    (completedNewSignParitySpace N hN χ σ).starProjection.comp (parityProjection N σ)=
      (completedNewSignParitySpace N hN χ σ).starProjection :=
  selfAdjoint_support_right _ _ (parityProjection_selfAdjoint N σ)
    (isSelfAdjoint_starProjection _) (canonicalParityProjection_parity_left N hN χ σ)

/-- Parity can be inserted in the input of the original canonical trace
without changing that trace. -/
theorem columnLinearTrace_canonical_parity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α→AutomorphicSpace N) :
    columnLinearTrace μ (fun z => parityProjection N σ (c z))
      (completedNewSignParitySpace N hN χ σ).starProjection=
    columnLinearTrace μ c (completedNewSignParitySpace N hN χ σ).starProjection := by
  rw [columnLinearTrace_filtered,(parityProjection_selfAdjoint N σ).adjoint_eq,
    canonicalParityProjection_parity_right,canonicalParityProjection_parity_left]

#print axioms canonicalParityProjection_cusp_left
#print axioms canonicalParityProjection_cusp_right
#print axioms canonicalParityProjection_parity_left
#print axioms canonicalParityProjection_parity_right
#print axioms columnLinearTrace_canonical_parity
end QuantitativeMaass
