module

public import QuantitativeMaassCanonicalParityDecompositionV1
public import QuantitativeMaassColumnLinearTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap AsymptoticClassicalPetersson AsymptoticSectorSigns
namespace QuantitativeMaass

/-- The original canonical new/sign projection is the sum of its two
orthogonal parity projections, on the original quotient Hilbert space. -/
theorem canonicalProjection_parity_sum (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) (e : Sector N) (σ : ℝ) (hσ : σ^2=1) :
    (completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e)).starProjection=
      (completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) σ).starProjection+
      (completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) (-σ)).starProjection := by
  apply projection_add_of_orthogonal_decomposition
    (completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e))
    (completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) σ)
    (completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) (-σ))
    inf_le_left inf_le_left
  · intro x hx y hy
    have hx' := (mem_completedParitySpace N σ x).mp hx.2
    have hy' := (mem_completedParitySpace N (-σ) y).mp hy.2
    have hy0 : parityProjection N σ y=0 := by
      have hh := parityProjection_add_neg N σ y
      rw [hy'] at hh
      exact add_right_cancel (hh.trans (zero_add y).symm)
    have hh := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (parityProjection_selfAdjoint N σ)) x y
    change inner ℂ (parityProjection N σ x) y=inner ℂ x (parityProjection N σ y) at hh
    simpa only [hx',hy0,inner_zero_right] using hh
  · intro x hx
    refine ⟨parityProjection N σ x,⟨completedSectorNewSign_parity N hN e σ x hx,
      (mem_completedParitySpace N σ _).mpr (parityProjection_idempotent N σ hσ x)⟩,
      parityProjection N (-σ) x,⟨completedSectorNewSign_parity N hN e (-σ) x hx,
      (mem_completedParitySpace N (-σ) _).mpr
        (parityProjection_idempotent N (-σ) (by simpa only [neg_sq] using hσ) x)⟩,
      (parityProjection_add_neg N σ x).symm⟩

/-- Integration of the two parity pieces uses the actual square-integrable
column; no formal splitting of a nonintegrable trace is used. -/
theorem columnLinearTrace_canonical_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (N : ℕ) [NeZero N] (hN : GridAdmissibleGap.Admissible N)
    (e : Sector N) (σ : ℝ) (hσ : σ^2=1)
    (c : α→AutomorphicSpace N) (hc : MemLp c 2 μ) :
    columnLinearTrace μ c (completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e)).starProjection=
      columnLinearTrace μ c
        (completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) σ).starProjection+
      columnLinearTrace μ c
        (completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) (-σ)).starProjection := by
  rw [canonicalProjection_parity_sum N hN e σ hσ]
  unfold columnLinearTrace
  simp only [add_apply,inner_add_left,Complex.add_re]
  exact integral_add (columnLinearTrace_integrable μ c hc _)
    (columnLinearTrace_integrable μ c hc _)

#print axioms canonicalProjection_parity_sum
#print axioms columnLinearTrace_canonical_sum
end QuantitativeMaass
