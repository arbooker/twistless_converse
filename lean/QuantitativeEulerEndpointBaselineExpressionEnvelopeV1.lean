module

public import QuantitativeEulerEndpointMatrixGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns
open scoped Classical

/-- One fixed level-and-sector constant controls both masses and matrix
heights of all original baseline row expressions in every rectangle. -/
theorem exists_baseline_expression_envelope (N : ℕ) [NeZero N] (sector : Sector N) :
    ∃ M : ℝ, 4≤M ∧ ∀ U : ℝ, M≤U →
      (Fintype.card (NewBaselineIndex N):ℝ)≤U ∧
      ∀ R Y H : ℝ, 0≤R → R≤U → 0≤H → H≤U → 0<Y → (min 1 Y)⁻¹≤U →
      ∀ t : ℕ, ∀ i : NewBaselineIndex N,
        wideBaselineRowBound N sector R Y H t i≤36*9^t*U^(8+10*t) ∧
        baselineMatrixHeight N R Y H i≤36*U^10 := by
  let f : Fin 3 ⊕ (NewBaselineIndex N × Fin 2) → ℝ
    | .inl i => ![4,(N:ℝ),(Fintype.card (NewBaselineIndex N):ℝ)] i
    | .inr (i,j) => ![(baselineSize N i:ℝ),baselineAmplitude N sector i] j
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  have hf (i) : f i≤M := hM ⟨i,rfl⟩
  have hM4 : 4≤M := hf (.inl 0)
  refine ⟨M,hM4,?_⟩
  intro U hU
  refine ⟨(hf (.inl 2)).trans hU,?_⟩
  intro R Y H hR0 hR hH0 hH hY hYinv t i
  have hU1 : 1≤U := by linarith
  exact ⟨baseline_row_polynomial N sector R Y H U t hU1 ((hf (.inl 1)).trans hU)
    (fun j => (hf (.inr (j,0))).trans hU) (fun j => (hf (.inr (j,1))).trans hU)
    hR0 hR hH0 hH hY hYinv i,
    baseline_matrix_height_polynomial N R Y H U hU1 ((hf (.inl 1)).trans hU)
      (fun j => (hf (.inr (j,0))).trans hU) hR0 hR hH0 hH hY hYinv i⟩

#print axioms exists_baseline_expression_envelope
end QuantitativeEulerEndpointPrepared
