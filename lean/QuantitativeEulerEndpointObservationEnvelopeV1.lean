module

public import QuantitativeEulerEndpointObservationGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeNewGap QuantitativeSpectralObservability
open QuantitativeSpectralExceptionalReducedRows
open scoped Classical MatrixGroups

/-- The bound for the entire original observation family is fixed before
choosing the height, number of blocks or auxiliary cap exponent. -/
theorem exists_sector_observation_envelope (N : ℕ) (hN : 0<N) (sector : Sector N)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B ε : ℝ) :
    ∃ M : ℝ, 4≤M ∧ ∀ V : ℝ, M≤V → ∀ H : ℝ, |H|≤V → ∀ t : ℕ,
      sectorObservationCost N hN sector S hS W B H ε t≤V^(7+72*t) := by
  let f : Fin 6 ⊕ (SectorFamilyIndex N × Fin 3) → ℝ
    | .inl i => ![4,|B|,|ε|,|terminalObservationConstant S W|,
        |(sectorGap N hN)⁻¹|,(Fintype.card (SectorFamilyIndex N):ℝ)] i
    | .inr (i,j) => ![|sectorFamilyL N hN sector S hS i|,
        |sectorFamilyK N hN sector S hS i|,|(sectorFamilyC N hN sector S hS i)⁻¹|] j
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  have hf (i) : f i≤M := hM ⟨i,rfl⟩
  have h4 : 4≤M := hf (.inl 0)
  refine ⟨M,h4,?_⟩
  intro V hV H hH t
  exact sector_observation_power_bound N hN sector S hS W B H ε V t (h4.trans hV)
    ((hf (.inl 1)).trans hV) hH ((hf (.inl 2)).trans hV)
    ((hf (.inl 3)).trans hV) ((hf (.inl 4)).trans hV) ((hf (.inl 5)).trans hV)
    (fun i => (hf (.inr (i,0))).trans hV) (fun i => (hf (.inr (i,1))).trans hV)
    (fun i => (hf (.inr (i,2))).trans hV)

#print axioms exists_sector_observation_envelope
end QuantitativeEulerEndpointPrepared
