module

public import AsymptoticClassicalFiniteDimensionV1
public import AsymptoticProjectiveCongruenceIndexV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticCongruenceStrip
open scoped ModularForm MatrixGroups

/-- The norm degree in the classical GL model is exactly the congruence
 index appearing in the already proved analytic coefficient. -/
theorem norm_degree_eq_index (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (level N).subgroupOf 𝒮ℒ) = (gamma N).relIndex (gamma 1) := by
  have h1 : CongruenceSubgroup.Gamma0 1 = ⊤ := by
    ext A
    simp only [CongruenceSubgroup.Gamma0_mem, Subgroup.mem_top, iff_true]
    exact Subsingleton.elim _ _
  rw [gamma_relIndex, h1]
  change (CongruenceSubgroup.Gamma0 N |>.map (SpecialLinearGroup.mapGL ℝ)).relIndex
    (SpecialLinearGroup.mapGL ℝ).range = _
  rw [MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ SpecialLinearGroup.mapGL_injective]

/-- An explicit classical dimension bound in the same index normalization
 as the summed incidence theorem. -/
theorem modular_dimension_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (ModularForm (level N) k) ≤
      (k * (gamma N).relIndex (gamma 1)).toNat / 12 + 1 := by
  have hh := LinearMap.finrank_le_finrank_of_injective
    (AsymptoticClassicalNorm.fourierJet_injective (level_one_period N) k (level_le_SL N))
  simpa only [Module.finrank_pi, Fintype.card_fin, norm_degree_eq_index] using hh

theorem cusp_dimension_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm (level N) k) ≤
      (k * (gamma N).relIndex (gamma 1)).toNat / 12 + 1 := by
  exact (LinearMap.finrank_le_finrank_of_injective
    (CuspForm.toModularFormₗ_injective (Γ := level N) (k := k))).trans
      (modular_dimension_le N k)

theorem new_dimension_le (N : ℕ) (hN : 0 < N) (k : ℤ) :
    Module.finrank ℂ (newSpace N hN k) ≤
      (k * (gamma N).relIndex (gamma 1)).toNat / 12 + 1 := by
  let : NeZero N := ⟨hN.ne'⟩
  exact (LinearMap.finrank_le_finrank_of_injective
    (newSpace N hN k).injective_subtype).trans (cusp_dimension_le N k)

#print axioms norm_degree_eq_index
#print axioms modular_dimension_le
#print axioms cusp_dimension_le
#print axioms new_dimension_le

end AsymptoticClassicalCusp
