module

public import AsymptoticClassicalCuspInjectionV1
public import AsymptoticClassicalDimensionBoundV1
public import AsymptoticClassicalLevelOneDimensionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open UpperHalfPlane AsymptoticClassicalCusp AsymptoticCongruenceStrip
open AsymptoticClassicalDiscriminant
open scoped MatrixGroups

/-- The number of integral congruence cosets equals the index used in
 the analytic asymptotic coefficient. -/
theorem integral_coset_card (N : ℕ) :
    Nat.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) =
      (gamma N).relIndex (gamma 1) := by
  have h1 : CongruenceSubgroup.Gamma0 1 = ⊤ := by
    ext A
    simp only [CongruenceSubgroup.Gamma0_mem, Subgroup.mem_top, iff_true]
    exact Subsingleton.elim _ _
  rw [gamma_relIndex, h1, Subgroup.relIndex_top_right, Subgroup.index_eq_card]

/-- An explicit injection gives the full cusp-space lower bound at
 every positive level. No dimension formula for sign sectors is used. -/
theorem cusp_dimension_lower (N : ℕ) (hN : 0 < N) (w : ℤ) :
    (gamma N).relIndex (gamma 1) * Module.finrank ℂ (ModularForm 𝒮ℒ w) ≤
      Module.finrank ℂ (CuspForm (level N)
        (12 * ((gamma N).relIndex (gamma 1) : ℤ) + w)) := by
  let : NeZero N := ⟨hN.ne'⟩
  let Q := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N
  let := Fintype.ofFinite Q
  have hc : Fintype.card Q = (gamma N).relIndex (gamma 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact integral_coset_card N
  let e := (Fintype.equivFinOfCardEq hc).symm
  have hh := LinearMap.finrank_le_finrank_of_injective
    (familyMap_injective N hN ((gamma N).relIndex (gamma 1)) w e)
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using hh

#print axioms integral_coset_card
#print axioms cusp_dimension_lower

end AsymptoticClassicalDimension
