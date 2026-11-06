module

public import AsymptoticClassicalMultiplicityDimensionV1
public import AsymptoticClassicalFrickeIsometryV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

/-- The even-weight Fricke involution as an actual Petersson isometry. -/
def frickeEvenIsometry (N : ℕ) [NeZero N] (hN : 0 < N) (k : ℕ) (hk : Even k) :
    CuspForm (level N) (k : ℤ) ≃ₗᵢ[ℂ] CuspForm (level N) (k : ℤ) :=
  (LinearEquiv.ofInvolutive (frickeOperator N hN (k : ℤ))
    (frickeOperator_involutive N hN k hk)).isometryOfInner
      (inner_frickeOperator N hN (k : ℤ))

theorem fricke_partial_projection (N : ℕ) [NeZero N] (hN : 0 < N)
    (k : ℕ) (hk : Even k) (S : Set ℕ) (f : CuspForm (level N) (k : ℤ)) :
    (partialNewSpace N hN (k : ℤ) S).starProjection (frickeOperator N hN (k : ℤ) f) =
      frickeOperator N hN (k : ℤ) ((partialNewSpace N hN (k : ℤ) S).starProjection f) := by
  apply projection_intertwine_of_adjoint _ _ _ (frickeOperator N hN (k : ℤ))
  · intro y x
    have he := inner_frickeOperator N hN (k : ℤ) y (frickeOperator N hN (k : ℤ) x)
    rw [frickeOperator_involutive N hN k hk x] at he
    exact he
  · exact fun x hx => frickeOperator_mem_partialNewSpace N hN (k : ℤ) S x hx
  · exact fun x hx => frickeOperator_mem_partialNewSpace N hN (k : ℤ) S x hx

/-- Global Fricke carries the ordinary old image exactly onto the second old image. -/
theorem fricke_map_old_range (N M : ℕ) [NeZero N] [NeZero M] (hN : 0 < N)
    (hMN : M ∣ N) (k : ℕ) (hk : Even k) :
    (LinearMap.range (restrict (k : ℤ) (level_antitone hMN))).map
      (frickeOperator N hN (k : ℤ)) =
      LinearMap.range (restrict (k : ℤ) (level_le_frickeOldLevel hN hMN)) := by
  let A := LinearMap.range (restrict (k : ℤ) (level_antitone hMN))
  let B := LinearMap.range (restrict (k : ℤ) (level_le_frickeOldLevel hN hMN))
  have he : Aᗮ.map (frickeOperator N hN (k : ℤ)) = Bᗮ := by
    rw [← trace_kernel_eq_orthogonal N M (k : ℤ) hMN,
      ← fricke_trace_kernel_eq_orthogonal N M hN (k : ℤ) hMN]
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      apply (fricke_trace_swap_zero_iff N M hN (k : ℤ) (frickeOperator N hN (k : ℤ) g)).mp
      simpa only [frickeOperator_involutive N hN k hk g] using (LinearMap.mem_ker.mp hg)
    · intro hf
      refine ⟨frickeOperator N hN (k : ℤ) f, ?_, frickeOperator_involutive N hN k hk f⟩
      exact (fricke_trace_swap_zero_iff N M hN (k : ℤ) f).mpr hf
  have hm := A.map_orthogonal_equiv (frickeEvenIsometry N hN k hk)
  change Aᗮ.map (frickeOperator N hN (k : ℤ)) =
    (A.map (frickeOperator N hN (k : ℤ)))ᗮ at hm
  have hh := congrArg (fun U : Submodule ℂ (CuspForm (level N) (k : ℤ)) => Uᗮ)
    (hm.symm.trans he)
  simpa only [Submodule.orthogonal_orthogonal] using hh

#print axioms frickeEvenIsometry
#print axioms fricke_partial_projection
#print axioms fricke_map_old_range

end AsymptoticClassicalCusp
