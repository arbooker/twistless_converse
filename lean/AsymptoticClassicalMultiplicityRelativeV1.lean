module

public import AsymptoticClassicalMultiplicityFrickeV1
public import AsymptoticClassicalOldIntersectionSimpleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

/-- Adding one prime-new condition intersects the existing partial newspace
 with its actual paired trace kernel. -/
theorem partialNewSpace_insert (N : ℕ) (hN : 0 < N) (k : ℤ) (S : Set ℕ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) :
    partialNewSpace N hN k (insert p.val S) =
      primeTraceKernel N hN k p ⊓ partialNewSpace N hN k S := by
  ext f
  simp only [mem_partialNewSpace, Set.mem_insert_iff, Submodule.mem_inf]
  constructor
  · intro hf
    exact ⟨hf p (Or.inl rfl), fun q hq => hf q (Or.inr hq)⟩
  · rintro ⟨hp, hS⟩ q (hq | hq)
    · have he : q = p := Subtype.ext hq
      simpa only [he] using hp
    · exact hS q hq

/-- An injective map preserves the dimension of every subspace. -/
theorem finrank_map_of_injective {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℂ E] [Module ℂ F] (U : Submodule ℂ E) (L : E →ₗ[ℂ] F)
    (hL : Function.Injective L) : Module.finrank ℂ (U.map L) = Module.finrank ℂ U := by
  have he : LinearMap.range (L.comp U.subtype) = U.map L := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← he]
  exact LinearMap.finrank_range_of_inj (hL.comp Subtype.val_injective)

/-- The ordinary old image inside a partial newspace has the lower-level
 partial-new dimension. -/
theorem restrict_partial_finrank (M p : ℕ) [NeZero M] (hM : 0 < M) (hp : p.Prime)
    (k : ℤ) (S : Set ℕ) (hpS : p ∉ S) :
    Module.finrank ℂ ↥(LinearMap.range (restrict k (level_antitone (Nat.dvd_mul_left M p))) ⊓
      partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) k S) =
      Module.finrank ℂ (partialNewSpace M hM k S) := by
  rw [← restrict_partial_range M p hM hp k S hpS]
  exact finrank_map_of_injective _ _ (restrict_injective k _)

/-- Global Fricke transports intersections with partial newspaces. -/
theorem fricke_map_inf_partial (N : ℕ) [NeZero N] (hN : 0 < N)
    (k : ℕ) (hk : Even k) (S : Set ℕ) (A : Submodule ℂ (CuspForm (level N) (k : ℤ))) :
    (A ⊓ partialNewSpace N hN (k : ℤ) S).map (frickeOperator N hN (k : ℤ)) =
      A.map (frickeOperator N hN (k : ℤ)) ⊓ partialNewSpace N hN (k : ℤ) S := by
  ext f
  constructor
  · rintro ⟨g, ⟨hgA, hgV⟩, rfl⟩
    exact ⟨⟨g, hgA, rfl⟩, frickeOperator_mem_partialNewSpace N hN (k : ℤ) S g hgV⟩
  · rintro ⟨⟨g, hg, rfl⟩, hf⟩
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩
    change g ∈ partialNewSpace N hN (k : ℤ) S
    have hh := frickeOperator_mem_partialNewSpace N hN (k : ℤ) S _ hf
    simpa only [frickeOperator_involutive N hN k hk g] using hh

/-- Both old images have equal dimensions inside every partial newspace. -/
theorem fricke_old_partial_finrank (N M : ℕ) [NeZero N] [NeZero M] (hN : 0 < N)
    (hMN : M ∣ N) (k : ℕ) (hk : Even k) (S : Set ℕ) :
    Module.finrank ℂ ↥(LinearMap.range
      (restrict (k : ℤ) (level_le_frickeOldLevel hN hMN)) ⊓ partialNewSpace N hN (k : ℤ) S) =
    Module.finrank ℂ ↥(LinearMap.range
      (restrict (k : ℤ) (level_antitone hMN)) ⊓ partialNewSpace N hN (k : ℤ) S) := by
  rw [← fricke_map_old_range N M hN hMN k hk, ← fricke_map_inf_partial N hN k hk]
  exact finrank_map_of_injective _ _ (frickeOperator_involutive N hN k hk).injective

#print axioms partialNewSpace_insert
#print axioms finrank_map_of_injective
#print axioms restrict_partial_finrank
#print axioms fricke_map_inf_partial
#print axioms fricke_old_partial_finrank

end AsymptoticClassicalCusp
