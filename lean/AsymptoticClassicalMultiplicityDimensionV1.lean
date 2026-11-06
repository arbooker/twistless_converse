module

public import AsymptoticClassicalMultiplicityProjectionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open scoped InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A projection preserving two old images distributes their sum over
 intersection with its range. -/
theorem inf_sup_of_projection (V A B : Submodule ℂ E) [CompleteSpace V]
    (hA : ∀ x ∈ A, V.starProjection x ∈ A)
    (hB : ∀ x ∈ B, V.starProjection x ∈ B) :
    (A ⊔ B) ⊓ V = (A ⊓ V) ⊔ (B ⊓ V) := by
  apply le_antisymm
  · rintro x ⟨hx, hv⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    apply Submodule.mem_sup.mpr
    refine ⟨V.starProjection a, ⟨hA a ha, V.starProjection_apply_mem a⟩,
      V.starProjection b, ⟨hB b hb, V.starProjection_apply_mem b⟩, ?_⟩
    rw [← map_add, hab, V.starProjection_eq_self_iff.mpr hv]
  · exact sup_le (inf_le_inf_right V le_sup_left) (inf_le_inf_right V le_sup_right)

/-- On the projected space, orthogonality to the projected old image is
 equivalent to orthogonality to the entire old image. -/
theorem inf_orthogonal_of_projection (V A : Submodule ℂ E) [CompleteSpace V]
    (hA : ∀ x ∈ A, V.starProjection x ∈ A) :
    (A ⊓ V)ᗮ ⊓ V = Aᗮ ⊓ V := by
  ext x
  constructor
  · rintro ⟨hx, hv⟩
    refine ⟨?_, hv⟩
    intro a ha
    have hz := hx (V.starProjection a) ⟨hA a ha, V.starProjection_apply_mem a⟩
    have he := V.starProjection_inner_eq_zero a x hv
    rw [inner_sub_left, hz, sub_zero] at he
    exact he
  · rintro ⟨hx, hv⟩
    exact ⟨fun a ha => hx a ha.1, hv⟩

/-- The relative two-old-space dimension identity, valid inside a partial
 newspace preserved by the old-image projections. -/
theorem relative_two_old_finrank [FiniteDimensional ℂ E]
    (V A B : Submodule ℂ E) [CompleteSpace V]
    (hA : ∀ x ∈ A, V.starProjection x ∈ A)
    (hB : ∀ x ∈ B, V.starProjection x ∈ B) :
    Module.finrank ℂ ↥((A ⊔ B)ᗮ ⊓ V) +
      Module.finrank ℂ ↥(A ⊓ V) + Module.finrank ℂ ↥(B ⊓ V) =
        Module.finrank ℂ V + Module.finrank ℂ ↥((A ⊓ B) ⊓ V) := by
  have hsum : ∀ x ∈ A ⊔ B, V.starProjection x ∈ A ⊔ B := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hA a ha) (hB b hb)
  have hd := Submodule.finrank_add_inf_finrank_orthogonal
    (inf_le_right : (A ⊔ B) ⊓ V ≤ V)
  rw [inf_orthogonal_of_projection V (A ⊔ B) hsum] at hd
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (A ⊓ V) (B ⊓ V)
  rw [← inf_sup_of_projection V A B hA hB] at hs
  have hi : (A ⊓ V) ⊓ (B ⊓ V) = (A ⊓ B) ⊓ V := by
    ext x
    simp only [Submodule.mem_inf]
    tauto
  rw [hi] at hs
  omega

#print axioms inf_sup_of_projection
#print axioms inf_orthogonal_of_projection
#print axioms relative_two_old_finrank

end AsymptoticClassicalCusp
