module

public import AsymptoticClassicalMultiplicityAdjointV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

instance partialNewSpace_complete (N : ℕ) [NeZero N] (hN : 0 < N) (k : ℤ) (S : Set ℕ) :
    CompleteSpace (partialNewSpace N hN k S) := FiniteDimensional.complete ℂ _

/-- An adjoint pair preserving subspaces intertwines their orthogonal projections. -/
theorem projection_intertwine_of_adjoint
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    (U : Submodule ℂ E) (V : Submodule ℂ F) [CompleteSpace U] [CompleteSpace V]
    (L : E →ₗ[ℂ] F) (T : F →ₗ[ℂ] E)
    (hadj : ∀ y x, inner ℂ (T y) x = inner ℂ y (L x))
    (hL : ∀ x ∈ U, L x ∈ V) (hT : ∀ y ∈ V, T y ∈ U) (x : E) :
    V.starProjection (L x) = L (U.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (hL _ (U.starProjection_apply_mem x))
  rw [← map_sub]
  rw [Submodule.mem_orthogonal]
  intro y hy
  rw [← hadj]
  exact (Submodule.mem_orthogonal U _).mp (U.sub_starProjection_mem_orthogonal x) _ (hT y hy)

/-- Restriction intertwines the actual Petersson projections onto partial
 newspaces whenever the newly added prime is outside the imposed set. -/
theorem restrict_partial_projection (M p : ℕ) [NeZero M] (hM : 0 < M) (hp : p.Prime)
    (k : ℤ) (S : Set ℕ) (hpS : p ∉ S) (f : CuspForm (level M) k) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) k S).starProjection
      (restrict k (level_antitone (Nat.dvd_mul_left M p)) f) =
    restrict k (level_antitone (Nat.dvd_mul_left M p))
      ((partialNewSpace M hM k S).starProjection f) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  exact projection_intertwine_of_adjoint (partialNewSpace M hM k S)
    (partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) k S)
    (restrict k (level_antitone (Nat.dvd_mul_left M p)))
    (arithmeticTrace (level (p * M)) (level M) k)
    (trace_adjoint (p * M) M k (Nat.dvd_mul_left M p))
    (fun x hx => restrict_mem_partialNewSpace M p hM hp k S hpS x hx)
    (fun y hy => trace_mem_partialNewSpace M p hM hp.pos k S y hy) f

/-- Projection compatibility identifies the intersection of an old image
 with a partial newspace as the image of the lower-level partial newspace. -/
theorem restrict_partial_range (M p : ℕ) [NeZero M] (hM : 0 < M) (hp : p.Prime)
    (k : ℤ) (S : Set ℕ) (hpS : p ∉ S) :
    (partialNewSpace M hM k S).map (restrict k (level_antitone (Nat.dvd_mul_left M p))) =
      LinearMap.range (restrict k (level_antitone (Nat.dvd_mul_left M p))) ⊓
        partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) k S := by
  let : NeZero p := ⟨hp.ne_zero⟩
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, restrict_mem_partialNewSpace M p hM hp k S hpS g hg⟩
  · rintro ⟨⟨g, rfl⟩, hg⟩
    refine ⟨(partialNewSpace M hM k S).starProjection g,
      (partialNewSpace M hM k S).starProjection_apply_mem g, ?_⟩
    rw [← restrict_partial_projection M p hM hp k S hpS,
      (partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) k S).starProjection_eq_self_iff.mpr hg]

#print axioms partialNewSpace_complete
#print axioms projection_intertwine_of_adjoint
#print axioms restrict_partial_projection
#print axioms restrict_partial_range

end AsymptoticClassicalCusp
