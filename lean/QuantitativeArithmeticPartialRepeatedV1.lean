module

public import QuantitativeArithmeticClassicalRepeatedV1
public import AsymptoticClassicalMultiplicityRecurrenceV1
public import AsymptoticClassicalDegeneracyRangeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPartialRepeated

open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

/-- An injective inclusion transports intersections with every subspace
whose exact image is the intersection with the upper space. -/
theorem map_inf_of_image {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℂ E] [Module ℂ F] (R : E →ₗ[ℂ] F) (hR : Function.Injective R)
    (U W : Submodule ℂ E) (V : Submodule ℂ F)
    (hU : U.map R = LinearMap.range R ⊓ V) :
    (W ⊓ U).map R = W.map R ⊓ V := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxW,hxU⟩, rfl⟩
    exact ⟨⟨x,hxW,rfl⟩, (hU ▸ (show R x ∈ U.map R from ⟨x,hxU,rfl⟩)).2⟩
  · rintro ⟨⟨x,hxW,rfl⟩,hxV⟩
    have hxU : R x ∈ U.map R := hU.symm ▸ ⟨⟨x,rfl⟩,hxV⟩
    obtain ⟨z,hz,hzx⟩ := hxU
    exact ⟨x,⟨hxW,hR hzx ▸ hz⟩,rfl⟩

/-- The two old ranges overlap in the restriction of the second old range
one level lower. This identity is valid at every repeated prime. -/
theorem repeated_intersection_range (L p : ℕ) (hL : 0<L) (hp : p.Prime) (k : ℤ) :
    let R := restrict k (level_antitone (Nat.dvd_mul_left (p*L) p))
    let D := restrict k (level_le_frickeOldLevel (Nat.mul_pos hp.pos hL)
      (Nat.dvd_mul_left L p))
    LinearMap.range R ⊓ LinearMap.range (restrict k (level_le_frickeOldLevel
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (Nat.dvd_mul_left (p*L) p))) =
      (LinearMap.range D).map R := by
  let : NeZero L := ⟨hL.ne'⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  dsimp only
  rw [restrict_range_group_congr k _ (level_le_dilation_conjugate (p*L) p hp.pos) (frickeOldLevel_eq_dilationLevel
    (p*L) p (Nat.mul_pos hp.pos hL) hp.pos)]
  rw [restrict_range_group_congr k _ (level_le_dilation_conjugate L p hp.pos) (frickeOldLevel_eq_dilationLevel L p hL hp.pos)]
  rw [restrict_intersection_eq_range (J := dilationLevel L p hp.pos) k _ _
    ((level_antitone (Nat.dvd_mul_left (p*L) p)).trans
      (level_le_dilation_conjugate L p hp.pos))
    (QuantitativeArithmeticClassicalRepeated.repeated_old_join_eq L p hL hp)]
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨restrict k (level_le_dilation_conjugate L p hp.pos) g,⟨g,rfl⟩,rfl⟩
  · rintro ⟨g,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩

/-- The overlap still contributes exactly the two-step lower partial
newspace after imposing any collection of other prime conditions. -/
theorem repeated_partial_intersection_finrank (L p : ℕ) (hL : 0<L)
    (hp : p.Prime) (k : ℕ) (hk : Even k) (S : Set ℕ) (hpS : p∉S) :
    Module.finrank ℂ ↥((LinearMap.range (restrict (k:ℤ)
      (level_antitone (Nat.dvd_mul_left (p*L) p))) ⊓
      LinearMap.range (restrict (k:ℤ) (level_le_frickeOldLevel
        (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (Nat.dvd_mul_left (p*L) p)))) ⊓
      partialNewSpace (p*(p*L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (k:ℤ) S) =
      Module.finrank ℂ (partialNewSpace L hL (k:ℤ) S) := by
  let : NeZero L := ⟨hL.ne'⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [repeated_intersection_range L p hL hp (k:ℤ)]
  rw [← map_inf_of_image _ (restrict_injective (k:ℤ) _)
    (partialNewSpace (p*L) (Nat.mul_pos hp.pos hL) (k:ℤ) S) _ _
    (restrict_partial_range (p*L) p (Nat.mul_pos hp.pos hL) hp (k:ℤ) S hpS)]
  rw [finrank_map_of_injective _ _ (restrict_injective (k:ℤ) _)]
  rw [fricke_old_partial_finrank (p*L) L (Nat.mul_pos hp.pos hL)
    (Nat.dvd_mul_left L p) k hk S]
  exact restrict_partial_finrank L p hL hp (k:ℤ) S hpS

/-- The full second-difference recurrence with all other new conditions retained. -/
theorem partialNewSpace_repeated_finrank (L p : ℕ) (hL : 0 < L)
    (hp : p.Prime) (k : ℕ) (hk : Even k)
    (S : Set ℕ) (hpS : p ∉ S) :
    Module.finrank ℂ (partialNewSpace (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (k : ℤ) (insert p S)) +
      2 * Module.finrank ℂ (partialNewSpace (p * L) (Nat.mul_pos hp.pos hL) (k : ℤ) S) =
    Module.finrank ℂ (partialNewSpace (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (k : ℤ) S) + Module.finrank ℂ (partialNewSpace L hL (k : ℤ) S) := by
  let : NeZero L := ⟨hL.ne'⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let A := LinearMap.range (restrict (k : ℤ) (level_antitone (Nat.dvd_mul_left (p * L) p)))
  let B := LinearMap.range (restrict (k : ℤ) (level_le_frickeOldLevel
    (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (Nat.dvd_mul_left (p * L) p)))
  let V := partialNewSpace (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (k : ℤ) S
  have hA : ∀ x ∈ A, V.starProjection x ∈ A := by
    rintro x ⟨f, rfl⟩
    rw [restrict_partial_projection (p * L) p (Nat.mul_pos hp.pos hL) hp (k : ℤ) S hpS]
    exact ⟨_, rfl⟩
  have hB : ∀ x ∈ B, V.starProjection x ∈ B := by
    have he : A.map (frickeOperator (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (k : ℤ)) = B :=
      fricke_map_old_range (p * (p * L)) (p * L) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (Nat.dvd_mul_left (p * L) p) k hk
    rw [← he]
    rintro x ⟨f, hf, rfl⟩
    rw [fricke_partial_projection (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k hk S]
    exact ⟨_, hA f hf, rfl⟩
  have hh := relative_two_old_finrank V A B hA hB
  have hAB : Module.finrank ℂ ↥((A ⊓ B) ⊓ V) =
      Module.finrank ℂ (partialNewSpace L hL (k : ℤ) S) :=
    repeated_partial_intersection_finrank L p hL hp k hk S hpS
  have hdimA : Module.finrank ℂ ↥(A ⊓ V) =
      Module.finrank ℂ (partialNewSpace (p * L) (Nat.mul_pos hp.pos hL) (k : ℤ) S) :=
    restrict_partial_finrank (p * L) p (Nat.mul_pos hp.pos hL) hp (k : ℤ) S hpS
  have hdimB : Module.finrank ℂ ↥(B ⊓ V) = Module.finrank ℂ ↥(A ⊓ V) :=
    fricke_old_partial_finrank (p * (p * L)) (p * L) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))
      (Nat.dvd_mul_left (p * L) p) k hk S
  rw [hAB, hdimB, hdimA] at hh
  have hker := primeTraceKernel_mul_orthogonal (p * L) p (Nat.mul_pos hp.pos hL) hp (k : ℤ)
  have hinsert := partialNewSpace_insert (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (k : ℤ) S
    ⟨p, hp, Nat.dvd_mul_right p (p * L)⟩
  rw [hker] at hinsert
  change partialNewSpace (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (k : ℤ) (insert p S) =
    (A ⊔ B)ᗮ ⊓ V at hinsert
  rw [hinsert]
  simpa only [two_mul, add_assoc] using hh


#print axioms repeated_intersection_range
#print axioms repeated_partial_intersection_finrank
#print axioms partialNewSpace_repeated_finrank

end QuantitativeArithmeticPartialRepeated
