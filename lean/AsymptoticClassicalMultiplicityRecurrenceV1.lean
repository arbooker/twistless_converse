module

public import AsymptoticClassicalMultiplicityRelativeV1
public import AsymptoticClassicalMultiplicityRepeatedV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

/-- At a simply ramified prime the old intersection is zero in the original
 Fricke model of the two degeneracy images. -/
theorem simple_fricke_old_intersection (M p : ℕ) (hM : 0 < M) (hp : p.Prime)
    (hc : p.Coprime M) (k : ℤ) :
    LinearMap.range (restrict k (level_antitone (Nat.dvd_mul_left M p))) ⊓
      LinearMap.range (restrict k (level_le_frickeOldLevel (Nat.mul_pos hp.pos hM)
        (Nat.dvd_mul_left M p))) = ⊥ := by
  rw [restrict_range_group_congr k _ _ (frickeOldLevel_eq_dilationLevel M p hM hp.pos)]
  exact simple_old_intersection_eq_bot M p hM hp hc k

/-- The paired trace kernel at a new factor is the orthogonal complement
 of the literal two old images from the original lower level. -/
theorem primeTraceKernel_mul_orthogonal (M p : ℕ) [NeZero M] (hM : 0 < M)
    (hp : p.Prime) (k : ℤ) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    primeTraceKernel (p * M) (Nat.mul_pos hp.pos hM) k
      ⟨p, hp, Nat.dvd_mul_right p M⟩ =
      (LinearMap.range (restrict k (level_antitone (Nat.dvd_mul_left M p))) ⊔
       LinearMap.range (restrict k (level_le_frickeOldLevel (Nat.mul_pos hp.pos hM)
         (Nat.dvd_mul_left M p))))ᗮ := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [primeTraceKernel_eq_orthogonal]
  congr 1
  unfold primeOldSpace
  have hd : p * M / p = M := Nat.mul_div_cancel_left M hp.pos
  apply congrArg₂ (· ⊔ ·)
  · exact restrict_range_group_congr k _ _ (congrArg level hd)
  · exact restrict_range_group_congr k _ _ (congrArg (fun L => frickeOldLevel (p * M) L
      (Nat.mul_pos hp.pos hM)) hd)

/-- Imposing a new simply ramified prime removes precisely two copies of
 the lower-level partial newspace. Every compatibility is for actual cusp forms. -/
theorem partialNewSpace_simple_finrank (M p : ℕ) [NeZero M] (hM : 0 < M)
    (hp : p.Prime) (hc : p.Coprime M) (k : ℕ) (hk : Even k)
    (S : Set ℕ) (hpS : p ∉ S) :
    Module.finrank ℂ (partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) (k : ℤ) (insert p S)) +
      2 * Module.finrank ℂ (partialNewSpace M hM (k : ℤ) S) =
    Module.finrank ℂ (partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) (k : ℤ) S) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let A := LinearMap.range (restrict (k : ℤ) (level_antitone (Nat.dvd_mul_left M p)))
  let B := LinearMap.range (restrict (k : ℤ) (level_le_frickeOldLevel
    (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p)))
  let V := partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) (k : ℤ) S
  have hA : ∀ x ∈ A, V.starProjection x ∈ A := by
    rintro x ⟨f, rfl⟩
    rw [restrict_partial_projection M p hM hp (k : ℤ) S hpS]
    exact ⟨_, rfl⟩
  have hB : ∀ x ∈ B, V.starProjection x ∈ B := by
    have he : A.map (frickeOperator (p * M) (Nat.mul_pos hp.pos hM) (k : ℤ)) = B :=
      fricke_map_old_range (p * M) M (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p) k hk
    rw [← he]
    rintro x ⟨f, hf, rfl⟩
    rw [fricke_partial_projection (p * M) (Nat.mul_pos hp.pos hM) k hk S]
    exact ⟨_, hA f hf, rfl⟩
  have hh := relative_two_old_finrank V A B hA hB
  have hAB : A ⊓ B = ⊥ := simple_fricke_old_intersection M p hM hp hc (k : ℤ)
  have hdimA : Module.finrank ℂ ↥(A ⊓ V) =
      Module.finrank ℂ (partialNewSpace M hM (k : ℤ) S) :=
    restrict_partial_finrank M p hM hp (k : ℤ) S hpS
  have hdimB : Module.finrank ℂ ↥(B ⊓ V) = Module.finrank ℂ ↥(A ⊓ V) :=
    fricke_old_partial_finrank (p * M) M (Nat.mul_pos hp.pos hM)
      (Nat.dvd_mul_left M p) k hk S
  rw [hAB, bot_inf_eq, finrank_bot, add_zero, hdimB, hdimA] at hh
  have hker := primeTraceKernel_mul_orthogonal M p hM hp (k : ℤ)
  have hinsert := partialNewSpace_insert (p * M) (Nat.mul_pos hp.pos hM) (k : ℤ) S
    ⟨p, hp, Nat.dvd_mul_right p M⟩
  rw [hker] at hinsert
  change partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) (k : ℤ) (insert p S) =
    (A ⊔ B)ᗮ ⊓ V at hinsert
  rw [hinsert]
  simpa only [two_mul, add_assoc] using hh

#print axioms simple_fricke_old_intersection
#print axioms primeTraceKernel_mul_orthogonal
#print axioms partialNewSpace_simple_finrank

end AsymptoticClassicalCusp
