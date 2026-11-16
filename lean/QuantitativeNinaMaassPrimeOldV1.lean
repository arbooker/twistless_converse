module

public import QuantitativeNinaMaassPrimeNormalizerV1
public import AsymptoticClassicalLocalAtkinOldIntertwineV1
public import AsymptoticClassicalLocalAtkinSymmetryV1
public import AsymptoticClassicalLocalFrickeMatrixV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticClassicalCusp
open AsymptoticCongruenceLabels AsymptoticAtkinLehner AsymptoticFreshMatrices
open scoped MatrixGroups InnerProductSpace

/-!
The actual local normalizer preserves the simultaneous physical newspace.
It exchanges the two old directions at its own prime, preserves them at
other primes, and commutes with global Fricke. The reused classical
declarations below are matrix identities only; the operators and vectors
throughout this chapter belong to the actual automorphic Hilbert spaces.
-/

namespace QuantitativeNinaMaass

theorem primeNormalizerRepresentative_local (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M))) (z : ℍ) :
    (primeNormalizerRepresentative M p hM A B hAB f).val z =
      f.val (localAtkinReal M p (Fact.out : p.Prime).pos A B hAB • z) := by
  let hp := (Fact.out : p.Prime).pos
  have he : localAtkinReal M p hp A B hAB =
      SpecialLinearGroup.mapGL ℝ (localSquare M p A B hAB) *
        heckeNormalizerReal M p hp A B hAB := by
    apply mul_right_cancel (b := localAtkinReal M p hp A B hAB)
    rw [localAtkinReal_square, mul_assoc, heckeNormalizer_localAtkin,
      scalar_eq_positiveScalarReal p hp]
  change f.val (heckeNormalizerLabel M p hp A B hAB • z) = _
  rw [← heckeNormalizer_action, he, mul_smul]
  exact (representative_matrix_invariant (p * M) f
    ⟨_, ⟨_, localSquare_mem M p A B hAB, rfl⟩⟩ _).symm

theorem primeNormalizerRepresentative_fricke (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M))) :
    primeNormalizerRepresentative M p hM A B hAB
        (frickeRepresentative (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) f) =
      frickeRepresentative (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (primeNormalizerRepresentative M p hM A B hAB f) := by
  apply Subtype.ext
  funext z
  rw [primeNormalizerRepresentative_local]
  change f.val (frickeLabel (p * M) _ •
      (localAtkinReal M p (Fact.out : p.Prime).pos A B hAB • z)) =
    (primeNormalizerRepresentative M p hM A B hAB f).val (frickeLabel (p * M) _ • z)
  rw [primeNormalizerRepresentative_local, frickeLabel_action_real,
    frickeLabel_action_real, ← mul_smul,
    localAtkin_fricke_intertwine M p (Fact.out : p.Prime).pos A B hAB hM,
    mul_smul, mul_smul]
  exact representative_matrix_invariant (p * M) f
    ⟨_, ⟨_, localFrickeCommutator_mem M p A B hAB, rfl⟩⟩ _

theorem primeNormalizer_fricke (M p : ℕ) [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (v : AutomorphicSpace (p * M)) :
    HeckeL2.normalizer M p hM A B hAB
        (frickeIsometry (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) v) =
      frickeIsometry (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (HeckeL2.normalizer M p hM A B hAB v) := by
  have he : (fun v : AutomorphicSpace (p * M) => HeckeL2.normalizer M p hM A B hAB
      (frickeIsometry (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) v)) =
      fun v => frickeIsometry (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (HeckeL2.normalizer M p hM A B hAB v) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma (p * M)) (quotientMeasure (p * M))).equalizer
      ((HeckeL2.normalizer M p hM A B hAB).continuous.comp (frickeIsometry _ _).continuous)
      ((frickeIsometry _ _).continuous.comp (HeckeL2.normalizer M p hM A B hAB).continuous)
    funext f
    simp only [Function.comp_apply, frickeIsometry_apply, primeNormalizer_apply,
      primeNormalizerRepresentative_fricke]
  exact congrFun he v

/-- At its own prime, the local normalizer sends the ordinary physical
cover to the second physical old direction, with no scalar at weight zero. -/
theorem primeNormalizer_cover_self (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (v : AutomorphicSpace M) :
    HeckeL2.normalizer M p hM A B hAB (levelCover (Nat.dvd_mul_left M p) v) =
      frickeIsometry (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (levelCover (Nat.dvd_mul_left M p) (frickeIsometry M hM v)) := by
  have he : (fun v : AutomorphicSpace M => HeckeL2.normalizer M p hM A B hAB
      (levelCover (Nat.dvd_mul_left M p) v)) =
      fun v => frickeIsometry (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (levelCover (Nat.dvd_mul_left M p) (frickeIsometry M hM v)) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma M) (quotientMeasure M)).equalizer
      ((HeckeL2.normalizer M p hM A B hAB).continuous.comp (levelCover _).continuous)
      ((frickeIsometry _ _).continuous.comp
        ((levelCover _).continuous.comp (frickeIsometry M hM).continuous))
    funext f
    simp only [Function.comp_apply, levelCover_apply, primeNormalizer_apply, frickeIsometry_apply]
    apply congrArg (AutomorphicL2.denseEmbedding (gamma (p * M)) (quotientMeasure (p * M)))
    apply Subtype.ext
    funext z
    change f.val (heckeNormalizerLabel M p (Fact.out : p.Prime).pos A B hAB • z) =
      f.val (frickeLabel M hM • (frickeLabel (p * M)
        (Nat.mul_pos (Fact.out : p.Prime).pos hM) • z))
    rw [HeckeL2.normalizer_function_eq_dilation, ← mul_smul, fricke_mul_fricke_eq_dilation]
  exact congrFun he v

/-- A distinct lowering prime is intertwined by the explicit integral
change of local normalizer, on the full completed quotient spaces. -/
theorem primeNormalizer_cover_lower (L q p : ℕ) [NeZero L] [NeZero q] [Fact p.Prime]
    (hL : 0 < L) (hq : 0 < q) (A B : ℤ)
    (hAB : (p : ℤ) * A + ((q * L : ℕ) : ℤ) * B = 1)
    (v : AutomorphicSpace (p * L)) :
    HeckeL2.normalizer (q * L) p (Nat.mul_pos hq hL) A B hAB
        (levelCover (show p * L ∣ p * (q * L) by
          rw [Nat.mul_left_comm p q L]; exact Nat.dvd_mul_left _ _) v) =
      levelCover (show p * L ∣ p * (q * L) by
          rw [Nat.mul_left_comm p q L]; exact Nat.dvd_mul_left _ _)
        (HeckeL2.normalizer L p hL A ((q : ℤ) * B)
          (localAtkin_lower_bezout L q p A B hAB) v) := by
  let hd : p * L ∣ p * (q * L) := by
    rw [Nat.mul_left_comm p q L]
    exact Nat.dvd_mul_left _ _
  have he : (fun v : AutomorphicSpace (p * L) =>
      HeckeL2.normalizer (q * L) p (Nat.mul_pos hq hL) A B hAB (levelCover hd v)) =
      fun v => levelCover hd (HeckeL2.normalizer L p hL A ((q : ℤ) * B)
        (localAtkin_lower_bezout L q p A B hAB) v) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma (p * L)) (quotientMeasure (p * L))).equalizer
      ((HeckeL2.normalizer _ _ _ _ _ _).continuous.comp (levelCover hd).continuous)
      ((levelCover hd).continuous.comp (HeckeL2.normalizer _ _ _ _ _ _).continuous)
    funext f
    simp only [Function.comp_apply, levelCover_apply, primeNormalizer_apply]
    apply congrArg (AutomorphicL2.denseEmbedding (gamma (p * (q * L)))
      (quotientMeasure (p * (q * L))))
    apply Subtype.ext
    funext z
    rw [primeNormalizerRepresentative_local]
    change f.val (localAtkinReal (q * L) p (Fact.out : p.Prime).pos A B hAB • z) =
      (primeNormalizerRepresentative L p hL A ((q : ℤ) * B)
        (localAtkin_lower_bezout L q p A B hAB) f).val z
    rw [primeNormalizerRepresentative_local, localAtkinReal_lower, mul_smul]
    exact representative_matrix_invariant (p * L) f
      ⟨_, ⟨_, localAtkinLowerSL_mem L q p A B hAB, rfl⟩⟩ _
  exact congrFun he v

theorem oldDirections_invariant_of_cover {M N : ℕ} [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N)
    (U : AutomorphicSpace N →ₗ[ℂ] AutomorphicSpace N)
    (V : AutomorphicSpace M →ₗ[ℂ] AutomorphicSpace M)
    (hC : ∀ v, U (levelCover hMN v) = levelCover hMN (V v))
    (hW : ∀ v, U (frickeIsometry N hN v) = frickeIsometry N hN (U v)) :
    oldDirections hN hMN ≤ (oldDirections hN hMN).comap U := by
  apply sup_le
  · rintro _ ⟨v, rfl⟩
    change U (levelCover hMN v) ∈ oldDirections hN hMN
    rw [hC]
    exact Submodule.mem_sup_left ⟨V v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    change U (frickeIsometry N hN (levelCover hMN v)) ∈ oldDirections hN hMN
    rw [hW, hC]
    exact Submodule.mem_sup_right ⟨V v, rfl⟩

theorem oldDirections_invariant_of_swap {M N : ℕ} [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N)
    (U : AutomorphicSpace N →ₗ[ℂ] AutomorphicSpace N)
    (V : AutomorphicSpace M →ₗ[ℂ] AutomorphicSpace M)
    (hC : ∀ v, U (levelCover hMN v) = frickeIsometry N hN (levelCover hMN (V v)))
    (hW : ∀ v, U (frickeIsometry N hN v) = frickeIsometry N hN (U v)) :
    oldDirections hN hMN ≤ (oldDirections hN hMN).comap U := by
  apply sup_le
  · rintro _ ⟨v, rfl⟩
    change U (levelCover hMN v) ∈ oldDirections hN hMN
    rw [hC]
    exact Submodule.mem_sup_right ⟨V v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    change U (frickeIsometry N hN (levelCover hMN v)) ∈ oldDirections hN hMN
    rw [hW, hC, frickeIsometry_involutive]
    exact Submodule.mem_sup_left ⟨V v, rfl⟩

theorem primeNormalizer_old_self (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) :
    oldDirections (Nat.mul_pos (Fact.out : p.Prime).pos hM) (Nat.dvd_mul_left M p) ≤
      (oldDirections (Nat.mul_pos (Fact.out : p.Prime).pos hM) (Nat.dvd_mul_left M p)).comap
        (HeckeL2.normalizer M p hM A B hAB).toLinearMap :=
  oldDirections_invariant_of_swap _ _ (HeckeL2.normalizer M p hM A B hAB).toLinearMap
    (frickeIsometry M hM).toLinearMap (primeNormalizer_cover_self M p hM A B hAB)
    (primeNormalizer_fricke M p hM A B hAB)

/-- Every actual prime-old space is preserved. This supplies the
orthogonality argument for simultaneous newness, rather than assuming it. -/
theorem primeNormalizer_old_prime (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (q : {q : ℕ // q.Prime ∧ q ∣ p * M}) :
    oldDirections (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (Nat.div_dvd_of_dvd q.property.2) ≤
      (oldDirections (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (Nat.div_dvd_of_dvd q.property.2)).comap (HeckeL2.normalizer M p hM A B hAB).toLinearMap := by
  rcases q with ⟨q, hq, hqN⟩
  by_cases hqp : q = p
  · subst q
    simpa only [Nat.mul_div_cancel_left M (Fact.out : p.Prime).pos] using
      primeNormalizer_old_self M p hM A B hAB
  · have hqM : q ∣ M := (hq.dvd_mul.mp hqN).resolve_left
      (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp h))
    obtain ⟨L, rfl⟩ := hqM
    have hL : 0 < L := Nat.pos_of_mul_pos_left hM
    let : NeZero L := ⟨hL.ne'⟩
    let : NeZero q := ⟨hq.ne_zero⟩
    have hd : p * (q * L) / q = p * L := by
      rw [Nat.mul_left_comm p q L, Nat.mul_div_cancel_left _ hq.pos]
    simp only [hd]
    apply oldDirections_invariant_of_cover _ _
      (HeckeL2.normalizer (q * L) p hM A B hAB).toLinearMap
      (HeckeL2.normalizer L p hL A ((q : ℤ) * B)
        (localAtkin_lower_bezout L q p A B hAB)).toLinearMap
    · exact primeNormalizer_cover_lower L q p hL hq.pos A B hAB
    · exact primeNormalizer_fricke (q * L) p hM A B hAB

/-- Self-adjointness and the proved preservation of every old direction
give preservation of the actual simultaneous physical newspace. -/
theorem primeNormalizer_mem_newSpace (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (v : AutomorphicSpace (p * M))
    (hv : v ∈ newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)) :
    HeckeL2.normalizer M p hM A B hAB v ∈
      newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) := by
  simp only [newSpace, Submodule.mem_iInf] at hv ⊢
  intro q
  have hq := hv q
  rw [newTraceKernel_eq_orthogonal] at hq ⊢
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (HeckeL2.normalizer_selfAdjoint M p hM A B hAB) x v
  change inner ℂ (HeckeL2.normalizer M p hM A B hAB x) v =
    inner ℂ x (HeckeL2.normalizer M p hM A B hAB v) at hs
  rw [← hs]
  exact (Submodule.mem_orthogonal _ _).mp hq _ (primeNormalizer_old_prime M p hM A B hAB q hx)

#print axioms primeNormalizerRepresentative_local
#print axioms primeNormalizerRepresentative_fricke
#print axioms primeNormalizer_fricke
#print axioms primeNormalizer_cover_self
#print axioms primeNormalizer_cover_lower
#print axioms oldDirections_invariant_of_cover
#print axioms oldDirections_invariant_of_swap
#print axioms primeNormalizer_old_self
#print axioms primeNormalizer_old_prime
#print axioms primeNormalizer_mem_newSpace

end QuantitativeNinaMaass
