module

public import FinitenessAllLevelGlobalRecoveryV1
public import FinitenessAllLevelDiskCoordinatesV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set Metric FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelFormalContinuation
  FinitenessAllLevelCertificatePencil FinitenessOriginalInput
  QuantitativeArithmeticRetainedCertificate

/-- Every fixed exact sector has compact inverse image of every bounded
closed disk, with no restriction on the disk radius or auxiliary bound. -/
theorem global_sector_bounded_isCompact {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool) (B : ℝ) :
    IsCompact {t : ℂ × space (radius a) |
      t ∈ sectorLocus hN A P hb hba m s ∧ ‖t.1‖ ≤ B} := by
  let c := FinitenessAllLevelDiskCoordinates.coordinates N (2 * m) p
    (radius_pos a) (radius_lt_one (hb.trans hba))
  have hc : Continuous c := FinitenessAllLevelDiskCoordinates.coordinates_continuous
    hN hp hgood hlarge m (radius_pos a) (radius_lt_one (hb.trans hba))
  have hK : IsCompact ((fun f : S N (2 * m) => f.val p) ⁻¹' closedBall 0 B) :=
    (FinitenessAllLevelProperness.eigenvalue_isProperMap hN hp hgood hlarge hm).isCompact_preimage
      (isCompact_closedBall 0 B)
  apply (hK.image hc).of_isClosed_subset
  · exact (constrained_locus_isClosed hN hp A P hb hba hae (sector Q m s) m).inter
      (isClosed_le continuous_fst.norm continuous_const)
  · intro t ht
    obtain ⟨f, he, hF⟩ := constraints_recover_global hN hp hpQ hm A P (hb.trans hba) hae
      (sector Q m s) t.1 t.2 (fun q _ => sector_norm Q m s q)
      (sector_signs Q m s 1) ht.1.2
    refine ⟨f, ?_, ?_⟩
    · simpa only [mem_preimage, mem_closedBall, dist_zero_right, he] using ht.2
    · exact Prod.ext he hF

/-- The projection of a fixed exact analytic sector is proper over the
whole eigenvalue plane, in its actual Banach subspace topology. -/
theorem global_sector_projection_isProperMap {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool) :
    IsProperMap (fun t : sectorLocus hN A P hb hba m s => t.val.1) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_fst.comp continuous_subtype_val, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  have he : Subtype.val '' ((fun t : sectorLocus hN A P hb hba m s => t.val.1) ⁻¹' K) =
      {t : ℂ × space (radius a) | t ∈ sectorLocus hN A P hb hba m s ∧ t.1 ∈ K} := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, hu⟩
    · intro ht
      exact ⟨⟨t, ht.1⟩, ht.2, rfl⟩
  rw [he]
  obtain ⟨B, _, hB⟩ := hK.isBounded.exists_pos_norm_le
  apply (global_sector_bounded_isCompact hN hp hgood hlarge hpQ A P hb hba hae hm s B).of_isClosed_subset
  · exact (constrained_locus_isClosed hN hp A P hb hba hae (sector Q m s) m).inter
      (hK.isClosed.preimage continuous_fst)
  · intro t ht
    exact ⟨ht.1, hB _ ht.2⟩

#print axioms global_sector_bounded_isCompact
#print axioms global_sector_projection_isProperMap

end FinitenessAllLevelConstraintLocus
