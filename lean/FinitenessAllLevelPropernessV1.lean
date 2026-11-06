module

public import FinitenessAllLevelContinuationV1
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelProperness

open Complex Filter Set FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessAllLevelDiskSeries FinitenessAllLevelBoundedFamilies
open scoped Topology

/-- Bounded-eigenvalue families are closed for the coefficient topology.
The analytic continuation in the limit is supplied by the Mellin theorem. -/
theorem family_isClosed {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L)
    {m : ℕ} (hm : 0 < m) : IsClosed (family N (2 * m) p L) := by
  apply IsSeqClosed.isClosed
  intro a f ha ht
  obtain ⟨s, hs⟩ := subset_fixed_growth hN hp hgood hlarge hL
  have hcoeff (n : ℕ) : Tendsto (fun j => a j n) atTop (𝓝 (f n)) :=
    ((continuous_apply n).tendsto f).comp ht
  exact ⟨FinitenessAllLevelContinuation.limit_isSolution hN (by omega)
    (fun j => hs m (ha j)) hcoeff,
    closure_eigenvalue_bound (mem_closure_of_tendsto ht (Eventually.of_forall ha))⟩

/-- Compactness of the actual original family, rather than just its closure. -/
theorem family_isCompact {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L)
    {m : ℕ} (hm : 0 < m) : IsCompact (family N (2 * m) p L) := by
  have h := closure_isCompact hN hp hgood hlarge hL m
  rwa [(family_isClosed hN hp hgood hlarge hL hm).closure_eq] at h

theorem compact_eigenvalue_set {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m)
    {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {f : ℕ → ℂ | IsSolution N (2 * m) f ∧ f p ∈ K} := by
  obtain ⟨L, hL, hb⟩ := hK.isBounded.exists_pos_norm_le
  have he : {f : ℕ → ℂ | IsSolution N (2 * m) f ∧ f p ∈ K} =
      family N (2 * m) p L ∩ (fun f : ℕ → ℂ => f p) ⁻¹' K := by
    ext f
    constructor
    · intro hf
      exact ⟨⟨hf.1, hb _ hf.2⟩, hf.2⟩
    · intro hf
      exact ⟨hf.1.1, hf.2⟩
  rw [he]
  exact (family_isCompact hN hp hgood hlarge hL.le hm).inter_right
    (hK.isClosed.preimage (continuous_apply p))

/-- The eigenvalue projection on the literal original solution set is a
proper topological map for the coefficient topology. No analytic-space
structure or geometric finiteness theorem is assumed here. -/
theorem eigenvalue_isProperMap {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m) :
    IsProperMap (fun f : S N (2 * m) => f.val p) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(continuous_apply p).comp continuous_subtype_val, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  have he : Subtype.val '' ((fun f : S N (2 * m) => f.val p) ⁻¹' K) =
      {f : ℕ → ℂ | IsSolution N (2 * m) f ∧ f p ∈ K} := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.property, hg⟩
    · intro hf
      exact ⟨⟨f, hf.1⟩, hf.2, rfl⟩
  rw [he]
  exact compact_eigenvalue_set hN hp hgood hlarge hm hK

def diskMap (k : ℕ) (R : ℝ) (f : ℕ → ℂ) : C(Disk R, ℂ) :=
  diskSeries (fullCoefficients f k) R

/-- On a bounded-eigenvalue family, coefficient convergence gives the
Banach supremum-norm topology needed for the future analytic charts. -/
theorem disk_continuous_on_family {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L)
    (m : ℕ) {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    ContinuousOn (diskMap (2 * m) R) (family N (2 * m) p L) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply SeqContinuous.continuous
  intro a f ht
  have hcoeff (n : ℕ) : Tendsto (fun j => (a j).val n) atTop (𝓝 (f.val n)) :=
    (((continuous_apply n).comp continuous_subtype_val).tendsto f).comp ht
  exact fourier_disk_tendsto hN hp hgood hlarge hL hR hR1
    (fun j => (a j).property) hcoeff

theorem disk_image_isCompact {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m)
    {K : Set ℂ} (hK : IsCompact K) {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    IsCompact (diskMap (2 * m) R '' {f : ℕ → ℂ | IsSolution N (2 * m) f ∧ f p ∈ K}) := by
  obtain ⟨L, hL, hb⟩ := hK.isBounded.exists_pos_norm_le
  apply (compact_eigenvalue_set hN hp hgood hlarge hm hK).image_of_continuousOn
  exact (disk_continuous_on_family hN hp hgood hlarge hL.le m hR hR1).mono
    (fun f hf => ⟨hf.1, hb _ hf.2⟩)

#print axioms family_isClosed
#print axioms family_isCompact
#print axioms compact_eigenvalue_set
#print axioms eigenvalue_isProperMap
#print axioms disk_continuous_on_family
#print axioms disk_image_isCompact

end FinitenessAllLevelProperness
