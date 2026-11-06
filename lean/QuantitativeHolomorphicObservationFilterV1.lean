module

public import QuantitativeHolomorphicNormalizedSectorV1
public import AsymptoticCompactObservationCountV1
public import QuantitativePositiveGramFilterV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap AsymptoticCompactObservationCount

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- Actual compact twist/ramified observation on normalized terminal coordinates. -/
def normalizedObservationRow (hN : 0 < N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s) :=
  let P' := AsymptoticReconstructedCount.parameters A P
  (rowOperator hN r e hs P'.epsilon_pos (P'.s+4) (h+1)).comp
    (normalizedCountReconstruction A hN P h e)

theorem normalizedObservationRow_norm_le (hN : 0 < N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s) :
    ‖normalizedObservationRow A hN P h e r hs‖ ≤
      rowBound hN r hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4) := by
  have hu : ‖normalizedCountReconstruction A hN P h e‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro g
    rw [normalizedCountReconstruction_norm, one_mul]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hu (norm_nonneg _)).trans
  simpa only [mul_one] using rowOperator_norm_le hN r e hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) (h+1)

theorem normalizedObservationRow_sector_zero (hN : 0 < N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s)
    (a : AsymptoticRamifiedSectors.sector N h
      (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) :
    normalizedObservationRow A hN P h e r hs (normalizedSectorCoordinates A hN P h e a) = 0 := by
  rw [normalizedObservationRow, comp_apply, normalizedSectorCoordinates_reconstruct]
  exact row_sector_annihilated hN (AsymptoticReconstructedCount.parameters A P) h e r hs _ ⟨a, rfl⟩

variable {ι : Type*}

/-- The observation bound is explicit and independent of weight and sector. -/
def normalizedObservationBound (hN : 0 < N) (P : Parameters A) (qs : Finset ι)
    (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i)) : ℝ :=
  1 + ∑ i ∈ qs, (rowBound hN (r i) (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)) ^ 2

def normalizedObservationGram (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i)) :=
  ∑ i ∈ qs, (normalizedObservationRow A hN P h e (r i) (hs i)).adjoint.comp
    (normalizedObservationRow A hN P h e (r i) (hs i))

theorem normalizedObservationBound_pos (hN : 0 < N) (P : Parameters A) (qs : Finset ι)
    (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i)) :
    0 < normalizedObservationBound A hN P qs r s hs := by
  unfold normalizedObservationBound
  positivity

private theorem gram_bounds_of_row_bounds {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (qs : Finset ι) (R : ι → G →L[ℂ] H) (b : ι → ℝ) (hb : ∀ i, ‖R i‖ ≤ b i) :
    0 ≤ ∑ i ∈ qs, (R i).adjoint.comp (R i) ∧
      (∑ i ∈ qs, (R i).adjoint.comp (R i)) ≤ (1 + ∑ i ∈ qs, b i ^ 2) • 1 := by
  have hg := QuantitativePositiveGramFilter.gram_sum_bounds qs R
  refine ⟨hg.1, hg.2.trans ?_⟩
  apply smul_le_smul_of_nonneg_right _ zero_le_one
  apply add_le_add le_rfl
  exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hb i) 2)

theorem normalizedObservationGram_bounds (hN : 0 < N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i)) :
    0 ≤ normalizedObservationGram A hN P h e qs r s hs ∧
      normalizedObservationGram A hN P h e qs r s hs ≤
        normalizedObservationBound A hN P qs r s hs • 1 := by
  exact gram_bounds_of_row_bounds qs
    (fun i => normalizedObservationRow A hN P h e (r i) (hs i)) _
    (fun i => normalizedObservationRow_norm_le A hN P h e (r i) (hs i))

def normalizedObservationFilter (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i)) (d : ℕ) :=
  (1 - (normalizedObservationBound A hN P qs r s hs)⁻¹ •
    normalizedObservationGram A hN P h e qs r s hs) ^ d

theorem normalizedObservationFilter_order (hN : 0 < N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i)) (d : ℕ) :
    0 ≤ normalizedObservationFilter A hN P h e qs r s hs d ∧
      normalizedObservationFilter A hN P h e qs r s hs d ≤ 1 ∧
        ‖normalizedObservationFilter A hN P h e qs r s hs d‖ ≤ 1 :=
  QuantitativePositiveGramFilter.filter_order _ (normalizedObservationBound_pos A hN P qs r s hs)
    (normalizedObservationGram_bounds A hN P h e qs r s hs).1
    (normalizedObservationGram_bounds A hN P h e qs r s hs).2 d

theorem normalizedObservationGram_sector_zero (hN : 0 < N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i))
    (a : AsymptoticRamifiedSectors.sector N h
      (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) :
    normalizedObservationGram A hN P h e qs r s hs
      (normalizedSectorCoordinates A hN P h e a) = 0 := by
  rw [normalizedObservationGram, _root_.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  change (normalizedObservationRow A hN P h e (r i) (hs i)).adjoint
    (normalizedObservationRow A hN P h e (r i) (hs i) (normalizedSectorCoordinates A hN P h e a)) = 0
  rw [normalizedObservationRow_sector_zero, map_zero]

/-- Every degree of the positive global filter fixes the entire literal
sector in its injective normalized coordinates. -/
theorem normalizedObservationFilter_sector_fixes (hN : 0 < N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀ i, IsCompact (s i)) (d : ℕ)
    (a : AsymptoticRamifiedSectors.sector N h
      (h+1+(AsymptoticReconstructedCount.parameters A P).s) e) :
    normalizedObservationFilter A hN P h e qs r s hs d
      (normalizedSectorCoordinates A hN P h e a) = normalizedSectorCoordinates A hN P h e a := by
  induction d with
  | zero => simp [normalizedObservationFilter]
  | succ d ih =>
    change ((1 - (normalizedObservationBound A hN P qs r s hs)⁻¹ •
      normalizedObservationGram A hN P h e qs r s hs)^(d+1)) _ = _
    rw [pow_succ', mul_apply_eq_comp]
    change (1 - (normalizedObservationBound A hN P qs r s hs)⁻¹ •
      normalizedObservationGram A hN P h e qs r s hs)
      (normalizedObservationFilter A hN P h e qs r s hs d (normalizedSectorCoordinates A hN P h e a)) = _
    rw [ih]
    simp only [sub_apply, smul_apply, normalizedObservationGram_sector_zero, smul_zero, sub_zero]
    rfl

#print axioms normalizedObservationGram_bounds
#print axioms normalizedObservationFilter_order
#print axioms normalizedObservationFilter_sector_fixes

end QuantitativeHolomorphic
