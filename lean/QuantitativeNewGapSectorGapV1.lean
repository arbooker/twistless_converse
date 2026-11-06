module

public import QuantitativeNewGapSectorSpaceV1
public import QuantitativeNewGapAllPrimesV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticSectorSigns
open AsymptoticSubspaceIntersection
open scoped lp

def sectorSignRow (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    ℓ²(Classes (gamma N),ℂ) →L[ℂ] ℓ²(Classes (gamma N),ℂ) :=
  permutationOperator (sectorNormalizer N hN i)-(sectorNormalizerSign e i:ℂ) • 1

theorem sectorSignRow_gap (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    4*‖f-(sectorSignConstraint N hN e i).starProjection f‖^2=‖sectorSignRow N hN e i f‖^2 :=
  permutationSignSpace_gap _ (sectorNormalizer_involutive N hN i) _ (sectorNormalizerSign_sq e i) f

theorem countingSectorSpace_distance (N : ℕ) (hN : 0<N) (e : Sector N)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    ‖f-(countingSectorSpace N hN e).starProjection f‖^2≤
      ‖f-(AsymptoticTotalNewCorner.space N hN).starProjection f‖^2+
      ∑ i : SectorSignIndex N,‖f-(sectorSignConstraint N hN e i).starProjection f‖^2 := by
  have h₁ := inter_projection_distance _ _ (totalNew_jointSectorSigns_commute N hN e) f
  have h₂ := jointListSpace_distance _ (sectorSignProjections_commute N hN e)
    (Finset.univ : Finset (SectorSignIndex N)).toList f
  rw [Finset.sum_map_toList] at h₂
  exact h₁.trans (add_le_add_right h₂ _)

/-- Positive gap for the literal finite intersection of every new
constraint and every global/local sign. All commutators and arithmetic
old-group preservation have been proved for these actual operators. -/
theorem countingSectorSpace_gap (N : ℕ) (hN : 0<N) :
    ∃ γ : ℝ,0<γ ∧ ∀ (e : Sector N) (f : ℓ²(Classes (gamma N),ℂ)),
      γ*‖f-(countingSectorSpace N hN e).starProjection f‖^2≤
        (N.primeFactors.toList.map fun p => localOldEnergy N hN p f).sum+
        ∑ i : SectorSignIndex N,‖sectorSignRow N hN e i f‖^2 := by
  obtain ⟨a,ha,hgap⟩ := totalNew_old_energy_gap N hN
  refine ⟨min a 4,lt_min ha (by norm_num),?_⟩
  intro e f
  have hfirst := (mul_le_mul_of_nonneg_right (min_le_left a 4)
    (sq_nonneg ‖f-(AsymptoticTotalNewCorner.space N hN).starProjection f‖)).trans (hgap f)
  have hsecond : min a 4*(∑ i : SectorSignIndex N,
      ‖f-(sectorSignConstraint N hN e i).starProjection f‖^2)≤
      ∑ i : SectorSignIndex N,‖sectorSignRow N hN e i f‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_right (min_le_right a 4)
      (sq_nonneg ‖f-(sectorSignConstraint N hN e i).starProjection f‖)
    rwa [sectorSignRow_gap] at hh
  exact (mul_le_mul_of_nonneg_left (countingSectorSpace_distance N hN e f)
    (le_min ha.le (by norm_num))).trans (by rw [mul_add]; exact add_le_add hfirst hsecond)

#print axioms countingSectorSpace_distance
#print axioms countingSectorSpace_gap

end QuantitativeNewGap
