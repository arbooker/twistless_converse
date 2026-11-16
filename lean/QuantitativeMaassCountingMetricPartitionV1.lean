module

public import QuantitativeMaassCoverMetricEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
open scoped ENNReal
namespace QuantitativeMaass

/-- The finite-cover partition identity also holds on counting orbits.
No finite orbit, finite total mass or subgroup closure is required. -/
theorem counting_cover_metric_partition {X ι : Type*} [Fintype ι]
    (e : ι→X≃X) (w : X→ℝ) (hw : ∀ x,0≤w x)
    (hpos : ∀ x,0<∑ i,w (e i x)) (F : X→ℝ≥0∞)
    (hF : ∀ i x,F (e i x)=F x) :
    (∑' x,ENNReal.ofReal (w x*(∑ i,(∑ j,w (e j ((e i).symm x)))⁻¹))*F x)=∑' x,F x := by
  classical
  let A (x : X) := ∑ i,w (e i x)
  let v (i : ι) (x : X) := ENNReal.ofReal (w x*(A ((e i).symm x))⁻¹)*F x
  have hv (x) : ENNReal.ofReal (w x*(∑ i,(∑ j,w (e j ((e i).symm x)))⁻¹))*F x=
      ∑' i,v i x := by
    rw [tsum_fintype]
    dsimp only [v,A]
    rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg,Finset.sum_mul]
    intro i _
    exact mul_nonneg (hw x) (inv_pos.mpr (hpos _)).le
  simp_rw [hv]
  rw [ENNReal.tsum_comm]
  have hmove (i : ι) : (∑' x,v i x)=∑' x,ENNReal.ofReal (w (e i x)*(A x)⁻¹)*F x := by
    rw [←(e i).tsum_eq (v i)]
    apply tsum_congr
    intro x
    dsimp only [v]
    rw [Equiv.symm_apply_apply,hF]
  simp_rw [hmove]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  rw [tsum_fintype,←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg]
  · rw [←Finset.sum_mul]
    change ENNReal.ofReal (A x*(A x)⁻¹)*F x=F x
    rw [mul_inv_cancel₀ (hpos x).ne',ENNReal.ofReal_one,one_mul]
  · intro i _
    exact mul_nonneg (hw _) (inv_pos.mpr (hpos x)).le

#print axioms counting_cover_metric_partition
end QuantitativeMaass
