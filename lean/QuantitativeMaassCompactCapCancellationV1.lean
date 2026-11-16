module

public import QuantitativeMaassBandMultipliersV1
public import QuantitativeMaassCappedWeightV1

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane

namespace QuantitativeMaass

/-- A finite inverse-band sum equals the inverse weight wherever it
contains the unique band of the point. -/
theorem LogBands.inverseCoefficient_sum {α : Type*} (l : α → ℝ)
    (S : Finset ℤ) (x : α) (hx : ⌊l x⌋ ∈ S) :
    (∑ n ∈ S, inverseCoefficient l n x) = (Real.exp (-l x) : ℂ) := by
  classical
  rw [Finset.sum_eq_single ⌊l x⌋]
  · exact Set.indicator_of_mem (mem_floor_region l x) _
  · intro n _ hn
    have hxn : x ∉ region l n := fun h =>
      Set.disjoint_left.mp (region_disjoint l hn) h (mem_floor_region l x)
    exact Set.indicator_of_notMem hxn _
  · exact fun h => False.elim (h hx)

/-- All points above the propagated lower cutoff lie in the finite set
of bands used by the terminal inverse cap. -/
theorem cappedHeightWeight_floor_mem {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (m : ℕ) (z : ℍ) (hz : δ * Real.exp (-R) ≤ z.im) :
    ⌊Real.log (cappedHeightWeight δ m z)⌋ ∈
      Finset.Icc (- (⌈(m : ℝ) * R + 1⌉₊ : ℤ)) (⌈(m : ℝ) * R + 1⌉₊ : ℤ) := by
  have hlog := Real.log_le_log (mul_pos hδ (Real.exp_pos (-R))) hz
  rw [Real.log_mul hδ.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hlower : -(m : ℝ) * R ≤ Real.log (cappedHeightWeight δ m z) := by
    rw [cappedHeightWeight_log hδ]
    have hh : -R ≤ min (Real.log z.im - Real.log δ) 0 := by
      exact le_min (by linarith) (neg_nonpos.mpr hR)
    nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg m)]
  have hupper : Real.log (cappedHeightWeight δ m z) ≤ 0 := by
    rw [cappedHeightWeight_log hδ]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) (min_le_right _ _)
  have hceil := Nat.le_ceil ((m : ℝ) * R + 1)
  have hlo := Int.lt_floor_add_one (Real.log (cappedHeightWeight δ m z))
  have hup := Int.floor_le (Real.log (cappedHeightWeight δ m z))
  apply Finset.mem_Icc.mpr
  constructor
  · have h : -((⌈(m : ℝ) * R + 1⌉₊ : ℕ) : ℝ) ≤
        (⌊Real.log (cappedHeightWeight δ m z)⌋ : ℤ) := by linarith
    exact_mod_cast h
  · have h : (⌊Real.log (cappedHeightWeight δ m z)⌋ : ℝ) ≤
        (⌈(m : ℝ) * R + 1⌉₊ : ℕ) := by
      linarith [show (0 : ℝ) ≤ (⌈(m : ℝ) * R + 1⌉₊ : ℕ) from Nat.cast_nonneg _]
    exact_mod_cast h

/-- Exact coefficient cancellation on the compact input rectangle used
by the window trace. It is independent of the upper height cutoff. -/
theorem compact_inverse_cap_coefficient {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (m : ℕ) (z : ℍ) (hz : δ * Real.exp (-R) ≤ z.im) :
    (∑ n ∈ Finset.Icc (- (⌈(m : ℝ) * R + 1⌉₊ : ℤ)) (⌈(m : ℝ) * R + 1⌉₊ : ℤ),
      LogBands.inverseCoefficient (fun w => Real.log (cappedHeightWeight δ m w)) n z) *
      (cappedHeightWeight δ m z : ℂ) = 1 := by
  rw [LogBands.inverseCoefficient_sum (fun w : ℍ => Real.log (cappedHeightWeight δ m w)) _ z
      (cappedHeightWeight_floor_mem hδ hR m z hz),
    ← Complex.ofReal_mul, Real.exp_neg, Real.exp_log (cappedHeightWeight_pos hδ m z),
    inv_mul_cancel₀ (cappedHeightWeight_pos hδ m z).ne', Complex.ofReal_one]

#print axioms LogBands.inverseCoefficient_sum
#print axioms cappedHeightWeight_floor_mem
#print axioms compact_inverse_cap_coefficient

end QuantitativeMaass
