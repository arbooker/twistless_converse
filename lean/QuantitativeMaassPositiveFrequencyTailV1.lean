module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass

/-- The number of nonzero positive modes reaching height H is bounded by
u/H. The zero mode is excluded before taking the infinite sum. -/
theorem positive_frequency_count (H u : ℝ) (hH : 0<H) (hu : 0≤u) (a : ℝ≥0∞) :
    (∑' n : ℕ,if ((n+1:ℕ):ℝ)*H≤u then a else 0)≤ENNReal.ofReal (u/H)*a := by
  classical
  have hsel (n : ℕ) : ((n+1:ℕ):ℝ)*H≤u ↔ n<⌊u/H⌋₊ := by
    rw [←le_div_iff₀ hH,←Nat.le_floor_iff (div_nonneg hu hH.le)]
    omega
  simp_rw [hsel]
  have he : (∑' n : ℕ,if n<⌊u/H⌋₊ then a else 0)= (⌊u/H⌋₊:ℝ≥0∞)*a := by
    rw [tsum_eq_sum (s := Finset.range ⌊u/H⌋₊)]
    · calc
        _=∑ _n∈Finset.range ⌊u/H⌋₊,a := Finset.sum_congr rfl
          (fun n hn => ite_eq_left (Finset.mem_range.mp hn))
        _=_ := by simp
    · intro n hn
      simp only [Finset.mem_range,not_lt] at hn
      exact ite_eq_right (not_lt.mpr hn)
  rw [he]
  have hh : (⌊u/H⌋₊:ℝ≥0∞)≤ENNReal.ofReal (u/H) := by
    simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (Nat.floor_le (div_nonneg hu hH.le))
  exact mul_le_mul' hh le_rfl

/-- Tonelli's frequency-counting estimate in the transformed frequency
variable. It is valid even when one of the integrals is infinite. -/
theorem positive_frequency_tail_count (H : ℝ) (hH : 0<H) (h : ℝ→ℝ≥0∞) :
    (∫⁻ u in Ioi (0:ℝ),∑' n : ℕ,
      if ((n+1:ℕ):ℝ)*H≤u then h u/ENNReal.ofReal u else 0)≤
      ENNReal.ofReal H⁻¹*(∫⁻ u in Ioi (0:ℝ),h u) := by
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  apply (positive_frequency_count H u hH hu.le (h u/ENNReal.ofReal u)).trans_eq
  rw [ENNReal.ofReal_div_of_pos hH]
  have hu0 : ENNReal.ofReal u≠0 := (ENNReal.ofReal_pos.mpr hu).ne'
  have hut : ENNReal.ofReal u≠⊤ := ENNReal.ofReal_ne_top
  rw [div_eq_mul_inv,div_eq_mul_inv]
  calc
    _=(ENNReal.ofReal u*(ENNReal.ofReal u)⁻¹)*(ENNReal.ofReal H)⁻¹*h u := by ac_rfl
    _=_ := by rw [ENNReal.mul_inv_cancel hu0 hut,one_mul,ENNReal.ofReal_inv_of_pos hH]

#print axioms positive_frequency_count
#print axioms positive_frequency_tail_count

end QuantitativeMaass
