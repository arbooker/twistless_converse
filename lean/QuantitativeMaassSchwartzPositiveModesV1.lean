module

public import QuantitativeMaassSchwartzPeriodizationV1
public import QuantitativeMaassPositiveWindowKernelV1
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass

theorem schwartz_integer_summable (F : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => F n) :=
  summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((F.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

theorem even_integer_tsum (f : ℤ→ℂ) (hf : Summable f) (he : Function.Even f) :
    (∑' n : ℤ,f n)=f 0+2*(∑' n : ℕ,f (n+1)) := by
  have hh := tsum_int_eq_zero_add_two_mul_tsum_pnat he hf
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (n : ℤ))] at hh
  simpa only [two_nsmul,two_mul,Nat.cast_add,Nat.cast_one] using hh

/-- Poisson summation with the horizontal zero mode explicitly removed. -/
theorem schwartz_centered_poisson (F : SchwartzMap ℝ ℂ) (he : Function.Even F) :
    (∑' k : ℤ,F k)-𝓕 F 0=2*(∑' n : ℕ,𝓕 F (n+1)) := by
  have hp := F.tsum_eq_tsum_fourier 0
  simp only [zero_add,AddCircle.coe_zero,fourier_eval_zero,mul_one] at hp
  have heF : Function.Even (fun n : ℤ => 𝓕 F n) := by
    intro n
    simp only [Int.cast_neg]
    exact schwartz_fourier_even F he n
  rw [even_integer_tsum _ (schwartz_integer_summable (𝓕 F)) heF] at hp
  simpa only [Int.cast_zero,Int.cast_add,Int.cast_one,Int.cast_natCast,add_sub_cancel_left] using
    congrArg (fun z : ℂ => z-𝓕 F 0) hp

#print axioms schwartz_integer_summable
#print axioms even_integer_tsum
#print axioms schwartz_centered_poisson

end QuantitativeMaass
