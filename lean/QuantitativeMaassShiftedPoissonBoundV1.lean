module

public import QuantitativeMaassSchwartzPositiveModesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Removing the zero mode from any shifted periodization leaves at most
the total nonzero Fourier mass. The bound is uniform in the shift. -/
theorem schwartz_shifted_poisson_bound (F : SchwartzMap ℝ ℂ)
    (he : Function.Even F) (x : ℝ) :
    ‖(∑' k : ℤ,F (x+k))-𝓕 F 0‖≤2*(∑' n : ℕ,‖𝓕 F (n+1)‖) := by
  let q : ℤ→ℂ := fun n => 𝓕 F n*fourier n (x : UnitAddCircle)
  have hn (n : ℤ) : ‖q n‖=‖𝓕 F n‖ := by
    simp only [q,norm_mul,fourier_apply,Circle.norm_coe,mul_one]
  have hq : Summable q := Summable.of_norm (by
    simpa only [hn] using (schwartz_integer_summable (𝓕 F)).norm)
  have hi : Function.Injective (fun n : ℕ => (n:ℤ)+1) := by
    intro a b hab
    exact_mod_cast (add_right_cancel hab)
  have hj : Function.Injective (fun n : ℕ => -((n:ℤ)+1)) := neg_injective.comp hi
  have hp := hq.comp_injective hi
  have hm := hq.comp_injective hj
  have hsplit : (∑' n : ℤ,q n)-q 0=
      (∑' n : ℕ,q ((n:ℤ)+1))+(∑' n : ℕ,q (-((n:ℤ)+1))) := by
    rw [tsum_int_eq_zero_add_tsum_pnat hq,
      tsum_pnat_eq_tsum_succ (f := fun n : ℕ => q (n:ℤ)),
      tsum_pnat_eq_tsum_succ (f := fun n : ℕ => q (-(n:ℤ)))]
    simp only [Nat.cast_add,Nat.cast_one]
    abel
  have hzero : q 0=𝓕 F 0 := by simp only [q,Int.cast_zero,fourier_zero,mul_one]
  rw [F.tsum_eq_tsum_fourier x]
  change ‖(∑' n : ℤ,q n)-𝓕 F 0‖≤_
  rw [←hzero,hsplit]
  calc
    _≤‖∑' n : ℕ,q ((n:ℤ)+1)‖+‖∑' n : ℕ,q (-((n:ℤ)+1))‖ := norm_add_le _ _
    _≤(∑' n : ℕ,‖q ((n:ℤ)+1)‖)+(∑' n : ℕ,‖q (-((n:ℤ)+1))‖) :=
      add_le_add (norm_tsum_le_tsum_norm hp.norm) (norm_tsum_le_tsum_norm hm.norm)
    _=_ := by
      have hneg (n : ℕ) : 𝓕 F (-((n:ℝ)+1))=𝓕 F ((n:ℝ)+1) :=
        schwartz_fourier_even F he _
      simp only [hn,Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,
        hneg]
      ring

#print axioms schwartz_shifted_poisson_bound

end QuantitativeMaass
