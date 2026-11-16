module

public import QuantitativeMaassCappedWeightV1
public import QuantitativeMaassFiniteBandBoundV1
public import Mathlib.Data.Int.Interval

set_option autoImplicit false
@[expose] public noncomputable section

open UpperHalfPlane
open scoped BigOperators

namespace QuantitativeMaass

/-- Two logarithmic weight bands joined by a propagation ball have bounded
integer separation, uniformly in the cutoff height. -/
theorem cappedHeightWeight_band_separation {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (z w : ℍ) (n m : ℤ) (R : ℝ) (hR : dist z w≤R)
    (hz : (n:ℝ)≤Real.log (cappedHeightWeight ε t z) ∧
      Real.log (cappedHeightWeight ε t z)<(n:ℝ)+1)
    (hw : (m:ℝ)≤Real.log (cappedHeightWeight ε t w) ∧
      Real.log (cappedHeightWeight ε t w)<(m:ℝ)+1) :
    |(n:ℝ)-(m:ℝ)|<(t:ℝ)*R+1 := by
  have h := (cappedHeightWeight_log_dist hε t z w).trans
    (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg t))
  obtain ⟨hl,hu⟩ := abs_le.mp h
  exact abs_lt.mpr ⟨by linarith [hz.2,hw.1],by linarith [hz.1,hw.2]⟩

theorem integer_band_card (J : ℕ) (n : ℤ) :
    (Finset.Icc (n-(J:ℤ)) (n+(J:ℤ))).card=2*J+1 := by
  rw [Int.card_Icc]
  omega

theorem integer_band_filter_card (T : Finset ℤ) (J : ℕ) (n : ℤ) :
    (T.filter (fun m => |n-m|≤(J:ℤ))).card≤2*J+1 := by
  rw [←integer_band_card J n]
  apply Finset.card_le_card
  intro m hm
  have h := abs_le.mp (Finset.mem_filter.mp hm).2
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

/-- The finite-band estimate with the actual integer propagation
multiplicity 2J+1, derived in both directions. -/
theorem integer_band_norm_square_bound {H : Type*} [NormedAddCommGroup H]
    (S T : Finset ℤ) (J : ℕ) (C : ℝ) (a : ℤ → ℝ) (v : ℤ → ℤ → H)
    (hv : ∀ n∈S,∀ m∈T,|n-m|≤(J:ℤ) → ‖v n m‖≤C*a m) :
    (∑ n∈S,‖∑ m∈T.filter (fun m => |n-m|≤(J:ℤ)),v n m‖^2)≤
      ((2*J+1:ℕ):ℝ)^2*C^2*∑ m∈T,(a m)^2 := by
  apply finite_band_norm_square_bound S T (fun n => T.filter (fun m => |n-m|≤(J:ℤ)))
    (2*J+1) (fun _ _ => Finset.filter_subset _ _)
    (fun n _ => integer_band_filter_card T J n)
  · intro m hm
    have he : S.filter (fun n => m∈T.filter (fun m => |n-m|≤(J:ℤ)))=
        S.filter (fun n => |m-n|≤(J:ℤ)) := by
      ext n
      simp only [Finset.mem_filter,hm,true_and,abs_sub_comm]
    rw [he]
    exact integer_band_filter_card S J m
  · intro n hn m hm
    exact hv n hn m (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hm).2

#print axioms cappedHeightWeight_band_separation
#print axioms integer_band_card
#print axioms integer_band_filter_card
#print axioms integer_band_norm_square_bound

end QuantitativeMaass
