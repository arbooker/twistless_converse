module

public import QuantitativeMaassTranslatedSchwartzMassV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap

namespace QuantitativeMaass

theorem broadTimeWeight_cosinePacket_norm_two (L : ℝ) (hL : 0 < L) (t r : ℝ) :
    ‖cosinePacket (broadTimeWeight L t) r‖ ≤ 2 := by
  have hi : Integrable (broadTimeWeight L t) := (broadTimeWeight_smooth L t).continuous.integrable_of_hasCompactSupport
    (broadTimeWeight_compact L hL t)
  apply le_trans (b := ∫ s : ℝ, ‖broadTimeWeight L t s‖)
  · apply norm_integral_le_of_norm_le hi.norm
    filter_upwards with s
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (norm_nonneg _)).trans_eq
      (mul_one _)
  · exact broadTimeWeight_norm_integral_le L hL t

/-- The concrete normalized packet has spectral mass of order t L + L².
The constant is independent of both frequency and width. -/
theorem broadTimeWeight_spectral_mass_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 0 < L → ∀ t : ℝ,
      Integrable (fun r : ℝ => |r| * ‖cosinePacket (broadTimeWeight L t) r‖^2) ∧
      (∫ r : ℝ, |r| * ‖cosinePacket (broadTimeWeight L t) r‖^2) ≤
        C * (|t| *L + L^2) := by
  let F := angularFourier broadBaseSchwartz
  let m₀ := ∫ u : ℝ, ‖F u‖
  let m₁ := ∫ u : ℝ, |u| * ‖F u‖
  have hm₀ : 0 ≤ m₀ := integral_nonneg (fun _ => norm_nonneg _)
  have hm₁ : 0 ≤ m₁ := integral_nonneg (fun _ => by positivity)
  refine ⟨4*(m₀+m₁), by positivity, ?_⟩
  intro L hL t
  have hm := translatedSchwartz_first_moment F L hL t
  have hp := translatedSchwartz_first_moment F L hL (-t)
  simp only [sub_neg_eq_add, abs_neg] at hp
  let g : ℝ → ℝ := fun r => 2*(|r| *‖F ((r-t)/L)‖ + |r| *‖F ((r+t)/L)‖)
  have hg : Integrable g := (hm.1.add hp.1).const_mul 2
  have hb (r : ℝ) : |r| *‖cosinePacket (broadTimeWeight L t) r‖^2 ≤ g r := by
    have htwo := broadTimeWeight_cosinePacket_norm_two L hL t r
    have hsum := broadTimeWeight_cosinePacket_norm_le L hL t r
    have hn := norm_nonneg (cosinePacket (broadTimeWeight L t) r)
    have hs : ‖cosinePacket (broadTimeWeight L t) r‖^2 ≤
        2*(‖F ((r-t)/L)‖ + ‖F ((r+t)/L)‖) := by
      dsimp [F]
      nlinarith
    have hx := mul_le_mul_of_nonneg_left hs (abs_nonneg r)
    dsimp [g]
    nlinarith
  have hcont : Continuous (cosinePacket (broadTimeWeight L t)) := by
    have he : cosinePacket (broadTimeWeight L t) =
        angularFourier (broadTimeSchwartz L hL t) := by
      funext r
      exact cosinePacket_eq_angularFourier (broadTimeSchwartz L hL t)
        (broadTimeWeight_even L t) r
    rw [he]
    exact (angularFourier (broadTimeSchwartz L hL t)).continuous
  have hi : Integrable (fun r : ℝ => |r| *‖cosinePacket (broadTimeWeight L t) r‖^2) :=
    hg.mono' (by fun_prop) (Filter.Eventually.of_forall (fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb r))
  refine ⟨hi, (integral_mono hi hg hb).trans ?_⟩
  dsimp [g]
  rw [integral_const_mul, integral_add hm.1 hp.1]
  have hm' : (∫ r : ℝ, |r| *‖F ((r-t)/L)‖) ≤ L*(|t| *m₀+L*m₁) := hm.2
  have hp' : (∫ r : ℝ, |r| *‖F ((r+t)/L)‖) ≤ L*(|t| *m₀+L*m₁) := hp.2
  have hcross₀ : 0 ≤ m₀*L^2 := by positivity
  have hcross₁ : 0 ≤ m₁*|t| *L := by positivity
  nlinarith

#print axioms broadTimeWeight_cosinePacket_norm_two
#print axioms broadTimeWeight_spectral_mass_bound

end QuantitativeMaass
