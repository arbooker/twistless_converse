module

public import QuantitativeMaassWavePacketResidualV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology

namespace QuantitativeMaass

def cosineSquareMass (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s : ℝ, ρ s*Real.cos (t*s)^2

/-- A positive cosine transform prevents loss in the normalization,
even when the oscillation is much faster than the time support. -/
theorem cosineSquareMass_half_le (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (hmass : (∫ s : ℝ, ρ s)=1) (t : ℝ)
    (hcos : 0 ≤ ∫ s : ℝ, ρ s*Real.cos (2*(t*s))) :
    1/2 ≤ cosineSquareMass ρ t := by
  have hi : Integrable ρ := hρ.integrable_of_hasCompactSupport hc
  have hi' : Integrable (fun s : ℝ => ρ s*Real.cos (2*(t*s))) :=
    (hρ.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have he : cosineSquareMass ρ t =
      ((∫ s : ℝ, ρ s)+(∫ s : ℝ, ρ s*Real.cos (2*(t*s))))/2 := by
    unfold cosineSquareMass
    rw [← integral_add hi hi',← integral_div]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by
      dsimp only
      rw [Real.cos_two_mul]
      ring)
  rw [he,hmass]
  linarith

def normalizedCosineWeight (ρ : ℝ → ℝ) (t : ℝ) (s : ℝ) : ℂ :=
  (ρ s*Real.cos (t*s)/cosineSquareMass ρ t : ℝ)

theorem normalizedCosineWeight_continuous (ρ : ℝ → ℝ) (hρ : Continuous ρ) (t : ℝ) :
    Continuous (normalizedCosineWeight ρ t) := by
  unfold normalizedCosineWeight
  fun_prop

theorem normalizedCosineWeight_support (ρ : ℝ → ℝ) (t : ℝ) :
    Function.support (normalizedCosineWeight ρ t) ⊆ Function.support ρ := by
  intro s hs
  by_contra hz
  have hz' : ρ s=0 := by simpa only [Function.mem_support,not_not] using hz
  exact hs (by simp only [normalizedCosineWeight,hz',zero_mul,zero_div,Complex.ofReal_zero])

theorem normalizedCosineWeight_compact (ρ : ℝ → ℝ)
    (hc : HasCompactSupport ρ) (t : ℝ) : HasCompactSupport (normalizedCosineWeight ρ t) := by
  apply HasCompactSupport.intro hc
  intro s hs
  by_contra hn
  exact hs (subset_tsupport ρ (normalizedCosineWeight_support ρ t hn))

/-- Exact central-frequency normalization for the actual weight. -/
theorem normalizedCosineWeight_normalization (ρ : ℝ → ℝ) (t : ℝ)
    (hpos : 0 < cosineSquareMass ρ t) :
    (∫ s : ℝ, normalizedCosineWeight ρ t s*(Real.cos (t*s):ℂ))=1 := by
  have he : (fun s : ℝ => normalizedCosineWeight ρ t s*(Real.cos (t*s):ℂ)) =
      fun s => ((ρ s*Real.cos (t*s)^2/cosineSquareMass ρ t : ℝ):ℂ) := by
    funext s
    rw [normalizedCosineWeight,← Complex.ofReal_mul]
    congr 1
    ring
  rw [he,integral_complex_ofReal,integral_div]
  change ((cosineSquareMass ρ t/cosineSquareMass ρ t : ℝ):ℂ)=1
  rw [div_self hpos.ne',Complex.ofReal_one]

/-- Uniform L1 mass of the normalized packet. This is independent of
both the frequency and any subsequent dilation of the time support. -/
theorem normalizedCosineWeight_norm_integral_le (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (hnonneg : ∀ s, 0 ≤ ρ s)
    (hmass : (∫ s : ℝ, ρ s)=1) (t : ℝ)
    (hhalf : 1/2 ≤ cosineSquareMass ρ t) :
    (∫ s : ℝ, ‖normalizedCosineWeight ρ t s‖) ≤ 2 := by
  have hpos : 0 < cosineSquareMass ρ t := by linarith
  have hi : Integrable ρ := hρ.integrable_of_hasCompactSupport hc
  have hw : Integrable (normalizedCosineWeight ρ t) :=
    (normalizedCosineWeight_continuous ρ hρ t).integrable_of_hasCompactSupport
      (normalizedCosineWeight_compact ρ hc t)
  calc
    _ ≤ ∫ s : ℝ, ρ s/cosineSquareMass ρ t := by
      apply integral_mono hw.norm (hi.div_const _)
      intro s
      simp only [normalizedCosineWeight,Complex.norm_real,Real.norm_eq_abs,
        abs_div,abs_mul,abs_of_nonneg (hnonneg s),abs_of_pos hpos]
      apply div_le_div_of_nonneg_right _ hpos.le
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hnonneg s)
    _ = 1/cosineSquareMass ρ t := by rw [integral_div,hmass]
    _ ≤ 2 := (div_le_iff₀ hpos).mpr (by linarith)

#print axioms cosineSquareMass_half_le
#print axioms normalizedCosineWeight_normalization
#print axioms normalizedCosineWeight_norm_integral_le

end QuantitativeMaass
