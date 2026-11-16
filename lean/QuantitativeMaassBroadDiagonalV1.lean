module

public import QuantitativeMaassBroadSpectralMassV1
public import QuantitativeMaassBroadCorrespondenceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap

namespace QuantitativeMaass

/-- Exact spherical identity for the actual translated convolution square. -/
theorem broadTranslatedProfile_identity (L : ℝ) (hL : 0 < L) (t τ : ℝ) :
    broadTranslatedProfile L hL t τ 1 = (1/(4*Real.pi):ℂ) *
      (∫ r : ℝ, (Real.cos (τ*r):ℂ) *
        (cosinePacket (broadTimeWeight L t) r * cosinePacket (broadTimeWeight L t) r) *
        ((r*Real.tanh (Real.pi*r):ℝ):ℂ)) := by
  unfold broadTranslatedProfile broadTranslatedSquare
  rw [evenTimeTranslate_spherical_identity _ ((timeConvolution _ _).smooth ⊤)
    (timeConvolution_even _ _ (broadTimeWeight_even L t) (broadTimeWeight_even L t))
    (timeConvolution_compact _ _ (broadTimeWeight_compact L hL t) (broadTimeWeight_compact L hL t))]
  simp_rw [cosinePacket_timeConvolution (broadTimeSchwartz L hL t) (broadTimeSchwartz L hL t)
    (broadTimeWeight_even L t) (broadTimeWeight_even L t)]
  rfl

/-- The spherical identity term has the required linear central-frequency
growth, uniformly over every translation used by the finite-place filter. -/
theorem broadTranslatedProfile_diagonal_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 0 < L) (t τ : ℝ),
      ‖broadTranslatedProfile L hL t τ 1‖ ≤ C*(|t| * L + L^2) := by
  obtain ⟨C,hC,hbound⟩ := broadTimeWeight_spectral_mass_bound
  refine ⟨(1/(4*Real.pi))*C, by positivity, ?_⟩
  intro L hL t τ
  have hm := hbound L hL t
  rw [broadTranslatedProfile_identity, norm_mul]
  have hscalar : ‖(1/(4*Real.pi):ℂ)‖ = (1/(4*Real.pi):ℝ) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hscalar]
  have hb : ‖∫ r : ℝ, (Real.cos (τ*r):ℂ) *
        (cosinePacket (broadTimeWeight L t) r * cosinePacket (broadTimeWeight L t) r) *
        ((r*Real.tanh (Real.pi*r):ℝ):ℂ)‖ ≤
      ∫ r : ℝ, |r| * ‖cosinePacket (broadTimeWeight L t) r‖^2 := by
    apply norm_integral_le_of_norm_le hm.1
    filter_upwards with r
    have htanh : |Real.tanh (Real.pi*r)| ≤ 1 :=
      abs_le.mpr ⟨(Real.neg_one_lt_tanh _).le, (Real.tanh_lt_one _).le⟩
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ 1*(‖cosinePacket (broadTimeWeight L t) r‖ *
          ‖cosinePacket (broadTimeWeight L t) r‖) * (|r| * 1) := by
        gcongr
        exact Real.abs_cos_le_one _
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left (hb.trans hm.2)
    (by positivity : (0:ℝ) ≤ 1/(4*Real.pi))
  simpa only [mul_assoc] using hh

#print axioms broadTranslatedProfile_identity
#print axioms broadTranslatedProfile_diagonal_bound

end QuantitativeMaass
