module

public import QuantitativeMaassBroadDiagonalV1
public import QuantitativeMaassMixedHeckeDensityV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap

namespace QuantitativeMaass

def broadSpectralWeight (L t r : ℝ) : ℝ :=
  ‖cosinePacket (broadTimeWeight L t) r‖^2*windowPlancherelWeight r

theorem broadSpectralWeight_nonneg (L t r : ℝ) : 0 ≤ broadSpectralWeight L t r :=
  mul_nonneg (sq_nonneg _) (windowPlancherelWeight_nonneg r)

theorem broadSpectralWeight_le (L t r : ℝ) :
    broadSpectralWeight L t r ≤ |r| * ‖cosinePacket (broadTimeWeight L t) r‖^2 := by
  have htanh : |Real.tanh (Real.pi*r)| ≤ 1 :=
    abs_le.mpr ⟨(Real.neg_one_lt_tanh _).le, (Real.tanh_lt_one _).le⟩
  have hw : windowPlancherelWeight r ≤ |r| := by
    calc
      _ ≤ |windowPlancherelWeight r| := le_abs_self _
      _ = |r| * |Real.tanh (Real.pi*r)| := abs_mul _ _
      _ ≤ |r| := by nlinarith [abs_nonneg r]
  exact (mul_le_mul_of_nonneg_left hw (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem broadSpectralWeight_continuous (L : ℝ) (hL : 0 < L) (t : ℝ) :
    Continuous (broadSpectralWeight L t) := by
  have he : cosinePacket (broadTimeWeight L t) = angularFourier (broadTimeSchwartz L hL t) := by
    funext r
    exact cosinePacket_eq_angularFourier (broadTimeSchwartz L hL t) (broadTimeWeight_even L t) r
  unfold broadSpectralWeight
  rw [he]
  exact ((angularFourier (broadTimeSchwartz L hL t)).continuous.norm.pow 2).mul
    windowPlancherelWeight_continuous

theorem broadSpectralWeight_mass_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 0 < L → ∀ t : ℝ,
      Integrable (broadSpectralWeight L t) ∧
      (∫ r : ℝ, broadSpectralWeight L t r) ≤ C*(|t| * L + L^2) := by
  obtain ⟨C,hC,hbound⟩ := broadTimeWeight_spectral_mass_bound
  refine ⟨C,hC,?_⟩
  intro L hL t
  have hh := hbound L hL t
  have hi : Integrable (broadSpectralWeight L t) :=
    hh.1.mono' (broadSpectralWeight_continuous L hL t).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (broadSpectralWeight_nonneg L t r)]
        exact broadSpectralWeight_le L t r))
  exact ⟨hi, (integral_mono hi hh.1 (broadSpectralWeight_le L t)).trans hh.2⟩

theorem broadSpectralWeight_integrable (L : ℝ) (hL : 0 < L) (t : ℝ) :
    Integrable (broadSpectralWeight L t) := by
  obtain ⟨_,_,h⟩ := broadSpectralWeight_mass_bound
  exact (h L hL t).1

/-- The translated identity is the cosine integral of the positive
spherical spectral weight of the concrete packet. -/
theorem broadTranslatedProfile_eq_mass (L : ℝ) (hL : 0 < L) (t τ : ℝ) :
    broadTranslatedProfile L hL t τ 1 =
      ((1/(4*Real.pi)*(∫ r : ℝ, Real.cos (τ*r)*broadSpectralWeight L t r):ℝ):ℂ) := by
  rw [broadTranslatedProfile_identity]
  have hs (r : ℝ) : cosinePacket (broadTimeWeight L t) r *
      cosinePacket (broadTimeWeight L t) r =
        (‖cosinePacket (broadTimeWeight L t) r‖^2:ℝ) := by
    have hz : star (cosinePacket (broadTimeWeight L t) r) =
        cosinePacket (broadTimeWeight L t) r := by
      unfold cosinePacket
      rw [Complex.star_def, ← integral_conj]
      apply integral_congr_ae
      filter_upwards with s
      rw [map_mul, Complex.conj_ofReal]
      exact congrArg (fun z : ℂ => z*(Real.cos (s*r):ℂ)) (broadTimeWeight_real L t s)
    calc
      _ = cosinePacket (broadTimeWeight L t) r * star (cosinePacket (broadTimeWeight L t) r) := by rw [hz]
      _ = _ := by rw [Complex.star_def, Complex.mul_conj']; norm_cast
  simp_rw [hs]
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  · simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  · apply integral_congr_ae
    filter_upwards with r
    simp only [broadSpectralWeight, windowPlancherelWeight, Complex.ofReal_mul]
    ring

#print axioms broadSpectralWeight_mass_bound
#print axioms broadTranslatedProfile_eq_mass

end QuantitativeMaass
