module

public import QuantitativeMaassCutoffOffBandSumV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- The energy frequency and the principal spectral parameter differ by
at most two, including the exceptional spectrum below one quarter. -/
theorem energy_principal_frequency_bounds (r : ℝ) (hr : 0≤r) :
    0≤Real.sqrt (1+r)-Real.sqrt (r-1/4) ∧
      Real.sqrt (1+r)-Real.sqrt (r-1/4)≤2 := by
  have hlow : Real.sqrt (r-1/4)≤Real.sqrt (1+r) :=
    Real.sqrt_le_sqrt (by linarith)
  refine ⟨sub_nonneg.mpr hlow,?_⟩
  have ha := Real.sq_sqrt (show 0≤1+r by linarith)
  have hb := Real.sqrt_nonneg (r-1/4)
  by_cases h : 0≤r-1/4
  · have hc := Real.sq_sqrt h
    nlinarith [Real.sqrt_nonneg (1+r)]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
    nlinarith [Real.sqrt_nonneg (1+r)]

/-- Separation in the principal parameter gives the separation used in
the closed energy-form commutator estimate. -/
theorem principal_separation_energy (r μ L : ℝ) (hr : 0≤r) (hμ : 0≤μ)
    (hsep : L+2≤|Real.sqrt (r-1/4)-Real.sqrt (μ-1/4)|) :
    L≤|Real.sqrt (1+r)-Real.sqrt (1+μ)| := by
  obtain ⟨hr0,hr2⟩ := energy_principal_frequency_bounds r hr
  obtain ⟨hμ0,hμ2⟩ := energy_principal_frequency_bounds μ hμ
  rcases le_total (Real.sqrt (r-1/4)) (Real.sqrt (μ-1/4)) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hsep
    have hh := neg_le_abs (Real.sqrt (1+r)-Real.sqrt (1+μ))
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hsep
    have hh := le_abs_self (Real.sqrt (1+r)-Real.sqrt (1+μ))
    linarith

/-- A unit input band and the complement of a wider band have explicit
energy separation. The extra three accounts for both changes of coordinate. -/
theorem outside_wide_band_energy_separation (r μ t L : ℝ)
    (hr : 0≤r) (hμ : 0≤μ)
    (hin : |Real.sqrt (μ-1/4)-t|≤1)
    (hout : L+3≤|Real.sqrt (r-1/4)-t|) :
    L≤|Real.sqrt (1+r)-Real.sqrt (1+μ)| := by
  apply principal_separation_energy r μ L hr hμ
  have htri := abs_add_le (Real.sqrt (r-1/4)-Real.sqrt (μ-1/4))
    (Real.sqrt (μ-1/4)-t)
  have he : Real.sqrt (r-1/4)-Real.sqrt (μ-1/4)+(Real.sqrt (μ-1/4)-t)=
      Real.sqrt (r-1/4)-t := by ring
  rw [he] at htri
  linarith

#print axioms energy_principal_frequency_bounds
#print axioms principal_separation_energy
#print axioms outside_wide_band_energy_separation

end QuantitativeMaass
