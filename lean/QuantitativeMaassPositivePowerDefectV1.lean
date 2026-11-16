module

public import QuantitativeMaassWaveSpectrumV1
public import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

/-- A uniform polynomial bound at the endpoint zero; no spectral gap is
needed for the source filter after a bounded change of metric. -/
theorem power_defect_scalar {x : ℝ} (hx : 0≤x) (hx1 : x≤1) (n : ℕ) :
    x^n*(1-x)≤1/((n:ℝ)+1) := by
  have hsum : ((n:ℝ)+1)*x^n≤∑ i∈Finset.range (n+1),x^i := by
    calc
      _ = ∑ _i∈Finset.range (n+1),x^n := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi =>
        pow_le_pow_of_le_one hx hx1 (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  have hh := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hx1)
  rw [geom_sum_mul_neg] at hh
  apply (le_div_iff₀ (by positivity : 0<(n:ℝ)+1)).mpr
  nlinarith only [hh,pow_nonneg hx (n+1)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact functional calculus realization of the finite residual polynomial. -/
theorem power_defect_cfc (A : H→L[ℂ]H) (hA : IsSelfAdjoint A) (n : ℕ) :
    A^n*(1-A)=cfc (fun s : ℝ => s^n*(1-s)) A := by
  rw [cfc_mul (fun s : ℝ => s^n) (fun s : ℝ => 1-s) A
    (continuous_id.pow n).continuousOn (continuous_const.sub continuous_id).continuousOn,
    cfc_pow_id A n hA,cfc_sub (fun _ : ℝ => 1) (fun s : ℝ => s) A
      continuous_const.continuousOn continuous_id.continuousOn,
    cfc_id' ℝ A hA,cfc_const (1:ℝ) A hA,map_one]

theorem positive_power_defect_norm (A : H→L[ℂ]H) (hA : A.IsPositive)
    (hn : ‖A‖≤1) (n : ℕ) : ‖A^n*(1-A)‖≤1/((n:ℝ)+1) := by
  rw [power_defect_cfc A hA.isSelfAdjoint n]
  apply norm_cfc_le (by positivity)
  intro s hs
  obtain ⟨hs0,hs1⟩ := Wave.positiveContraction_spectrum_bound A hA hn hs
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg hs0 _) (sub_nonneg.mpr hs1))]
  exact power_defect_scalar hs0 hs1 n

/-- The sandwiched positive defect has the sharper squared-power bound. -/
theorem positive_power_sandwich_norm (A : H→L[ℂ]H) (hA : A.IsPositive)
    (hn : ‖A‖≤1) (m : ℕ) : ‖A^m*(1-A)*A^m‖≤1/(((2*m:ℕ):ℝ)+1) := by
  have he : A^m*(1-A)*A^m=A^(2*m)*(1-A) := by
    rw [mul_sub,sub_mul,mul_one,←pow_add,←pow_succ,←pow_add]
    rw [mul_sub,mul_one,←pow_succ]
    congr 1 <;> congr 1 <;> omega
  rw [he]
  exact positive_power_defect_norm A hA hn (2*m)

#print axioms power_defect_scalar
#print axioms power_defect_cfc
#print axioms positive_power_defect_norm
#print axioms positive_power_sandwich_norm
end QuantitativeMaass
