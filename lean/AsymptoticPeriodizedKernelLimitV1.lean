module

public import AsymptoticCylinderKernelPeriodizationV1
public import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane Filter AsymptoticBergmanDecay
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem translated_base_square_summable (z u : ℍ) :
    Summable (fun n : ℤ => ‖base (translate z n) u‖^2) := by
  have hs : Summable (fun n : ℤ => (((difference z u : ℂ)+n)^2)⁻¹) := by
    simpa only [Int.cast_one, one_mul, zpow_ofNat] using
      EisensteinSeries.linear_right_summable (difference z u : ℂ) 1 (k:=2) (by norm_num)
  have hh := hs.norm.mul_left (‖2*Complex.I*(Real.sqrt (z.im*u.im) : ℂ)‖^2)
  apply hh.congr
  intro n
  rw [base_translate, norm_div, div_pow]
  simp only [norm_inv, norm_pow, difference]
  ring

theorem translated_base_power_summable (h : ℕ) (z u : ℍ) :
    Summable (fun n : ℤ => base (translate z n) u^(2*h+2)) := by
  apply Summable.of_norm_bounded (translated_base_square_summable z u)
  intro n
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (norm_base_le_one _ _) (by omega)

theorem translate_injective (z : ℍ) : Function.Injective (translate z) := by
  intro n m h
  have hc := congrArg UpperHalfPlane.coe h
  change (z : ℂ)+n = (z : ℂ)+m at hc
  exact Int.cast_injective (add_left_cancel hc)

noncomputable def returnValue (z u : ℍ) : ℂ :=
  if ∃ n : ℤ, translate z n = u then 1 else 0

theorem returnValue_eq_sum (z u : ℍ) :
    returnValue z u = ∑' n : ℤ, if translate z n = u then (1 : ℂ) else 0 := by
  classical
  by_cases h : ∃ n : ℤ, translate z n = u
  · obtain ⟨j, hj⟩ := h
    rw [returnValue, ite_eq_left ⟨j, hj⟩, tsum_eq_single j]
    · simp [hj]
    · intro n hn
      have hne : translate z n ≠ u := by
        intro he
        exact hn (translate_injective z (he.trans hj.symm))
      simp [hne]
  · rw [returnValue, ite_eq_right h]
    symm
    calc
      _ = ∑' _n : ℤ, (0 : ℂ) := tsum_congr (fun n => ite_eq_right (fun hn => h ⟨n, hn⟩))
      _ = 0 := tsum_zero

/-- After normalization, the periodized kernel converges exactly to the
indicator of return modulo an integer translation. The summable square
bound justifies the infinite periodization, not just a finite truncation. -/
theorem periodized_kernel_tendsto (z u : ℍ) :
    Tendsto (fun h : ℕ => ∑' n : ℤ, base (translate z n) u^(2*h+2)) atTop
      (𝓝 (returnValue z u)) := by
  classical
  rw [returnValue_eq_sum]
  have hexp : Tendsto (fun h : ℕ => 2*h+2) atTop atTop :=
    tendsto_atTop_mono (fun h => by omega : ∀ h : ℕ, h ≤ 2*h+2) tendsto_id
  apply tendsto_tsum_of_dominated_convergence (translated_base_square_summable z u)
  · intro n
    by_cases h : translate z n = u
    · simp only [h, base_self, one_pow]
      exact tendsto_const_nhds
    · simp only [ite_eq_right h]
      exact (pow_tendsto_zero h).comp hexp
  · apply Eventually.of_forall
    intro h n
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) (norm_base_le_one _ _) (by omega)

#print axioms translated_base_square_summable
#print axioms translated_base_power_summable
#print axioms periodized_kernel_tendsto

end AsymptoticUnweightedKernel
