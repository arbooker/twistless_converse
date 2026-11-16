module

public import QuantitativeMaassPoincareContinuityV1
public import QuantitativeMaassPoincareWeightedSeedV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

theorem complex_toLp_norm_sq {A : Type*} [MeasurableSpace A]
    {μ : Measure A} (f : A → ℂ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℝ), L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Convergence of square-energy errors gives convergence of the actual
complex L² equivalence classes. -/
theorem tendsto_toLp_of_square_energy {A : Type*} [MeasurableSpace A]
    {μ : Measure A} (f : ℕ → A → ℂ) (hf : ∀ n, MemLp (f n) 2 μ)
    (g : A → ℂ) (hg : MemLp g 2 μ)
    (he : Tendsto (fun n => ∫ x, ‖f n x-g x‖^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn (n : ℕ) : ‖(hf n).toLp (f n)-hg.toLp g‖^2=
      ∫ x, ‖f n x-g x‖^2 ∂μ := by
    rw [← MemLp.toLp_sub]
    exact complex_toLp_norm_sq _ ((hf n).sub hg)
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
    simpa only [hn] using he
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto (fun n => Real.sqrt (‖(hf n).toLp (f n)-hg.toLp g‖^2)) atTop
    (𝓝 (Real.sqrt 0)) at ht
  simpa only [Function.comp_apply,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using ht

#print axioms complex_toLp_norm_sq
#print axioms tendsto_toLp_of_square_energy

end QuantitativeMaass
