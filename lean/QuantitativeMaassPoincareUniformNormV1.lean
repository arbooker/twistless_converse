module

public import QuantitativeMaassPoincareNormBoundV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeMaass

/-- Uniform approximation on a fixed finite-measure support controls the
actual L² norm. The deliberately coarse constant avoids divisions by a
possibly zero support measure. -/
theorem compact_uniform_l2_norm_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (K : Set A) (hKm : MeasurableSet K) (hKf : μ K≠∞)
    (f : A → ℂ) (hf : MemLp f 2 μ) (hs : Function.support f ⊆ K)
    (δ : ℝ) (hδ : 0≤δ) (hb : ∀ x, ‖f x‖≤δ) :
    ‖hf.toLp f‖≤δ*((μ K).toReal+1) := by
  have hi : (∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ)≤ENNReal.ofReal (δ^2)*μ K := by
    calc
      _ ≤ ∫⁻ x, K.indicator (fun _ => ENNReal.ofReal (δ^2)) x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x∈K
        · rw [Set.indicator_of_mem hx]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)
        · have hz : f x=0 := by
            by_contra hne
            exact hx (hs hne)
          simp [hx,hz]
      _ = _ := by rw [lintegral_indicator hKm]; simp
  have hi' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKf) hi
  rw [square_energy_toReal f hf,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)] at hi'
  have hm := ENNReal.toReal_nonneg (a := μ K)
  have hn := norm_nonneg (hf.toLp f)
  have hp : 0≤δ*((μ K).toReal+1) := mul_nonneg hδ (by positivity)
  have hm' : (μ K).toReal≤((μ K).toReal+1)^2 := by nlinarith
  have hq := mul_le_mul_of_nonneg_left hm' (sq_nonneg δ)
  nlinarith

#print axioms compact_uniform_l2_norm_bound

end QuantitativeMaass
