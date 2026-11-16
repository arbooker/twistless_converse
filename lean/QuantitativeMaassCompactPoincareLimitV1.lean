module

public import QuantitativeMaassPoincareNormBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- On a fixed compact support, the actual periodization transports strong
square-integral convergence to the quotient measure. -/
theorem compact_poincare_square_tendsto {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [MeasurableSpace A] [MulAction G A]
    [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : Set A) (hK : IsCompact K) (f : ℕ → A → ℂ) (g : A → ℂ)
    (hf : ∀ n,Measurable (f n)) (hg : Measurable g)
    (hfs : ∀ n,Function.support (f n)⊆K) (hgs : Function.support g⊆K)
    (hfL : ∀ n,MemLp (f n) 2 μ) (hgL : MemLp g 2 μ)
    (he : Tendsto (fun n => ∫ x,‖f n x-g x‖^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,‖poincareSum (G := G) (f n) x-poincareSum (G := G) g x‖^2
      ∂μ.withDensity ρ) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := compact_poincare_uniform_norm_bound μ hmp ρ hρ hn K hK
  have hb (n : ℕ) :
      (∫ x,‖poincareSum (G := G) (f n) x-poincareSum (G := G) g x‖^2 ∂μ.withDensity ρ)
        ≤C^2*(∫ x,‖f n x-g x‖^2 ∂μ) := by
    have hs : Function.support (f n-g)⊆K := by
      intro x hx
      by_contra hnK
      have hf0 : f n x=0 := Function.notMem_support.mp (fun h => hnK (hfs n h))
      have hg0 : g x=0 := Function.notMem_support.mp (fun h => hnK (hgs h))
      exact hx (by simp only [Pi.sub_apply,hf0,hg0,sub_self])
    have hh := hbound (f n-g) ((hf n).sub hg) hs ((hfL n).sub hgL)
    have hh2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    rw [mul_pow,complex_toLp_norm_sq,complex_toLp_norm_sq] at hh2
    simpa only [poincareSum_sub_compact K hK (f n) g (hfs n) hgs,Pi.sub_apply] using hh2
  apply squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _)) hb
  simpa only [mul_zero] using he.const_mul (C^2)

#print axioms compact_poincare_square_tendsto

end QuantitativeMaass
