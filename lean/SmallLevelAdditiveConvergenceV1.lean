module

public import SmallLevelFrickeMellinRemainderV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

theorem mellin_congr_positive {f g : ℝ → ℂ} (he : EqOn f g (Ioi 0)) (s : ℂ) :
    mellin f s=mellin g s := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [he hy]

theorem mellinConvergent_congr_positive {f g : ℝ → ℂ} (he : EqOn f g (Ioi 0)) (s : ℂ) :
    MellinConvergent f s ↔ MellinConvergent g s := by
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro y hy
  dsimp only
  rw [he hy]

/-- The common right half-plane includes actual Mellin integrability, so
later subtraction and finite Taylor integration use valid linearity rules. -/
theorem additive_convergence_halfplane {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      MellinConvergent (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)) s ∧
      mellin (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)) s=SmallLevelAdditive.transform a r s := by
  obtain ⟨B,hB⟩ := SmallLevelAdditive.common_halfplane ha ha0
  obtain ⟨K,C,hC,hbound⟩ := fourier_boundary_bound ha ha0
  refine ⟨max B (K:ℝ),fun r s hs => ⟨?_,(hB r s (lt_of_le_of_lt (le_max_left _ _) hs)).2⟩⟩
  have hzero : (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I))=O[𝓝[>] 0]
      (fun y : ℝ => y^(-(K:ℝ))) := by
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin] with y hy
    change 0<y at hy
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hy.le _),Real.rpow_neg hy.le,
      Real.rpow_natCast]
    simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,
      zero_add,div_eq_mul_inv] using hbound ((r:ℂ)+(y:ℂ)*I) (by simpa using hy)
  have hlocal : LocallyIntegrableOn (fun y : ℝ => fourier a ((r:ℂ)+(y:ℂ)*I)) (Ioi 0) := by
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    intro y hy
    exact ((FinitenessFourierConstruction.holomorphic ha (by simpa using hy)).continuousAt.comp
      (by fun_prop)).continuousWithinAt
  exact mellinConvergent_of_isBigO_rpow hlocal (fourier_ray_rapid ha ha0 r (-(s.re+1)))
    (lt_add_one _) hzero (lt_of_le_of_lt (le_max_right _ _) hs)

#print axioms mellin_congr_positive
#print axioms mellinConvergent_congr_positive
#print axioms additive_convergence_halfplane

end SmallLevelTaylor
