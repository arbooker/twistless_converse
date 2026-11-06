module

public import FinitenessAllLevelMellinNormalizationV1
public import FinitenessAllLevelFrickeLimitsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelContinuation

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay FinitenessAllLevelMellinNormalization
open scoped Topology

/-- The original entire finite-order continuation is recovered from the
actual Fourier Fricke law and individual coefficient growth. -/
theorem continuation_of_fricke {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {f : ℕ → ℂ}
    (hf0 : f 0 = 0) {τ : ℝ} (hg : f =O[atTop] (fun n : ℕ => (n : ℝ) ^ τ))
    (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier (fullCoefficients f k) z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier (fullCoefficients f k) (-1 / ((N : ℂ) * z))) :
    Continuation N k f := by
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨hd, hb, hFE⟩ := FinitenessAllLevelMellinPair.mellin_entire hN hk
    (fullCoefficients f k) (polynomial_bound hf0 hg k) (fullCoefficients_zero hf0 k) ε hε0 hfr
  refine ⟨completion N k f, ?_, ?_, completion_eq hN hf0 hg, ε, hε, ?_⟩
  · exact (differentiable_const _).mul
      (hd.comp (differentiable_id.add (differentiable_const _)))
  · exact FinitenessInputBounds.bound_finiteOrder (FinitenessFiniteOrder.mul
      (FinitenessInputBounds.bound_const (constant N k))
      (FinitenessInputBounds.bound_shift hb (((k : ℂ) - 1) / 2)))
  · intro s
    simp only [completion]
    rw [hFE, show (k : ℂ) - (s + ((k : ℂ) - 1) / 2) =
      1 - s + ((k : ℂ) - 1) / 2 by ring]
    ring

/-- Coefficient limits of fixed-growth original solutions retain their
entire finite-order continuation. This is proved through the Fricke limit
and split Mellin construction, rather than assuming continuation is closed. -/
theorem limit_isSolution {N k : ℕ} {σ : ℝ} (hN : 0 < N) (hk : 0 < k)
    {a : ℕ → ℕ → ℂ} {f : ℕ → ℂ} (ha : ∀ j, a j ∈ FinitenessPaper2.E N k σ)
    (ht : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (f n))) :
    IsSolution N k f := by
  have hf : f ∈ closure (FinitenessPaper2.E N k σ) :=
    mem_closure_of_tendsto (tendsto_pi_nhds.mpr ht) (Eventually.of_forall ha)
  have he := FinitenessPaper2.closure_eulerData hN hf
  obtain ⟨ε, hε, hfr⟩ := FinitenessAllLevelFrickeLimits.fricke_limit hN ha ht
  exact { toEulerData := he
          continuation := continuation_of_fricke hN hk he.zero
            (FinitenessPaper2.closure_growth hN hf) ε hε hfr }

#print axioms continuation_of_fricke
#print axioms limit_isSolution

end FinitenessAllLevelContinuation
