module

public import FinitenessGammaIntegrabilityV1
public import Mathlib.Analysis.MellinInversion

@[expose] public section

namespace FinitenessGammaMellin

open Complex MeasureTheory Set

noncomputable def exponential (x : ℝ) : ℂ := Real.exp (-x)

theorem mellin_exponential {s : ℂ} (hs : 0 < s.re) :
    mellin exponential s = Gamma s := by
  rw [Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  rfl

theorem exponential_convergent {σ : ℝ} (hσ : 0 < σ) :
    MellinConvergent exponential (σ : ℂ) := by
  simpa only [MellinConvergent, exponential, smul_eq_mul, mul_comm]
    using Complex.GammaIntegral_convergent (s := (σ : ℂ)) (by simpa using hσ)

theorem mellin_vertical {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegrable (mellin exponential) σ := by
  have hi : Integrable (fun t : ℝ => Gamma ((σ : ℂ)+(t : ℂ)*I)) := by
    simpa only [pow_zero, one_mul] using FinitenessGammaIntegrability.integrable σ hσ 0
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  exact (mellin_exponential (s := (σ : ℂ)+(t : ℂ)*I) (by simpa using hσ)).symm

/-- The inverse Mellin formula for Gamma, with ALL convergence hypotheses
proved. This is the kernel used when opening the L-series on a right line. -/
theorem inverse_gamma {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ Gamma x = Real.exp (-x) := by
  calc
    mellinInv σ Gamma x = mellinInv σ (mellin exponential) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [mellin_exponential (by simpa using hσ)]
    _ = exponential x := mellinInv_mellin_eq σ exponential hx
      (exponential_convergent hσ) (mellin_vertical hσ) (by unfold exponential; fun_prop)
    _ = Real.exp (-x) := rfl

#print axioms mellin_vertical
#print axioms inverse_gamma

end FinitenessGammaMellin
