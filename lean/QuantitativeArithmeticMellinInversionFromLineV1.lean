module
public import Mathlib.Analysis.MellinInversion
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticMellinInversionFromLine
open Complex MeasureTheory

theorem inverse_of_line (F : ℝ → ℂ) (Q : ℂ → ℂ) (σ : ℝ)
    (hF : MellinConvergent F σ) (hQ : VerticalIntegrable Q σ)
    (he : ∀ t : ℝ,mellin F ((σ:ℂ)+(t:ℂ)*I)=Q ((σ:ℂ)+(t:ℂ)*I))
    {y : ℝ} (hy : 0<y) (hc : ContinuousAt F y) : mellinInv σ Q y=F y := by
  have hv : VerticalIntegrable (mellin F) σ := by
    apply hQ.congr
    exact Filter.Eventually.of_forall (fun t => (he t).symm)
  calc
    _ = mellinInv σ (mellin F) y := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [he t])
    _ = _ := mellinInv_mellin_eq σ F hy hF hv hc
#print axioms inverse_of_line
end QuantitativeArithmeticMellinInversionFromLine
