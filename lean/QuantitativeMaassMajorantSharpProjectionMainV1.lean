module

public import QuantitativeMaassEnlargedSharpProjectionMainV1
public import QuantitativeMaassMajorantSectorProjectionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter MeasureTheory ContinuousLinearMap AsymptoticSectorSigns
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticRegularTrace QuantitativeNewGap
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The literal normalized regular main term with a sharp spatial rectangle. -/
def originalMajorantSharpSectorProjectionMain (N : ℕ) (hN : 0<N) (e : Sector N)
    (δ C : ℝ) (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t : ℝ) : ℝ :=
  (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2 *
    enlargedSharpSectorProjectionMain N hN e δ C K hc ε t

/-- Removing the spatial smoothing preserves the normalized main term. -/
theorem originalMajorant_sharp_projection_main_decay (N : ℕ) (hN : 0<N) (e : Sector N)
    (δ C D : ℝ) (hδ : 0<δ) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (W : ℝ) (hD : 0≤D) (hDW : W+3≤D) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      ‖originalMajorantSharpSectorProjectionMain N hN e δ C K hc ε t-
        originalMajorantSectorProjectionMain N hN e δ C D hδ K hc ε t‖/(t*ε t)) atTop (𝓝 0) := by
  have hlim := (originalMajorant_normalization_sq_limit K ε
    (hε.mono (fun _ h => h.1)) hp).mul
    (enlarged_sharp_projection_main_decay N hN e δ C D hδ hC K hc he hK hm ε hε hp W hD hDW)
  rw [mul_zero] at hlim
  convert hlim using 1
  funext t
  dsimp only [originalMajorantSharpSectorProjectionMain,originalMajorantSectorProjectionMain]
  rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  ring

#print axioms originalMajorant_sharp_projection_main_decay
end QuantitativeMaass.Scheduled
