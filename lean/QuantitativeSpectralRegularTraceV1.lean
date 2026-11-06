module

public import QuantitativeSpectralCutV1
public import AsymptoticRegularSignedTraceV1
public import AsymptoticProjectionTraceV1

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralRegularTrace

open MeasureTheory ContinuousLinearMap InnerProductSpace QuantitativeSpectralCut
open AsymptoticRegularTrace
open scoped lp ENNReal InnerProduct

variable {G α : Type*} [Group G] [MeasurableSpace α]

private theorem projection_root (P : Submodule ℂ ℓ²(G,ℂ)) [CompleteSpace P] :
    (matrix P.starProjection 1 1).re = ‖P.starProjection (delta 1)‖^2 := by
  have h := matrix_gram P.starProjection (1 : G)
  have hs : P.starProjection.adjoint = P.starProjection := isSelfAdjoint_starProjection P
  have hp : P.starProjection.comp P.starProjection = P.starProjection :=
    P.isIdempotentElem_starProjection
  rwa [hs, hp] at h

/-- Rooted regular trace of a genuine high spectral cut. This is an
operator theorem: the cut is constructed from the positive part of `A-a I`.
Its regularity assumptions concern only measurable diagonals. No spectral
measure, rank bound, or spectral extraction inequality is assumed. -/
theorem trace_cut_majorant (μ : Measure α)
    (A : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hA : ∀ x, IsSelfAdjoint (A x))
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x, CompleteSpace (P x)]
    {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (hnorm : ∀ x, ‖A x‖ ≤ M)
    (hAP : ∀ x, (A x).comp (P x).starProjection = A x)
    (hmP : Measurable (fun x => matrix (P x).starProjection 1 1))
    (hmF : Measurable (fun x => matrix (highAt (A x) a).starProjection 1 1)) :
    trace μ A ≤ ENNReal.ofReal a * trace μ (fun x => (P x).starProjection) +
      ENNReal.ofReal M * trace μ (fun x => (highAt (A x) a).starProjection) := by
  let rP := fun x => (matrix (P x).starProjection 1 1).re
  let rF := fun x => (matrix (highAt (A x) a).starProjection 1 1).re
  have hp (x : α) : 0 ≤ rP x := by dsimp [rP]; rw [projection_root]; positivity
  have hf (x : α) : 0 ≤ rF x := by dsimp [rF]; rw [projection_root]; positivity
  have hpoint (x : α) : (matrix (A x) 1 1).re ≤ a*rP x + M*rF x := by
    have h := corner_quadratic_majorant (A x) (hA x) (P x) ha (hnorm x) (hAP x) (delta 1)
    dsimp [rP, rF]
    rw [projection_root, projection_root]
    rw [matrix, ← delta_inner]
    have he : (⟪delta 1, A x (delta 1)⟫_ℂ).re = (⟪A x (delta 1), delta 1⟫_ℂ).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rwa [he]
  have hmP' : Measurable (fun x => ENNReal.ofReal (rP x)) :=
    (Complex.continuous_re.measurable.comp hmP).ennreal_ofReal
  have hmF' : Measurable (fun x => ENNReal.ofReal (rF x)) :=
    (Complex.continuous_re.measurable.comp hmF).ennreal_ofReal
  have hmeas : Measurable (fun x => ENNReal.ofReal a * ENNReal.ofReal (rP x)) :=
    measurable_const.mul (Complex.continuous_re.measurable.comp hmP).ennreal_ofReal
  unfold trace
  calc
    (∫⁻ x, ENNReal.ofReal (matrix (A x) 1 1).re ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (a*rP x + M*rF x) ∂μ :=
      lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hpoint x))
    _ = (∫⁻ x, ENNReal.ofReal a * ENNReal.ofReal (rP x) +
          ENNReal.ofReal M * ENNReal.ofReal (rF x) ∂μ) := by
      congr 1
      funext x
      rw [ENNReal.ofReal_add (mul_nonneg ha (hp x)) (mul_nonneg hM (hf x)),
        ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hM]
    _ = _ := by
      rw [lintegral_add_left hmeas, lintegral_const_mul _ hmP', lintegral_const_mul _ hmF']

/-- Adjustable fresh-prime high-cut extraction for the actual rooted
regular trace. The only fresh-prime input is its previously proved first
moment identity; the spectral mass conclusion is derived here. -/
theorem fresh_cut_trace (μ : Measure α)
    (A : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hA : ∀ x, IsSelfAdjoint (A x))
    (P : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x, CompleteSpace (P x)]
    {n theta : ℝ} (hn : 0 < n) (htheta : 0 ≤ theta)
    (hnorm : ∀ x, ‖A x‖ ≤ 1)
    (hAP : ∀ x, (A x).comp (P x).starProjection = A x)
    (hmP : Measurable (fun x => matrix (P x).starProjection 1 1))
    (hmF : Measurable (fun x => matrix (highAt (A x) (theta/n)).starProjection 1 1))
    (hfinite : trace μ (fun x => (P x).starProjection) < ∞)
    (hfirst : (trace μ A).toReal = (trace μ (fun x => (P x).starProjection)).toReal/n) :
    (1-theta) * (trace μ (fun x => (P x).starProjection)).toReal/n ≤
      (trace μ (fun x => (highAt (A x) (theta/n)).starProjection)).toReal := by
  have ha := div_nonneg htheta hn.le
  have hFfinite := projection_trace_finite_of_le μ
    (fun x => highAt (A x) (theta/n)) P
    (fun x => highAt_le_corner (A x) (hA x) (P x) ha (hAP x)) hfinite
  have hbound := trace_cut_majorant μ A hA P ha zero_le_one hnorm hAP hmP hmF
  simp only [ENNReal.ofReal_one, one_mul] at hbound
  have hfinite' : ENNReal.ofReal (theta/n) * trace μ (fun x => (P x).starProjection) +
      trace μ (fun x => (highAt (A x) (theta/n)).starProjection) ≠ ∞ := by finiteness
  have hreal := ENNReal.toReal_mono hfinite' hbound
  rw [ENNReal.toReal_add (by finiteness) hFfinite.ne,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, hfirst] at hreal
  have he : (1-theta) * (trace μ (fun x => (P x).starProjection)).toReal/n =
      (trace μ (fun x => (P x).starProjection)).toReal/n -
        theta/n * (trace μ (fun x => (P x).starProjection)).toReal := by ring
  rw [he]
  linarith

#print axioms trace_cut_majorant
#print axioms fresh_cut_trace

end QuantitativeSpectralRegularTrace
