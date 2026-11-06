module

public import AsymptoticSignedCornerV1
public import AsymptoticHyperbolicAreaV1
public import AsymptoticRegularFoldedLowV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory Set ContinuousLinearMap AsymptoticOrbitDiagonal
open scoped lp ENNReal

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]

noncomputable def removeCorner (s : Set α) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (x : α) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  (1-corner s x).comp ((B x).comp (1-corner s x))

omit [MeasurableSpace α] in
theorem removeCorner_matrix (s : Set α) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (x : α) :
    matrix (removeCorner s B x) 1 1=sᶜ.indicator (fun x => matrix (B x) 1 1) x := by
  classical
  unfold removeCorner matrix
  by_cases hx : x∈s
  · simp [comp_apply,sub_apply,corner_delta,one_smul,hx]
  · simp [comp_apply,sub_apply,corner_delta,corner_apply,one_smul,hx]

theorem removeCorner_diagonal_integrable (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hi : Integrable (fun x => (matrix (B x) 1 1).re) μ) :
    Integrable (fun x => (matrix (removeCorner s B x) 1 1).re) μ := by
  have he : (fun x => (matrix (removeCorner s B x) 1 1).re)=
      sᶜ.indicator (fun x => (matrix (B x) 1 1).re) := by
    funext x
    rw [removeCorner_matrix]
    classical
    by_cases hx : x∈sᶜ <;> simp [hx]
  rw [he]
  exact hi.indicator hs.compl

/-- Removing any finite-area corner changes a bounded integrable rooted
trace by at most the norm bound times that area's measure. -/
theorem removeCorner_trace_bound (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) (hf : μ s<∞)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) {C : ℝ}
    (hB : ∀ x,‖B x‖≤C) (hi : Integrable (fun x => (matrix (B x) 1 1).re) μ) :
    ‖signedTrace μ B-signedTrace μ (removeCorner s B)‖≤C*(μ s).toReal := by
  have hc := removeCorner_diagonal_integrable μ hs B hi
  have he : (fun x => (matrix (B x) 1 1).re-(matrix (removeCorner s B x) 1 1).re)=
      s.indicator (fun x => (matrix (B x) 1 1).re) := by
    funext x
    rw [removeCorner_matrix]
    classical
    by_cases hx : x∈s <;> simp [hx]
  unfold signedTrace
  rw [← integral_sub hi hc,he]
  have hb : Integrable (s.indicator (fun _ : α => C)) μ :=
    (integrableOn_const hf.ne).integrable_indicator hs
  apply (norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall ?_)).trans_eq
  · rw [integral_indicator_const _ hs]
    simp only [smul_eq_mul,measureReal_def,mul_comm]
  · intro x
    classical
    by_cases hx : x∈s
    · rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx,Real.norm_eq_abs]
      apply (Complex.abs_re_le_norm _).trans
      calc
        ‖matrix (B x) 1 1‖≤‖B x‖*‖delta (1:G)‖ :=
          (lp.norm_apply_le_norm (by norm_num) (B x (delta 1)) 1).trans ((B x).le_opNorm _)
        _ ≤ C := by simpa only [root_delta_norm,mul_one] using hB x
    · simp [hx]

#print axioms removeCorner_matrix
#print axioms removeCorner_diagonal_integrable
#print axioms removeCorner_trace_bound

end AsymptoticRegularTrace

namespace AsymptoticRegularUpperCutoff

open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticHyperbolicArea
open AsymptoticRegularFoldedLow (Space)

noncomputable def cut (H : ℝ) (B : ℍ → Space →L[ℂ] Space) : ℍ → Space →L[ℂ] Space :=
  removeCorner (closedTerminal H) B

theorem trace_error {H : ℝ} (hH : 0<H) (B : ℍ → Space →L[ℂ] Space) {C : ℝ}
    (hB : ∀ z,‖B z‖≤C) (hi : Integrable (fun z => (matrix (B z) 1 1).re) volume) :
    ‖signedTrace volume B-signedTrace volume (cut H B)‖≤C/H := by
  have hf : (volume : Measure ℍ) (closedTerminal H)<⊤ := by
    rw [closed_terminal_area hH]
    exact ENNReal.ofReal_lt_top
  have hh := removeCorner_trace_bound volume (closedTerminal_measurable H) hf B hB hi
  simpa only [cut,closed_terminal_area hH,ENNReal.toReal_ofReal (inv_nonneg.mpr hH.le),div_eq_mul_inv] using hh

#print axioms trace_error

end AsymptoticRegularUpperCutoff
