module

public import AsymptoticSignedCornerV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory Set ContinuousLinearMap AsymptoticOrbitDiagonal Filter
open scoped lp ENNReal Topology

variable {G α : Type*} [Group G] [MeasurableSpace α]

theorem signedTrace_sub (μ : Measure α) (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Integrable (fun x => (matrix (B x) 1 1).re) μ)
    (hC : Integrable (fun x => (matrix (C x) 1 1).re) μ) :
    signedTrace μ (fun x => B x-C x)=signedTrace μ B-signedTrace μ C := by
  have he (x : α) : matrix (B x-C x) 1 1=matrix (B x) 1 1-matrix (C x) 1 1 :=
    map_sub (matrixCLM 1 1) (B x) (C x)
  simp only [signedTrace,he,Complex.sub_re]
  exact integral_sub hB hC

variable [MulAction G α]

/-- Uniform norm errors cost at most the finite corner's area in the
signed trace. Both subtracted diagonals are proved integrable. -/
theorem norm_signedTrace_sub_le_corner (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) (hf : μ s<∞)
    (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) {CB CC δ : ℝ}
    (hmB : Measurable (fun x => matrix (B x) 1 1))
    (hmC : Measurable (fun x => matrix (C x) 1 1))
    (hB : ∀ x,‖B x‖≤CB) (hC : ∀ x,‖C x‖≤CC)
    (hpB : ∀ x,(B x).comp (corner s x)=B x) (hpC : ∀ x,(C x).comp (corner s x)=C x)
    (hd : ∀ x,‖B x-C x‖≤δ) :
    ‖signedTrace μ B-signedTrace μ C‖≤δ*(μ s).toReal := by
  rw [← signedTrace_sub μ B C
    (corner_diagonal_integrable μ hs hf B hmB hB hpB)
    (corner_diagonal_integrable μ hs hf C hmC hC hpC)]
  apply norm_signedTrace_le_corner μ hs hf _ hd
  intro x
  rw [sub_comp,hpB x,hpC x]

/-- Norm convergence in a fixed finite terminal corner yields trace
convergence, unlike norm convergence on the whole infinite-area space. -/
theorem signedTrace_tendsto_of_corner (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) (hf : μ s<∞)
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (CB : ℕ → ℝ) (CC : ℝ) (δ : ℕ → ℝ)
    (hmB : ∀ n,Measurable (fun x => matrix (B n x) 1 1))
    (hmC : Measurable (fun x => matrix (C x) 1 1))
    (hB : ∀ n x,‖B n x‖≤CB n) (hC : ∀ x,‖C x‖≤CC)
    (hpB : ∀ n x,(B n x).comp (corner s x)=B n x) (hpC : ∀ x,(C x).comp (corner s x)=C x)
    (hd : ∀ n x,‖B n x-C x‖≤δ n) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => signedTrace μ (B n)) atTop (𝓝 (signedTrace μ C)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => norm_signedTrace_sub_le_corner μ hs hf (B n) C (hmB n) hmC (hB n) hC (hpB n) hpC (hd n))
  simpa only [zero_mul] using hδ.mul_const (μ s).toReal

#print axioms norm_signedTrace_sub_le_corner
#print axioms signedTrace_tendsto_of_corner

end AsymptoticRegularTrace
