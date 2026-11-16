module

public import QuantitativeMaassRegularCyclicProductsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Integrability of a bounded error supported by a finite projection. -/
theorem right_supported_diagonal_integrable (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (E X : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hE : ∀ x,IsStarProjection (E x))
    (hmE : ∀ g h,Measurable (fun x => matrix (E x) g h))
    (hmX : ∀ g h,Measurable (fun x => matrix (X x) g h))
    (hcX : Covariant X) (hf : trace μ E<∞)
    {D : ℝ} (hn : ∀ x,‖X x‖≤D) (hs : ∀ x,X x*E x=X x) :
    Integrable (fun x => rootDiagonal (X x)) μ := by
  have hg (x : α) : (E x).adjoint.comp (E x)=E x := by
    rw [←ContinuousLinearMap.star_eq_adjoint,(hE x).isSelfAdjoint.star_eq]
    exact (hE x).isIdempotentElem.eq
  have hfe : trace μ (fun x => (E x).adjoint.comp (E x))<∞ := by simpa only [hg] using hf
  have hfx := trace_gram_comp_finite_of_bound μ X E hn hfe
  change trace μ (fun x => (X x*E x).adjoint.comp (X x*E x))<∞ at hfx
  simp only [hs] at hfx
  have hh := finite_gram_product_integrable μ hmp X E hmX hmE hcX hfx hfe
  simpa only [hs] using hh

/-- A left-supported error also pays only its finite supporting projection,
after cyclicity of two finite-energy factors. -/
theorem left_supported_weight_trace_bound (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (E B Y : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hE : ∀ x,IsStarProjection (E x))
    (hmE : ∀ g h,Measurable (fun x => matrix (E x) g h))
    (hmB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hmY : ∀ g h,Measurable (fun x => matrix (Y x) g h))
    (hcE : Covariant E) (hcB : Covariant B) (hcY : Covariant Y)
    (hf : trace μ E<∞) {C δ : ℝ} (hC : 0≤C) (hδ : 0≤δ)
    (hb : ∀ x,‖B x‖≤C) (hy : ∀ x,‖Y x‖≤δ) (hs : ∀ x,E x*Y x=Y x) :
    |signedTrace μ (fun x => B x*Y x)|≤C*δ*(trace μ E).toReal ∧
      Integrable (fun x => rootDiagonal (B x*Y x)) μ := by
  have hg (x : α) : (E x).adjoint.comp (E x)=E x := by
    rw [←ContinuousLinearMap.star_eq_adjoint,(hE x).isSelfAdjoint.star_eq]
    exact (hE x).isIdempotentElem.eq
  have hfe : trace μ (fun x => (E x).adjoint.comp (E x))<∞ := by simpa only [hg] using hf
  have hfBE := trace_gram_comp_finite_of_bound μ B E hb hfe
  have hfY := trace_gram_right_comp_finite μ hmp E Y hmE hmY hcE hcY hfe hy
  change trace μ (fun x => (E x*Y x).adjoint.comp (E x*Y x))<∞ at hfY
  simp only [hs] at hfY
  have hmBE := matrix_comp_measurable B E hmB hmE
  have hcBE := covariant_comp B E hcB hcE
  have hcyc := signedTrace_finite_gram_mul_comm μ hmp (fun x => B x*E x) Y hmBE hmY hcBE hcY hfBE hfY
  have hleft (x : α) : B x*E x*Y x=B x*Y x := by rw [mul_assoc,hs]
  simp only [hleft] at hcyc
  have hEn (x : α) : ‖E x‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hE x).nonneg).mpr (hE x).le_one
  have hn (x : α) : ‖Y x*(B x*E x)‖≤C*δ := by
    calc
      _ ≤ ‖Y x‖*(‖B x‖*‖E x‖) := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ δ*(C*1) := mul_le_mul (hy x) (mul_le_mul (hb x) (hEn x) (norm_nonneg _) hC)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hδ
      _ = _ := by ring
  have hs' (x : α) : Y x*(B x*E x)*E x=Y x*(B x*E x) := by
    simp only [mul_assoc,(hE x).isIdempotentElem.eq]
  have hh := signedTrace_right_supported_bound μ hmp E (fun x => Y x*(B x*E x)) hE hmE
    (matrix_comp_measurable _ _ hmY hmBE) hcE (covariant_comp _ _ hcY hcBE) hf hn hs'
  rw [←hcyc] at hh
  have hi := finite_gram_product_integrable μ hmp (fun x => B x*E x) Y hmBE hmY hcBE hfBE hfY
  simp only [hleft] at hi
  exact ⟨hh,hi⟩

#print axioms right_supported_diagonal_integrable
#print axioms left_supported_weight_trace_bound
end AsymptoticRegularTrace
