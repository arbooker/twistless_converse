module

public import QuantitativeMaassRegularTraceLinearityV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
    [TopologicalSpace α] [DiscreteTopology α]

omit [TopologicalSpace α] [DiscreteTopology α] in
/-- Compressing a bounded family by a finite projection preserves its signed
trace after inserting that projection on the right. -/
theorem signedTrace_projection_compression (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (E B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hE : ∀ x,IsStarProjection (E x))
    (hmE : ∀ g h,Measurable (fun x => matrix (E x) g h))
    (hmB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hcE : Covariant E) (hcB : Covariant B)
    (hf : trace μ E<∞) {C : ℝ} (hb : ∀ x,‖B x‖≤C) :
    signedTrace μ (fun x => E x*B x*E x)=signedTrace μ (fun x => B x*E x) := by
  have ha (x : α) : (E x).adjoint=E x := by
    rw [←ContinuousLinearMap.star_eq_adjoint]
    exact (hE x).isSelfAdjoint.star_eq
  have he (x : α) : (E x).adjoint.comp (E x)=E x := by
    rw [ha]
    exact (hE x).isIdempotentElem.eq
  have hfg : trace μ (fun x => (E x).adjoint.comp (E x))<∞ := by simpa only [he] using hf
  have hh := signedTrace_bounded_sandwich μ hmp E B hmE hmB hcE hcB hfg hb
  simp only [he] at hh
  simpa only [ha,mul_def,comp_assoc] using hh

/-- Exact complement trace identity in the semifinite regular setting.
Every use of linearity has an integrable rooted diagonal. -/
theorem signedTrace_projection_complement (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (F E : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hmF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hmE : ∀ g h,Measurable (fun x => matrix (E x) g h))
    (hcF : Covariant F) (hcE : Covariant E)
    (hp : ∀ x,0≤F x) (hE : ∀ x,IsStarProjection (E x))
    {K : ℝ} (hn : ∀ x,‖F x‖≤K) (hf : trace μ F<∞) (he : trace μ E<∞) :
    signedTrace μ (fun x => (1-E x)*F x*(1-E x))=
      signedTrace μ F-signedTrace μ E-signedTrace μ (fun x => F x*E x-E x) := by
  have hEn (x : α) : ‖E x‖≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hE x).nonneg).mpr (hE x).le_one
  have hEa (x : α) : (E x).adjoint=E x := by
    rw [←ContinuousLinearMap.star_eq_adjoint]
    exact (hE x).isSelfAdjoint.star_eq
  have hFa (x : α) : (F x).adjoint=F x := by
    rw [←ContinuousLinearMap.star_eq_adjoint]
    exact (IsSelfAdjoint.of_nonneg (hp x)).star_eq
  have hiF := positive_diagonal_integrable μ hmp F hmF hcF hp hn hf
  have hiE := positive_diagonal_integrable μ hmp E hmE hcE (fun x => (hE x).nonneg) hEn he
  have hiFE := positive_weight_diagonal_integrable μ hmp E F hmE hmF hcE hcF
    (fun x => (hE x).nonneg) hEn hn he
  change Integrable (fun x => rootDiagonal (F x*E x)) μ at hiFE
  have hroot (x : α) : rootDiagonal (E x*F x)=rootDiagonal (F x*E x) := by
    have ha : (F x*E x).adjoint=E x*F x := by
      change ((F x).comp (E x)).adjoint=(E x).comp (F x)
      rw [adjoint_comp,hEa,hFa]
    rw [rootDiagonal_apply,←ha,matrix_adjoint,Complex.conj_re]
    rfl
  have hiEF : Integrable (fun x => rootDiagonal (E x*F x)) μ := by
    simpa only [hroot] using hiFE
  have hgram (x : α) : (E x).adjoint.comp (E x)=E x := by
    rw [hEa]
    exact (hE x).isIdempotentElem.eq
  have hfg : trace μ (fun x => (E x).adjoint.comp (E x))<∞ := by simpa only [hgram] using he
  have hiEFE : Integrable (fun x => rootDiagonal (E x*F x*E x)) μ := by
    have hh := bounded_sandwich_diagonal_integrable μ hmp E F hmE hmF hcE hfg hn
    simpa only [hEa,mul_def,comp_assoc,rootDiagonal_apply] using hh
  have hcomp := signedTrace_projection_compression μ hmp E F hE hmE hmF hcE hcF he hn
  have hcross : signedTrace μ (fun x => E x*F x)=signedTrace μ (fun x => F x*E x) := by
    change (∫ x,rootDiagonal (E x*F x) ∂μ)=(∫ x,rootDiagonal (F x*E x) ∂μ)
    simp only [hroot]
  have hx := signedTrace_sub_of_integrable μ (fun x => F x*E x) E hiFE hiE
  have hdiag (x : α) : rootDiagonal ((1-E x)*F x*(1-E x))=
      rootDiagonal (F x)-rootDiagonal (F x*E x)-rootDiagonal (E x*F x)+rootDiagonal (E x*F x*E x) := by
    rw [show (1-E x)*F x*(1-E x)=F x-F x*E x-E x*F x+E x*F x*E x by
      simp only [sub_mul,mul_sub,one_mul,mul_one]; abel,
      map_add,map_sub,map_sub]
  change (∫ x,rootDiagonal ((1-E x)*F x*(1-E x)) ∂μ)=_
  simp only [hdiag]
  have hlin₁ := integral_add ((hiF.sub hiFE).sub hiEF) hiEFE
  have hlin₂ := integral_sub (hiF.sub hiFE) hiEF
  have hlin₃ := integral_sub hiF hiFE
  simp only [Pi.sub_apply] at hlin₁ hlin₂ hlin₃
  rw [hlin₁,hlin₂,hlin₃]
  change signedTrace μ F-signedTrace μ (fun x => F x*E x)-
    signedTrace μ (fun x => E x*F x)+signedTrace μ (fun x => E x*F x*E x)=_
  rw [hcross,hcomp,hx]
  ring

#print axioms signedTrace_projection_compression
#print axioms signedTrace_projection_complement
end AsymptoticRegularTrace
