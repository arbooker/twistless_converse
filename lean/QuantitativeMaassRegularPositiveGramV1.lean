module

public import QuantitativeMaassRegularGramTraceBoundV1
public import QuantitativeSpectralRegularEmbeddingV1
public import QuantitativeSpectralRegularOrderV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
open QuantitativeSpectralRegularAlgebra QuantitativeSpectralRegularEmbedding
open QuantitativeSpectralRegularOrder
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
    [TopologicalSpace α] [DiscreteTopology α]

/-- Positive bounded measurable covariant families have an actual measurable
covariant Gram factor, obtained inside the closed regular C*-algebra. -/
theorem positive_regular_gram_factor
    (hact : ∀ g : G,Measurable (fun x : α => g • x))
    (F : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (F x) g h)) (hc : Covariant F)
    {C : ℝ} (hn : ∀ x,‖F x‖≤C) (hp : ∀ x,0≤F x) :
    ∃ R : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ),
      (∀ g h,Measurable (fun x => matrix (R x) g h)) ∧ Covariant R ∧
      (∃ K : ℝ,0≤K ∧ ∀ x,‖R x‖≤K) ∧ ∀ x,(R x).adjoint.comp (R x)=F x := by
  have hu (x : α) : AsymptoticOrbitDiagonal.corner (G:=G) Set.univ x=1 := by
    ext1 v
    apply lp.ext
    funext g
    simp [AsymptoticOrbitDiagonal.corner_apply]
  let A := ofFamily hact Set.univ MeasurableSet.univ F C hn hm hc
    (fun x => by rw [hu];rfl) (fun x => by rw [hu];rfl)
  have hA : 0≤A := (pointwise_le_iff hact Set.univ MeasurableSet.univ 0 A).mp hp
  let R := CFC.sqrt A
  have hRR : star R*R=A := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq]
    exact CFC.sqrt_mul_sqrt_self A hA
  refine ⟨representation G α hact Set.univ MeasurableSet.univ R,
    representation_matrix_measurable _ _ _ _ _ R,representation_covariant _ _ _ _ _ R,
    ⟨‖R‖,norm_nonneg _,representation_norm_le _ _ _ _ _ R⟩,?_⟩
  intro x
  have hh := congrArg (fun T => representation G α hact Set.univ MeasurableSet.univ T x) hRR
  simpa only [representation_mul,representation_star,A,representation_ofFamily] using hh

/-- The bounded-weight estimate for a genuine positive regular family,
without a supplied square root or finite ambient trace assumption. -/
theorem signedTrace_positive_weight_bound (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (F B : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hcF : Covariant F) (hcB : Covariant B) (hp : ∀ x,0≤F x)
    {K C : ℝ} (hn : ∀ x,‖F x‖≤K) (hb : ∀ x,‖B x‖≤C)
    (hf : trace μ F<∞) :
    |signedTrace μ (fun x => (B x).comp (F x))|≤C*(trace μ F).toReal := by
  obtain ⟨R,hR,hcR,_,hRR⟩ := positive_regular_gram_factor (fun g => (hmp g).measurable) F hF hcF hn hp
  have hr : trace μ (fun x => (R x).adjoint.comp (R x))<∞ := by simpa only [hRR] using hf
  have hh := signedTrace_weighted_gram_bound μ hmp R B hR hB hcR hcB hr hb
  simpa only [hRR] using hh

#print axioms positive_regular_gram_factor
#print axioms signedTrace_positive_weight_bound
end AsymptoticRegularTrace
