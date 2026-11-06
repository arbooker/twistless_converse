module

public import AsymptoticMixingOperatorV1
public import AsymptoticRegularStackPolarV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticMixing

open AsymptoticSubgroupSupport AsymptoticObservationStack AsymptoticPolarIsometry
open AsymptoticRegularTrace ContinuousLinearMap MeasureTheory
open scoped lp ENNReal

variable {G α ι : Type*} [Group G] [Fintype ι] [MeasurableSpace α] [MulAction G α]

omit [MeasurableSpace α] in
theorem translation_covariant (a : G) : Covariant (fun _ : α => translation a) := by
  classical
  intro x b g h
  simp only [matrix,translation_apply,delta,lp.single_apply]
  simp only [Pi.single_apply,← mul_assoc,mul_right_cancel_iff]

variable [Countable G]

theorem mixed_regular (a : ι → G) (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i)) :
    (∀ g h,Measurable (fun x => matrix (mixed a (L x)) g h)) ∧
      Covariant (fun x => mixed a (L x)) := by
  exact ⟨matrix_finsetSum_measurable Finset.univ _
    (fun i _ => matrix_comp_measurable _ _ (fun _ _ => measurable_const) (hm i)),
    covariant_finsetSum Finset.univ _ (fun i _ =>
      covariant_comp _ _ (translation_covariant (a i)) (hc i))⟩

theorem normalizedMixed_regular (a : ι → G) (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i)) :
    (∀ g h,Measurable (fun x => matrix (normalizedMixed a (L x)) g h)) ∧
      Covariant (fun x => normalizedMixed a (L x)) := by
  obtain ⟨hr,hcr⟩ := mixed_regular a L hm hc
  simp only [normalizedMixed_formula]
  exact ⟨matrix_smul_measurable _ _ hr,covariant_smul _ _ hcr⟩

omit [MulAction G α] [Countable G] in
theorem normalizedMixed_polar_trace (μ : Measure α) (S : Subgroup G) (a : ι → G)
    (ha : ∀ i j,i≠j → a j*(a i)⁻¹∉S)
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hL : ∀ x i,Supported S (L x i)) :
    trace μ (fun x => (normalizedMixed a (polarRow (L x))).adjoint.comp
      (normalizedMixed a (polarRow (L x))))=
    ENNReal.ofReal ((Fintype.card ι:ℝ)⁻¹)*trace μ (fun x => (stack (L x)).kerᗮ.starProjection) := by
  rw [trace_gram,trace,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [normalizedMixed_polar_root S a ha (L x) (hL x) 1,ENNReal.ofReal_mul (by positivity)]

/-- Fresh mixing loses at most the number of rows in support dimension.
The support estimate is proved for the original operators, without
assuming regularity of their polar decompositions or closed ranges. -/
theorem normalizedMixed_rank_loss (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (S : Subgroup G) (a : ι → G) (ha : ∀ i j,i≠j → a j*(a i)⁻¹∉S)
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (hL : ∀ x i,Supported S (L x i)) (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) :
    ENNReal.ofReal ((Fintype.card ι:ℝ)⁻¹)*trace μ (fun x => (stack (L x)).kerᗮ.starProjection)≤
      trace μ (fun x => (normalizedMixed a (L x)).kerᗮ.starProjection) := by
  have hr := normalizedMixed_regular a L hm hc
  have hp := stack_polarRow_regular L hm hc M hM
  have hv := normalizedMixed_regular a (fun x => polarRow (L x))
    (fun i => (hp i).1) (fun i => (hp i).2)
  calc
    _=trace μ (fun x => (normalizedMixed a (polarRow (L x))).adjoint.comp
        (normalizedMixed a (polarRow (L x)))) := (normalizedMixed_polar_trace μ S a ha L hL).symm
    _≤trace μ (fun x => (normalizedMixed a (polarRow (L x))).kerᗮ.starProjection) :=
      trace_gram_le_support μ _ (fun x => normalizedMixed_polar_norm a (L x))
    _=trace μ (fun x => (outputSpace (normalizedMixed a (polarRow (L x)))).starProjection) :=
      support_trace_eq μ hmp _ hv.1 hv.2 1 (fun x => normalizedMixed_polar_norm a (L x))
    _=trace μ (fun x => (outputSpace (normalizedMixed a (L x))).starProjection) := by
      apply congrArg (trace μ)
      funext x
      simp only [← normalizedMixed_output_polar a (L x)]
    _=trace μ (fun x => (normalizedMixed a (L x)).kerᗮ.starProjection) :=
      (support_trace_eq μ hmp _ hr.1 hr.2 M
        (fun x => (normalizedMixed_norm a (L x)).trans (hM x))).symm

omit [MeasurableSpace α] [MulAction G α] [Countable G] in
theorem normalizedMixed_ker (a : ι → G) (hι : 0<Fintype.card ι)
    (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    (normalizedMixed a L).ker=(mixed a L).ker := by
  have hn : (Real.sqrt (Fintype.card ι))≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hι))
  ext v
  change normalizedMixed a L v=0 ↔ mixed a L v=0
  rw [normalizedMixed_formula,smul_apply,smul_eq_zero]
  simp only [Complex.ofReal_eq_zero,inv_eq_zero,hn,false_or]

/-- The unnormalized averaged equation has the same kernel. With q-1
rows the factor here is exactly 1/(q-1), as in the one-prime lemma. -/
theorem mixed_rank_loss (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (S : Subgroup G) (a : ι → G) (ha : ∀ i j,i≠j → a j*(a i)⁻¹∉S) (hι : 0<Fintype.card ι)
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (hL : ∀ x i,Supported S (L x i)) (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) :
    ENNReal.ofReal ((Fintype.card ι:ℝ)⁻¹)*trace μ (fun x => (stack (L x)).kerᗮ.starProjection)≤
      trace μ (fun x => (mixed a (L x)).kerᗮ.starProjection) := by
  simpa only [normalizedMixed_ker a hι] using normalizedMixed_rank_loss μ hmp S a ha L hm hc hL M hM

#print axioms translation_covariant
#print axioms mixed_regular
#print axioms normalizedMixed_regular
#print axioms normalizedMixed_polar_trace
#print axioms normalizedMixed_rank_loss
#print axioms normalizedMixed_ker
#print axioms mixed_rank_loss

end AsymptoticMixing
