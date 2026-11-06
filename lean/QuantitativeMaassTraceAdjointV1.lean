module

public import QuantitativeMaassCosetTraceIntegralV1
public import QuantitativeMaassHeckePairingV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace ComplexConjugate

namespace QuantitativeMaass.AutomorphicL2

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (H J : Subgroup G) (hHJ : H ≤ J) [Fintype (J ⧸ H.subgroupOf J)]
    (ρ σ : α → ℝ≥0∞) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hnρ : ∀ x, ∑' g : J, ρ (g.val • x) = 1)
    (hnσ : ∀ x, ∑' h : H, σ (h.val • x) = 1)

include hHJ hnσ in
omit [Countable G] [MeasurableSpace α] [Fintype (J ⧸ H.subgroupOf J)] in
theorem subgroupDensityNormalized (x : α) :
    ∑' h : H.subgroupOf J, σ (h.val.val • x) = 1 := by
  exact ((Subgroup.subgroupOfEquivOfLe hHJ).toEquiv.tsum_eq
    (fun h : H => σ (h.val • x))).trans (hnσ x)

/-- The literal finite coset sum is an actual automorphic L² representative. -/
def traceRepresentative (f : representatives H (μ.withDensity σ)) :
    representatives J (μ.withDensity ρ) :=
  ⟨CosetTrace.trace (H.subgroupOf J) f.val
      (fun h x => f.property.2.1 ⟨h.val.val,h.property⟩ x),
    CosetTrace.trace_measurable _ _ _ (fun g : J => (hmp g.val).measurable) f.property.1,
    (fun g x => CosetTrace.trace_invariant _ _ _ g x),
    CosetTrace.trace_memLp μ (fun g : J => hmp g.val) (H.subgroupOf J) ρ σ hρ hσ hnρ
      (subgroupDensityNormalized H J hHJ σ hnσ) f.val f.property.1 _ f.property.2.2⟩

theorem traceRepresentative_apply (f : representatives H (μ.withDensity σ)) (x : α) :
    (traceRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f).val x =
      ∑ q : J ⧸ H.subgroupOf J, f.val (q.out.val⁻¹ • x) :=
  CosetTrace.trace_out _ _ _ x

/-- Unfolding proves the exact adjoint pairing, for all measurable L²
representatives, without boundedness or smoothness hypotheses. -/
theorem trace_pairing (f : representatives H (μ.withDensity σ))
    (k : representatives J (μ.withDensity ρ)) :
    ⟪denseEmbedding J (μ.withDensity ρ)
        (traceRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f),
      denseEmbedding J (μ.withDensity ρ) k⟫_ℂ =
    ⟪denseEmbedding H (μ.withDensity σ) f,
      coverOperator μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ
        (denseEmbedding J (μ.withDensity ρ) k)⟫_ℂ := by
  rw [coverOperator_apply, denseEmbedding_inner, denseEmbedding_inner]
  let F : α → ℂ := fun x => conj (f.val x) * k.val x
  have hF : Measurable F := (Complex.continuous_conj.measurable.comp f.property.1).mul k.property.1
  have hFinv (h : H.subgroupOf J) (x : α) : F (h.val.val • x) = F x := by
    dsimp only [F]
    rw [f.property.2.1 ⟨h.val.val,h.property⟩ x, k.property.2.1 h.val x]
  have hFi : Integrable F (μ.withDensity σ) := by
    have hi := L2.integrable_inner (𝕜 := ℂ) (embedding H (μ.withDensity σ) f)
      (embedding H (μ.withDensity σ) (coverRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ k))
    apply hi.congr
    filter_upwards [f.property.2.2.coeFn_toLp,
      (coverRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ k).property.2.2.coeFn_toLp]
      with x hf hk
    change ⟪(f.property.2.2.toLp f.val) x,
      ((coverRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ k).property.2.2.toLp _) x⟫_ℂ = _
    rw [hf,hk]
    simp only [F, RCLike.inner_apply, mul_comm]
    rfl
  calc
    _ = ∫ x, CosetTrace.trace (H.subgroupOf J) F hFinv x ∂μ.withDensity ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        change conj ((traceRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f).val x) * k.val x = _
        rw [traceRepresentative_apply μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f x,
          CosetTrace.trace_out, map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _
        dsimp only [F]
        exact congrArg (fun v : ℂ => conj (f.val (q.out.val⁻¹ • x)) * v)
          (k.property.2.1 q.out⁻¹ x).symm)
    _ = ∫ x, F x ∂μ.withDensity σ :=
      CosetTrace.integral_unfold μ (fun g : J => hmp g.val) (H.subgroupOf J)
        ρ σ hρ hσ hnρ (subgroupDensityNormalized H J hHJ σ hnσ) F hF hFinv hFi
    _ = _ := rfl

/-- The Hilbert adjoint pushforward is exactly the actual finite coset sum. -/
theorem coverOperator_adjoint_apply (f : representatives H (μ.withDensity σ)) :
    (coverOperator μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ).adjoint
      (denseEmbedding H (μ.withDensity σ) f) =
    denseEmbedding J (μ.withDensity ρ)
      (traceRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f) := by
  apply ext_inner_right ℂ
  intro k
  have he := (denseEmbedding_dense J (μ.withDensity ρ)).equalizer
    (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    (show (fun v => ⟪(coverOperator μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ).adjoint
      (denseEmbedding H (μ.withDensity σ) f), v⟫_ℂ) ∘ denseEmbedding J (μ.withDensity ρ) =
      (fun v => ⟪denseEmbedding J (μ.withDensity ρ)
        (traceRepresentative μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f), v⟫_ℂ) ∘
          denseEmbedding J (μ.withDensity ρ) from by
      funext v
      simp only [Function.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      exact (trace_pairing μ hmp H J hHJ ρ σ hρ hσ hnρ hnσ f v).symm)
  exact congrFun he k

#print axioms trace_pairing
#print axioms coverOperator_adjoint_apply

end QuantitativeMaass.AutomorphicL2
