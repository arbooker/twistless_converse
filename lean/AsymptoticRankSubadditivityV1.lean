module

public import AsymptoticLabelledTraceV1
public import AsymptoticPolarRangeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticObservationStack

open ContinuousLinearMap AsymptoticPolarIsometry

variable {ι H J : Type*} [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [CompleteSpace H] [CompleteSpace J] in
theorem component_norm_le (B : H →L[ℂ] PiLp 2 (fun _ : ι => J)) (i : ι) :
    ‖component B i‖≤‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (component B i) (norm_nonneg B)
  intro v
  exact (PiLp.norm_apply_le (B v) i).trans (B.le_opNorm v)

theorem polarRow_norm_le (L : ι → H →L[ℂ] J) (i : ι) : ‖polarRow L i‖≤1 :=
  (component_norm_le (polar (stack L)) i).trans (polar_norm_le (stack L))

/-- A polar row and the original row have the same closed output range.
This requires neither a closed range nor an inverse of the Gram operator. -/
theorem polarRow_outputSpace (L : ι → H →L[ℂ] J) (i : ι) :
    outputSpace (polarRow L i)=outputSpace (L i) := by
  have he : (PiLp.proj (𝕜:=ℂ) 2 (fun _ : ι => J) i).comp (stack L)=L i := by
    ext v
    rfl
  simpa only [polarRow,component,he] using
    (outputSpace_comp_polar (PiLp.proj (𝕜:=ℂ) 2 (fun _ : ι => J) i) (stack L)).symm

#print axioms component_norm_le
#print axioms polarRow_norm_le
#print axioms polarRow_outputSpace

end AsymptoticObservationStack

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticPolarIsometry AsymptoticObservationStack
open scoped lp ENNReal

variable {G α ι : Type*} [Group G] [Countable G] [MeasurableSpace α]
variable [MulAction G α] [Fintype ι]

/-- The rank of a finite stack is at most the sum of its row ranks, for
the rooted regular trace. Infinite traces and nonclosed ranges are allowed. -/
theorem stack_rank_le_sum (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h))
    (hc : ∀ i,Covariant (fun x => L x i))
    (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) :
    trace μ (fun x => (stack (L x)).kerᗮ.starProjection)≤
      ∑ i,trace μ (fun x => (L x i).kerᗮ.starProjection) := by
  have hp := stack_polarRow_regular L hm hc M hM
  have hrow (i : ι) (x : α) : ‖L x i‖≤M := by
    have he : component (stack (L x)) i=L x i := by ext v; rfl
    exact (he ▸ component_norm_le (stack (L x)) i).trans (hM x)
  calc
    _=∑ i,trace μ (fun x => (polarRow (L x) i).adjoint.comp (polarRow (L x) i)) := by
      simpa only [polar_rows_gram] using
        trace_sum_gram μ (fun x => polarRow (L x)) (fun i => (hp i).1)
    _=∑ i,trace μ (fun x => (polarRow (L x) i).comp (polarRow (L x) i).adjoint) :=
      Finset.sum_congr rfl (fun i _ => trace_adjoint_mul hmp _ (hp i).1 (hp i).2)
    _≤∑ i,trace μ (fun x => ((polarRow (L x) i).adjoint).kerᗮ.starProjection) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [adjoint_adjoint] using
        trace_gram_le_support μ (fun x => (polarRow (L x) i).adjoint)
          (fun x => by rw [adjoint.norm_map]; exact polarRow_norm_le (L x) i)
    _=∑ i,trace μ (fun x => (outputSpace (L x i)).starProjection) := by
      simp only [← outputSpace_eq_adjoint_kernel,polarRow_outputSpace]
    _=∑ i,trace μ (fun x => (L x i).kerᗮ.starProjection) :=
      Finset.sum_congr rfl (fun i _ => (support_trace_eq μ hmp _ (hm i) (hc i) M (hrow i)).symm)

#print axioms stack_rank_le_sum

end AsymptoticRegularTrace
