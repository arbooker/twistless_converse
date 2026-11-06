module

public import AsymptoticRegularStackPolarV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticPolarIsometry AsymptoticObservationStack
open scoped lp ENNReal

variable {G α ι : Type*} [Group G] [Countable G] [MeasurableSpace α] [Fintype ι]

/-- Finite row Gram sums have the sum of their rooted traces, allowing
infinite trace and arbitrary infinite counting-coordinate columns. -/
theorem trace_sum_gram (μ : Measure α) (V : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (V x i) g h)) :
    trace μ (fun x => ∑ i,(V x i).adjoint.comp (V x i))=
      ∑ i,trace μ (fun x => (V x i).adjoint.comp (V x i)) := by
  have he (x : α) : (matrix (∑ i,(V x i).adjoint.comp (V x i)) 1 1).re=
      ∑ i,‖V x i (delta 1)‖^2 := by
    change Complex.reCLM (matrixCLM 1 1 (∑ i,(V x i).adjoint.comp (V x i)))=_
    rw [map_sum,map_sum]
    exact Finset.sum_congr rfl (fun i _ => matrix_gram (V x i) 1)
  calc
    _=∫⁻ x,∑ i,ENNReal.ofReal (‖V x i (delta 1)‖^2) ∂μ := by
      apply lintegral_congr
      intro x
      rw [he]
      exact ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)
    _=∑ i,∫⁻ x,ENNReal.ofReal (‖V x i (delta 1)‖^2) ∂μ :=
      lintegral_finsetSum Finset.univ (fun i _ => root_energy_measurable (fun x => V x i) (fun g => hm i g 1))
    _=_ := Finset.sum_congr rfl (fun i _ => (trace_gram μ (fun x => V x i)).symm)

noncomputable def labelledDiagonal
    (B : PiLp 2 (fun _ : ι => ℓ²(G,ℂ)) →L[ℂ] PiLp 2 (fun _ : ι => ℓ²(G,ℂ))) (i : ι) :
    ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  let E := PiLp.proj (𝕜:=ℂ) 2 (fun _ : ι => ℓ²(G,ℂ)) i
  E.comp (B.comp E.adjoint)

noncomputable def labelledTrace (μ : Measure α)
    (B : α → PiLp 2 (fun _ : ι => ℓ²(G,ℂ)) →L[ℂ] PiLp 2 (fun _ : ι => ℓ²(G,ℂ))) : ℝ≥0∞ :=
  ∑ i,trace μ (fun x => labelledDiagonal (B x) i)

omit [Group G] [Countable G] in
theorem output_labelledDiagonal (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (i : ι) :
    labelledDiagonal (outputSpace (stack L)).starProjection i=
      (polarRow L i).comp (polarRow L i).adjoint := by
  unfold labelledDiagonal polarRow component
  rw [← polar_cogram,adjoint_comp]
  simp only [comp_assoc]

variable [MulAction G α]

/-- For a finite labelled observation stack, the source support trace
is the labelled trace of the actual output support projection. Thus the
polar dimension identity does not merge distinct observation labels. -/
theorem stack_support_trace_eq (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (L : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h,Measurable (fun x => matrix (L x i) g h)) (hc : ∀ i,Covariant (fun x => L x i))
    (M : ℝ) (hM : ∀ x,‖stack (L x)‖≤M) :
    trace μ (fun x => (stack (L x)).kerᗮ.starProjection)=
      labelledTrace μ (fun x => (outputSpace (stack (L x))).starProjection) := by
  have hp := stack_polarRow_regular L hm hc M hM
  calc
    _=∑ i,trace μ (fun x => (polarRow (L x) i).adjoint.comp (polarRow (L x) i)) := by
      simpa only [polar_rows_gram] using trace_sum_gram μ (fun x => polarRow (L x)) (fun i => (hp i).1)
    _=∑ i,trace μ (fun x => (polarRow (L x) i).comp (polarRow (L x) i).adjoint) :=
      Finset.sum_congr rfl (fun i _ => trace_adjoint_mul hmp _ (hp i).1 (hp i).2)
    _=_ := by simp only [labelledTrace,output_labelledDiagonal]

#print axioms trace_sum_gram
#print axioms output_labelledDiagonal
#print axioms stack_support_trace_eq

end AsymptoticRegularTrace
