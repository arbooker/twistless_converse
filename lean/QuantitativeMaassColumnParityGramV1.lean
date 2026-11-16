module

public import QuantitativeMaassColumnLinearTraceV1
public import QuantitativeMaassParityKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap AsymptoticClassicalPetersson
namespace QuantitativeMaass

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem columnLinearTrace_add (μ : Measure α) (c : α → H) (hc : MemLp c 2 μ)
    (A B : H →L[ℂ] H) :
    columnLinearTrace μ c (A+B) = columnLinearTrace μ c A+columnLinearTrace μ c B := by
  simp only [columnLinearTrace,add_apply,inner_add_left,Complex.add_re]
  exact integral_add (columnLinearTrace_integrable μ c hc A) (columnLinearTrace_integrable μ c hc B)

theorem columnLinearTrace_real_smul (μ : Measure α) (c : α → H)
    (A : H →L[ℂ] H) (r : ℝ) :
    columnLinearTrace μ c ((r:ℂ) • A) = r*columnLinearTrace μ c A := by
  unfold columnLinearTrace
  have heq (z : α) : (inner ℂ (((r:ℂ) • A) (c z)) (c z)).re =
      r*(inner ℂ (A (c z)) (c z)).re := by
    change (inner ℂ ((r:ℂ) • A (c z)) (c z)).re = _
    rw [inner_smul_left]
    rw [show starRingEnd ℂ (r:ℂ) = (r:ℂ) from Complex.conj_ofReal r]
    simp only [Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp_rw [heq]
  exact integral_const_mul _ _

variable [CompleteSpace H]

/-- Move a filter into the observed Gram operator without interchanging
the observation and the filter. -/
theorem columnLinearTrace_filtered (μ : Measure α) (c : α → H)
    (F T : H →L[ℂ] H) :
    columnLinearTrace μ (fun z => F (c z)) T =
      columnLinearTrace μ c (F.adjoint.comp (T.comp F)) := by
  unfold columnLinearTrace
  apply integral_congr_ae
  filter_upwards with z
  change (inner ℂ (T (F (c z))) (F (c z))).re =
    (inner ℂ (F.adjoint (T (F (c z)))) (c z)).re
  rw [F.adjoint_inner_left]

theorem selfAdjoint_commute_adjoint (R F : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hF : Commute R F) :
    F.adjoint.comp R = R.comp F.adjoint := by
  have hh := congrArg (fun A : H →L[ℂ] H => A.adjoint) hF.eq
  change (R.comp F).adjoint = (F.comp R).adjoint at hh
  simpa only [adjoint_comp,hR.adjoint_eq] using hh

/-- Reflection commutation identifies the observed Gram operator with
reflection followed by the same Gram operator as in the ordinary trace. -/
theorem columnLinearTrace_filtered_selfAdjoint (μ : Measure α) (c : α → H)
    (F R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (hF : Commute R F) :
    columnLinearTrace μ (fun z => F (c z)) R =
      columnLinearTrace μ c (R.comp (F.adjoint.comp F)) := by
  rw [columnLinearTrace_filtered,←comp_assoc,
    selfAdjoint_commute_adjoint R F hR hF,comp_assoc]

/-- The actual filtered parity trace splits into the ordinary Gram trace
and its reflected trace, with the exact factor one half. -/
theorem columnLinearTrace_filtered_parity (μ : Measure α) (N : ℕ)
    (c : α → AutomorphicSpace N) (hc : MemLp c 2 μ)
    (F : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (σ : ℝ)
    (hF : Commute (reflectionIsometry N).toContinuousLinearMap F) :
    columnLinearTrace μ (fun z => F (c z)) (parityProjection N σ) =
      (columnLinearTrace μ c (F.adjoint.comp F) +
        σ*columnLinearTrace μ c ((reflectionIsometry N).toContinuousLinearMap.comp
          (F.adjoint.comp F)))/2 := by
  unfold parityProjection
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num]
  rw [columnLinearTrace_real_smul,columnLinearTrace_add μ _ (hc.continuousLinearMap_comp F),
    columnLinearTrace_real_smul,
    columnLinearTrace_filtered_selfAdjoint μ c F _ (reflectionIsometry_selfAdjoint N) hF]
  have hg : columnLinearTrace μ (fun z => F (c z)) 1 = columnLinearTrace μ c (F.adjoint.comp F) := by
    simpa only [show (1 : AutomorphicSpace N →L[ℂ] AutomorphicSpace N).comp F = F from rfl]
      using columnLinearTrace_filtered μ c F 1
  rw [hg]
  ring

#print axioms columnLinearTrace_filtered
#print axioms columnLinearTrace_filtered_selfAdjoint
#print axioms columnLinearTrace_filtered_parity

end QuantitativeMaass
