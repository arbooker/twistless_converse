module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservationStack

variable {ι E J : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J]

/-- A finite family of observations, with the Hilbert direct-sum norm. -/
noncomputable def stack (L : ι → E →L[ℂ] J) : E →L[ℂ] PiLp 2 (fun _ : ι => J) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => J)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi L)

omit [Fintype ι] in
theorem stack_apply (L : ι → E →L[ℂ] J) (v : E) (i : ι) :
    stack L v i=L i v := rfl

omit [Fintype ι] in
theorem stack_eq_zero_iff (L : ι → E →L[ℂ] J) (v : E) :
    stack L v=0 ↔ ∀ i,L i v=0 := by
  constructor
  · intro h i
    exact congrArg (fun f : PiLp 2 (fun _ : ι => J) => f i) h
  · intro h
    ext i
    exact h i

/-- A bound depending only on the row bounds and the finite index set.
In particular it is uniform in any weight parameter absent from b. -/
theorem stack_norm_le (L : ι → E →L[ℂ] J) (b : ι → ℝ)
    (hb : ∀ i,0≤b i) (hL : ∀ i,‖L i‖≤b i) :
    ‖stack L‖≤‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => J)).symm.toContinuousLinearMap‖*
      ∑ i,b i := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply ContinuousLinearMap.norm_pi_le_of_le _ (Finset.sum_nonneg (fun i _ => hb i))
  intro i
  exact (hL i).trans (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i))

#print axioms stack_eq_zero_iff
#print axioms stack_norm_le

end AsymptoticObservationStack
