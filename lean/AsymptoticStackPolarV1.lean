module

public import AsymptoticPolarBoundsV1
public import AsymptoticRegularObservationGramV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticObservationStack

open ContinuousLinearMap Filter AsymptoticPolarIsometry
open scoped Topology

variable {ι H J : Type*} [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable def component (B : H →L[ℂ] PiLp 2 (fun _ : ι => J)) (i : ι) : H →L[ℂ] J :=
  (PiLp.proj (𝕜:=ℂ) 2 (fun _ : ι => J) i).comp B

omit [Fintype ι] [CompleteSpace H] [CompleteSpace J] in
theorem component_apply (B : H →L[ℂ] PiLp 2 (fun _ : ι => J)) (i : ι) (x : H) :
    component B i x=B x i := rfl

omit [Fintype ι] [CompleteSpace H] [CompleteSpace J] in
theorem stack_component (B : H →L[ℂ] PiLp 2 (fun _ : ι => J)) : stack (component B)=B := by
  ext x i
  rfl

noncomputable def polarRow (L : ι → H →L[ℂ] J) (i : ι) : H →L[ℂ] J :=
  component (polar (stack L)) i

/-- The initial support of a finite stack is the sum of the Gram
operators of its polar rows. Observation labels remain distinct. -/
theorem polar_rows_gram (L : ι → H →L[ℂ] J) :
    (∑ i,(polarRow L i).adjoint.comp (polarRow L i))=(stack L).kerᗮ.starProjection := by
  rw [← stack_gram]
  change (stack (component (polar (stack L)))).adjoint.comp
    (stack (component (polar (stack L))))=_
  rw [stack_component,polar_gram]

noncomputable def regularizedRow (L : ι → H →L[ℂ] J) (n : ℕ) (i : ι) : H →L[ℂ] J :=
  component (regularizedPolar (stack L) n) i

theorem regularizedRow_formula (L : ι → H →L[ℂ] J) (n : ℕ) (i : ι) :
    regularizedRow L n i=(((n+1)^2:ℕ):ℂ) • (L i).comp (AsymptoticPolarIsometry.resolvent (stack L) n) := by
  ext x
  rfl

theorem polarRow_strong_limit (L : ι → H →L[ℂ] J) (i : ι) (x : H) :
    Tendsto (fun n => regularizedRow L n i x) atTop (𝓝 (polarRow L i x)) :=
  ((PiLp.proj (𝕜:=ℂ) 2 (fun _ : ι => J) i).continuous.tendsto _).comp
    (regularizedPolar_strong_limit (stack L) x)

#print axioms component_apply
#print axioms stack_component
#print axioms polar_rows_gram
#print axioms regularizedRow_formula
#print axioms polarRow_strong_limit

end AsymptoticObservationStack
