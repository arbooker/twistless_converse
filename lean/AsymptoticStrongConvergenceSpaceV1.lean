module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.UniformSpace.Equicontinuity
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

namespace AsymptoticStrongConvergence

open Filter ContinuousLinearMap
open scoped Topology

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J]

/-- Vectors on which a sequence of bounded linear maps converges to zero. -/
def vanishing (T : ℕ → H →L[ℂ] J) : Submodule ℂ H where
  carrier := {x | Tendsto (fun n => T n x) atTop (𝓝 0)}
  zero_mem' := by simpa only [Set.mem_ofPred_eq,map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:J)) atTop (𝓝 0))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq,map_add,zero_add] using hx.add hy
  smul_mem' := by
    intro a x hx
    simpa only [Set.mem_ofPred_eq,map_smul,smul_zero] using hx.const_smul a

/-- A uniform operator bound makes the zero-convergence subspace closed. -/
theorem vanishing_isClosed (T : ℕ → H →L[ℂ] J) {B : ℝ} (hT : ∀ n,‖T n‖≤B) :
    IsClosed (vanishing T : Set H) := by
  have hi : (∃ C : ℝ,∀ n,‖T n‖≤C) ↔ Equicontinuous ((↑) ∘ T) :=
    (NormedSpace.equicontinuous_TFAE T).out 6 2
  have he : Equicontinuous ((↑) ∘ T) := hi.mp ⟨B,hT⟩
  exact he.isClosed_setOfPred_tendsto continuous_const

variable [CompleteSpace H]

/-- A closed subspace containing a closed range's orthogonal complement,
the observation adjoint range, and the surviving kernel is the whole space. -/
theorem eq_top_of_range_kernel (V W : Submodule ℂ H) [CompleteSpace V]
    [CompleteSpace W] [CompleteSpace J] (L : H →L[ℂ] J)
    (hperp : Vᗮ≤W) (hadj : L.adjoint.range≤W) (hker : V⊓L.ker≤W) : W=⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hvv : x∈Vᗮᗮ := Submodule.orthogonal_le hperp hx
  have hv : x∈V := by simpa only [Submodule.orthogonal_orthogonal] using hvv
  have hlp : x∈L.adjoint.rangeᗮ := Submodule.orthogonal_le hadj hx
  have hl : x∈L.ker := by
    simpa only [ContinuousLinearMap.orthogonal_range,adjoint_adjoint] using hlp
  have hxx := hx x (hker ⟨hv,hl⟩)
  exact (inner_self_eq_zero (𝕜:=ℂ)).mp hxx

#print axioms vanishing_isClosed
#print axioms eq_top_of_range_kernel

end AsymptoticStrongConvergence
