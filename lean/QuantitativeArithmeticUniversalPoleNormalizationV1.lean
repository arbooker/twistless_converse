module
public import QuantitativeArithmeticUniversalPoleVectorV1
public import Mathlib.Tactic.Ring
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Filter Set
open scoped Topology
variable {ι : Type*} [Fintype ι]

/-- Rescaling preserves every actual analytic row simultaneously. -/
theorem IsLeadingVector.scale {G : ℂ → ι → ℂ} {s : ℂ} {v : ι → ℂ}
    (hv : IsLeadingVector G s v) (c : ℂ) (hc : c≠0) :
    IsLeadingVector G s (fun j => c*v j) := by
  refine ⟨?_,?_⟩
  · intro h
    apply hv.1
    funext j
    have hj : c*v j=0 := congrFun h j
    exact (mul_eq_zero.mp hj).resolve_left hc
  · intro A H hA hH he
    have h := hv.2 A H hA hH he
    calc
      ∑ j, A s j*(c*v j) = c*(∑ j, A s j*v j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [h,mul_zero]

/-- Normalize a nonzero principal coordinate without changing the pole or
losing any of the continued Taylor, Hecke, word or entire-twist rows. -/
theorem IsLeadingVector.normalize {G : ℂ → ι → ℂ} {s : ℂ} {v : ι → ℂ}
    (hv : IsLeadingVector G s v) (j : ι) (hj : v j≠0) :
    ∃ w, IsLeadingVector G s w ∧ w j=1 ∧ ∀ i, w i=v i/v j := by
  refine ⟨fun i => (v j)⁻¹*v i, hv.scale _ (inv_ne_zero hj), ?_, ?_⟩
  · exact inv_mul_cancel₀ hj
  · intro i
    rw [div_eq_mul_inv,mul_comm]

#print axioms IsLeadingVector.scale
#print axioms IsLeadingVector.normalize
end QuantitativeArithmeticUniversalPoleVector
