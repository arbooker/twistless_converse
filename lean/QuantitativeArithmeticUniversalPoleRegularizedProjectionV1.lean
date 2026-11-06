module
public import QuantitativeArithmeticUniversalPoleProjectionV1
public import SmallLevelRegularizedShiftBlockV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Filter Set SmallLevelFiniteShift
open scoped Topology
variable {ι : Type*} [Fintype ι]

/-- Nonzero top projections of arbitrary finite stacks preserve universality. -/
theorem IsLeadingVector.project_regularized_top {G : ℂ → ι → ℂ} {x : ℂ} {d : ℕ}
    {v : Fin (d+1) × ι → ℂ} (hv : IsLeadingVector (regularizedStack d G x) x v)
    (h0 : (fun j => v (0,j))≠0) : IsLeadingVector (fun z j => (z-x)*G z j) x (fun j => v (0,j)) := by
  classical
  refine ⟨h0,?_⟩
  intro A H hA hH he
  let B : ℂ → Fin (d+1) × ι → ℂ := fun z b => if b.1=0 then A z b.2 else 0
  have hB (b : Fin (d+1) × ι) : AnalyticAt ℂ (fun z => B z b) x := by
    by_cases hb : b.1=0
    · simpa only [B,ite_eq_left hb] using hA b.2
    · simpa only [B,ite_eq_right hb] using (analyticAt_const (v:=(0:ℂ)))
  have hsum (z : ℂ) (w : Fin (d+1) × ι → ℂ) :
      ∑ b, B z b*w b=∑ j, A z j*w (0,j) :=
    block_delta_apply 0 (A z) w
  have he' : (fun z => ∑ b, B z b*regularizedStack d G x z b)=ᶠ[𝓝[≠] x] H := by
    filter_upwards [he] with z hz
    rw [hsum]
    simpa [regularizedStack] using hz
  have h := hv.2 B H hB hH he'
  simpa only [hsum] using h

#print axioms IsLeadingVector.project_regularized_top
end QuantitativeArithmeticUniversalPoleVector
