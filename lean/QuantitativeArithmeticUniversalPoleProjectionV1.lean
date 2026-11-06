module
public import QuantitativeArithmeticUniversalPoleDirectionV1
public import SmallLevelFiniteShiftBlockV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Filter Set SmallLevelFiniteShift
open scoped Topology
variable {ι : Type*} [Fintype ι]

/-- A nonzero upper projection of a universal two-point principal vector is
itself universal for the original family. No equality of pole orders is
assumed in the construction of the two-point vector. -/
theorem IsLeadingVector.project_zero {G : ℂ → ι → ℂ} {x : ℂ}
    {v : Fin 2 × ι → ℂ} (hv : IsLeadingVector (stackGrid 1 G) x v)
    (h0 : (fun j => v (0,j))≠0) : IsLeadingVector G x (fun j => v (0,j)) := by
  classical
  refine ⟨h0,?_⟩
  intro A H hA hH he
  let B : ℂ → Fin 2 × ι → ℂ := fun z b => if b.1=0 then A z b.2 else 0
  have hB (b : Fin 2 × ι) : AnalyticAt ℂ (fun z => B z b) x := by
    by_cases hb : b.1=0
    · simpa only [B,ite_eq_left hb] using hA b.2
    · simpa only [B,ite_eq_right hb] using (analyticAt_const (v:=(0:ℂ)))
  have hsum (z : ℂ) (w : Fin 2 × ι → ℂ) :
      ∑ b, B z b*w b=∑ j, A z j*w (0,j) := by
    simp [B,Fintype.sum_prod_type]
  have he' : (fun z => ∑ b, B z b*stackGrid 1 G z b)=ᶠ[𝓝[≠] x] H := by
    filter_upwards [he] with z hz
    rw [hsum]
    simpa only [stackGrid,Fin.val_zero,Nat.cast_zero,sub_zero] using hz
  have h := hv.2 B H hB hH he'
  simpa only [hsum] using h

#print axioms IsLeadingVector.project_zero
end QuantitativeArithmeticUniversalPoleVector
