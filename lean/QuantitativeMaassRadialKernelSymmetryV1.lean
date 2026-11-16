module

public import QuantitativeMaassRadialSeedV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip
open scoped Topology MatrixGroups

namespace QuantitativeMaass

theorem integral_action_dist (s : SL(2,ℤ)) (z w : ℍ) :
    dist (s•z) (s•w)=dist z w := by
  have he (v : ℍ) : (s:SL(2,ℝ))•v=s•v := by
    apply UpperHalfPlane.ext
    simp only [coe_specialLinearGroup_apply]
    rfl
  rw [← he z,← he w]
  exact dist_smul _ _ _

/-- The actual projective congruence action preserves hyperbolic distance. -/
theorem congruence_action_dist (N : ℕ) (γ : gamma N) (z w : ℍ) :
    dist (γ•z) (γ•w)=dist z w := by
  have he (v : ℍ) : representative γ•v=γ•v := by
    rw [← integralLabel_action,representative_label]
    rfl
  rw [← he z,← he w]
  exact integral_action_dist (representative γ) z w

/-- Symmetry of the actual projective radial Poincare kernel, obtained by
inverting group labels. The formula has no duplicated scalar representatives. -/
theorem radialPoincareKernel_symm (N : ℕ) (g : ℝ → ℂ) (w z : ℍ) :
    radialPoincareKernel N g w z=radialPoincareKernel N g z w := by
  unfold radialPoincareKernel poincareSum
  simp only [radialFunction_upper]
  calc
    (∑' γ : gamma N, g (Real.cosh (dist (γ•z) w))) =
        ∑' γ : gamma N, g (Real.cosh (dist (γ⁻¹•w) z)) := by
      apply tsum_congr
      intro γ
      have he := congruence_action_dist N γ⁻¹ (γ•z) w
      rw [inv_smul_smul] at he
      rw [← he,dist_comm z (γ⁻¹•w)]
    _ = _ := (Equiv.inv (gamma N)).tsum_eq
      (fun γ : gamma N => g (Real.cosh (dist (γ•w) z)))

theorem radialPoincareKernel_center_invariant (N : ℕ) (g : ℝ → ℂ) (w z : ℍ)
    (γ : gamma N) :
    radialPoincareKernel N g (γ•w) z=radialPoincareKernel N g w z := by
  rw [radialPoincareKernel_symm N g (γ•w) z,radialPoincareKernel_invariant,
    radialPoincareKernel_symm N g z w]

#print axioms congruence_action_dist
#print axioms radialPoincareKernel_symm
#print axioms radialPoincareKernel_center_invariant

end QuantitativeMaass
