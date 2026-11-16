module

public import QuantitativeMaassLatticeDiscrepancyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Every radial profile with bounded propagation restricts to a compactly
supported horizontal profile at each positive height. -/
theorem parabolicLineProfile_compact (g : ℝ → ℂ) (B : ℝ)
    (hs : Function.support g⊆Iic B) (y : ℝ) (hy : 0<y) :
    HasCompactSupport (parabolicLineProfile g y) := by
  let C := 2*y^2*(|B|+1)
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-(C+1)) (C+1)))
  intro v hv
  have hh : 1+v^2/(2*y^2)≤B := hs hv
  have hd : 0<2*y^2 := by positivity
  have hb : v^2≤(B-1)*(2*y^2) := (div_le_iff₀ hd).mp (by linarith)
  have hC : 0≤C := by dsimp only [C];positivity
  have hsq : v^2≤C := by
    dsimp only [C]
    nlinarith [le_abs_self B]
  have hab : |v|≤C+1 := by
    nlinarith [sq_abs v,sq_nonneg (|v|-1),sq_nonneg (C-|v|),abs_nonneg v]
  exact abs_le.mp hab

/-- The horizontal-profile lattice discrepancy has a proved finite variation
integral; all summability and integrability premises are discharged. -/
theorem parabolicLineProfile_lattice_discrepancy (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ) (hs : Function.support g⊆Iic B)
    (y : ℝ) (hy : 0<y) (a : ℝ) :
    Summable (fun n : ℤ => parabolicLineProfile g y (a+n)) ∧
      ‖(∑' n : ℤ,parabolicLineProfile g y (a+n))-∫ v,parabolicLineProfile g y v‖≤
        ∫ v,‖deriv (parabolicLineProfile g y) v‖ := by
  have hc := parabolicLineProfile_compact g B hs y hy
  have hsm := parabolicLineProfile_smooth g hg y
  have h1 : ContDiff ℝ 1 (parabolicLineProfile g y) := hsm.of_le (by simp)
  exact integer_lattice_discrepancy _ h1 (hsm.continuous.integrable_of_hasCompactSupport hc)
    ((contDiff_one_iff_deriv.mp h1).2.integrable_of_hasCompactSupport hc.deriv) a

#print axioms parabolicLineProfile_compact
#print axioms parabolicLineProfile_lattice_discrepancy

end QuantitativeMaass
