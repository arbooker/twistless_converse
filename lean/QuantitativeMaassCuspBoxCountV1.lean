module

public import QuantitativeMaassHighCuspCountV1
public import QuantitativeMaassCuspCoreGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip QuantitativeArithmeticMaassOverlap QuantitativeSpectralObservability
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- A fixed-radius return count is linear in height throughout every standard
cusp box, with one constant before both the truncation height and level. -/
theorem diagonalOrbitSet_cusp_box_linear (R : ℝ) (hR : 0≤R) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) [NeZero N] (H : ℝ) (z : ℍ),z∈wideBox H →
      ((diagonalOrbitSet N z R).card:ℝ)≤C*(1+z.im) := by
  let H₀ := max 2 (Real.exp (R/2))
  let L := Real.log (4*(H₀+3)^2)
  let B := energyMultiplicity I 0 (R+2*L)
  let C : ℝ := B+6*Real.exp R+9
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro N _ H z hz
  by_cases hhigh : Real.exp (R/2)<z.im
  · have hb := diagonalOrbitSet_high_cusp_card_real N z R hR hhigh
    dsimp only [C]
    have hB : 0≤(B:ℝ) := Nat.cast_nonneg _
    nlinarith [z.im_pos,Real.exp_pos R,mul_nonneg hB z.im_pos.le]
  · have hz0 : z∈wideBox H₀ :=
      ⟨hz.1,hz.2.1,hz.2.2.1,(le_of_not_gt hhigh).trans (le_max_right _ _)⟩
    have hd : dist z I≤L := by
      apply (Real.le_log_iff_exp_le (by dsimp only [H₀];positivity : 0<4*(H₀+3)^2)).mpr
      exact wideBox_exp_dist H₀ (le_max_left _ _) hz0
    have hsub : diagonalOrbitSet N z R⊆diagonalOrbitSet N I (R+2*L) := by
      intro g hg
      exact displacement_in_diagonalOrbitSet N I z L R hd g ((mem_diagonalOrbitSet N z R g).mp hg)
    have hc : (diagonalOrbitSet N z R).card≤B :=
      (Finset.card_le_card hsub).trans (diagonalOrbitSet_card_bound N I (R+2*L))
    have hb : ((diagonalOrbitSet N z R).card:ℝ)≤B := by exact_mod_cast hc
    have hBC : (B:ℝ)≤C := by dsimp only [C];linarith [Real.exp_pos R]
    exact hb.trans (hBC.trans (le_mul_of_one_le_right hC.le (by linarith [z.im_pos])))

#print axioms diagonalOrbitSet_cusp_box_linear

end QuantitativeMaass
