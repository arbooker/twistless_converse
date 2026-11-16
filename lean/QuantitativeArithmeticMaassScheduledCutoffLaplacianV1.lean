module

public import QuantitativeArithmeticMaassRectangleLaplacianV1
public import QuantitativeArithmeticMaassScheduledCutoffGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
namespace QuantitativeMaass.Scheduled

/-- The actual cutoff's Laplacian has a fixed exponential cost, uniformly
in the lower edge, including moving lower cutoffs. -/
theorem cutoffSeed_laplacian (D : ℝ) :
    ∀ᶠ t in atTop, ∀ (δ : ℝ) (hδ : 0<δ) (z : ℍ),
      ‖upperLaplacian (cutoffSeed δ D t hδ).toFun z‖≤
        Real.exp ((2*D+2)*Strong.strongScale t) := by
  obtain ⟨C,hC,hbound⟩ := rectangleSmoothSeed_laplacian_global
  filter_upwards [(Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
    (eventually_ge_atTop C)] with t ht
  intro δ hδ z
  have hb := hbound 0 1 δ (Real.exp (Strong.strongScale t/2))
    (Real.exp (-(D*Strong.strongScale t))) hδ (Real.exp_pos _) z
  apply hb.trans
  calc
    C*Real.exp (Strong.strongScale t/2)^2/Real.exp (-(D*Strong.strongScale t))^2 =
        C*Real.exp ((2*D+1)*Strong.strongScale t) := by
      rw [show (2*D+1)*Strong.strongScale t=
        (Strong.strongScale t/2+Strong.strongScale t/2)-
          (-(D*Strong.strongScale t)+-(D*Strong.strongScale t)) by ring,
        Real.exp_sub,Real.exp_add,Real.exp_add]
      ring
    _ ≤ Real.exp (Strong.strongScale t)*Real.exp ((2*D+1)*Strong.strongScale t) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = Real.exp ((2*D+2)*Strong.strongScale t) := by
      rw [←Real.exp_add]
      congr 1
      ring

#print axioms cutoffSeed_laplacian
end QuantitativeMaass.Scheduled
