module

public import QuantitativeMaassCylinderBandsV1
public import QuantitativeMaassCuspRectangleV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A compact radial kernel on the translation cylinder cannot connect
heights whose logarithms differ by more than the propagation radius. -/
theorem cylinderRadialKernel_log_zero (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (x y : ℍ)
    (hxy : R < |Real.log y.im-Real.log x.im|) : radialPoincareKernel 0 g x y=0 := by
  unfold radialPoincareKernel poincareSum
  suffices hz : ∀ γ : gamma 0,upperFunction (radialFunction g x) (γ•y)=0 by
    simp only [hz,tsum_zero]
  intro γ
  rw [radialFunction_upper]
  by_contra hn
  have hd := Real.cosh_le_cosh.mp (hs hn)
  rw [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] at hd
  have hi : (γ.val•y).im=y.im := by
    obtain ⟨n,hn⟩ := gamma_zero_translation γ
    rw [hn,AsymptoticCompactTranslation.label_im]
  have hh := UpperHalfPlane.dist_log_im_le (γ.val•y) x
  rw [Real.dist_eq,hi] at hh
  exact (not_le_of_gt hxy) (hh.trans hd)

/-- One compact rectangle contains the strip support of all kernel rows
whose centers lie in a fixed metric ball. -/
theorem cylinderRadialKernel_strip_support (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (o x : ℍ) (L : ℝ) (hx : dist x o≤L)
    (y : ℍ) (hy : y∈strip) (hxy : radialPoincareKernel 0 g x y≠0) :
    y∈upperRectangle 0 1 (Real.exp (Real.log o.im-(R+L))) (Real.exp (Real.log o.im+(R+L))) := by
  have hrow : |Real.log y.im-Real.log x.im|≤R :=
    le_of_not_gt (fun h => hxy (cylinderRadialKernel_log_zero g R hR hs x y h))
  have hcenter : |Real.log x.im-Real.log o.im|≤L := by
    exact (UpperHalfPlane.dist_log_im_le x o).trans hx
  have htotal : |Real.log y.im-Real.log o.im|≤R+L := by
    calc
      _ = |(Real.log y.im-Real.log x.im)+(Real.log x.im-Real.log o.im)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hrow hcenter)
  have hbounds := abs_le.mp htotal
  change y.re∈Icc (0:ℝ) 1 ∧ y.im∈Icc _ _
  refine ⟨⟨hy.1,hy.2.le⟩,?_,?_⟩
  · rw [←Real.exp_log y.im_pos]
    exact Real.exp_le_exp.mpr (by linarith [hbounds.1])
  · rw [←Real.exp_log y.im_pos]
    exact Real.exp_le_exp.mpr (by linarith [hbounds.2])

#print axioms cylinderRadialKernel_log_zero
#print axioms cylinderRadialKernel_strip_support

end QuantitativeMaass
