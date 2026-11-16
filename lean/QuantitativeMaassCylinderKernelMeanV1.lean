module

public import QuantitativeMaassCylinderStationaryV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticIntegralSubgroup
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Literal unit-period mean of a cylinder radial kernel in its center. -/
def cylinderRadialMean (g : ℝ → ℂ) (z w : ℍ) : ℂ :=
  ∫ x in Icc (0:ℝ) 1,radialPoincareKernel 0 g (x+ᵥz) w

theorem cylinderRadialKernel_center_periodic (g : ℝ → ℂ) (z w : ℍ) :
    Function.Periodic (fun x : ℝ => radialPoincareKernel 0 g (x+ᵥz) w) 1 := by
  intro x
  have hh := radialPoincareKernel_center_invariant 0 g (x+ᵥz) w
    ⟨translationLabel ((1:ℤ):ℚ),translation_mem 0 1⟩
  change radialPoincareKernel 0 g (translationLabel ((1:ℤ):ℚ) • (x+ᵥz)) w=_ at hh
  rw [cylinder_translationLabel_vadd,Int.cast_one,←add_vadd,add_comm 1 x] at hh
  exact hh

/-- The period-average kernel is a genuine height-only function in its
input variable. This proves the structural constant-mode cancellation. -/
theorem cylinderRadialMean_translation (g : ℝ → ℂ) (z w : ℍ) (r : ℝ) :
    cylinderRadialMean g z (r+ᵥw)=cylinderRadialMean g z w := by
  let F := fun a x : ℝ => radialPoincareKernel 0 g (x+ᵥz) (a+ᵥw)
  have hp (a : ℝ) : Function.Periodic (F a) 1 :=
    cylinderRadialKernel_center_periodic g z (a+ᵥw)
  have hstat (a x y : ℝ) : F (x+a) (y+a)=F x y := by
    dsimp only [F]
    rw [add_comm x a,add_comm y a,add_vadd,add_vadd,cylinderRadialKernel_translation]
  simpa only [F,zero_vadd,cylinderRadialMean] using stationary_period_integral F hp hstat r

theorem cylinderRadialMean_continuous (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) (z : ℍ) :
    Continuous (cylinderRadialMean g z) := by
  have hk := radialPoincareKernel_joint_continuous_physical 0 g hg R hR hs
  have ht : Continuous (fun p : ℍ×ℝ => (p.2+ᵥz,p.1)) :=
    ((cylinder_vadd_continuous z).comp continuous_snd).prodMk continuous_fst
  have hj := hk.comp ht
  change Continuous (fun p : ℍ×ℝ => radialPoincareKernel 0 g (p.2+ᵥz) p.1) at hj
  exact continuous_parametric_integral_of_continuous
    (f:=fun (w : ℍ) (x : ℝ) => radialPoincareKernel 0 g (x+ᵥz) w) hj
    (μ:=volume) (s:=Icc (0:ℝ) 1) isCompact_Icc

/-- Its support retains the exact logarithmic propagation bound. -/
theorem cylinderRadialMean_log_zero (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (z w : ℍ)
    (hsep : R < |Real.log w.im-Real.log z.im|) : cylinderRadialMean g z w=0 := by
  unfold cylinderRadialMean
  apply integral_eq_zero_of_ae
  filter_upwards with x
  exact cylinderRadialKernel_log_zero g R hR hs (x+ᵥz) w (by simpa only [vadd_im] using hsep)

#print axioms cylinderRadialKernel_center_periodic
#print axioms cylinderRadialMean_translation
#print axioms cylinderRadialMean_continuous
#print axioms cylinderRadialMean_log_zero

end QuantitativeMaass
