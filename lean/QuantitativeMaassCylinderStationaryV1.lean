module

public import QuantitativeMaassCylinderSquareKernelV1
public import QuantitativeMaassStationaryMeanV1
public import QuantitativeMaassHighCuspKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticClassicalPetersson
open AsymptoticIntegralSubgroup AsymptoticMassTransport AsymptoticCompactTranslation
open scoped Topology ContDiff MatrixGroups SchwartzMap

namespace QuantitativeMaass

theorem cylinder_vadd_continuous (z : ℍ) : Continuous (fun x : ℝ => x+ᵥz) := by
  apply continuous_induced_rng.mpr
  fun_prop

/-- Cylinder deck transformations commute with every real horizontal shift. -/
theorem gamma_zero_vadd (γ : gamma 0) (r : ℝ) (z : ℍ) :
    γ • (r+ᵥz)=r+ᵥ(γ•z) := by
  have hc : representative γ 1 0=0 := by
    have hm := CongruenceSubgroup.Gamma0_mem.mp (representative_mem γ)
    simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_zero,zero_dvd_iff] using hm
  have he (w : ℍ) : representative γ • w=γ•w := by
    rw [←integralLabel_action,representative_label]
    rfl
  rw [←he,integral_upper_triangular_vadd _ hc,he]

/-- Cylinder radial kernels are stationary at all heights, not only high
cusps: every group summand is a translation. -/
theorem cylinderRadialKernel_translation (g : ℝ → ℂ) (r : ℝ) (x y : ℍ) :
    radialPoincareKernel 0 g (r+ᵥx) (r+ᵥy)=radialPoincareKernel 0 g x y := by
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  apply tsum_congr
  intro γ
  rw [gamma_zero_vadd,(isometry_real_vadd r).dist_eq]

theorem cylinder_translationLabel_vadd (n : ℤ) (z : ℍ) :
    translationLabel (n:ℚ) • z=(n:ℝ)+ᵥz := by
  rw [label_action]
  apply UpperHalfPlane.ext
  rw [AsymptoticMobiusFold.translation_action,coe_vadd]
  push_cast
  ring

/-- Every actual cylinder column has horizontal period one. -/
theorem cylinderTimeColumn_periodic (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (z : ℍ) :
    Function.Periodic (fun x : ℝ => cylinderTimeColumn f hc he R hR hs (x+ᵥz)) 1 := by
  intro x
  have hh := cylinderAbelColumn_invariant (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
    (evenCoshLift_support_of_time_support f R hR hs)
    ⟨translationLabel (1:ℚ),translation_mem 0 1⟩ (x+ᵥz)
  change cylinderTimeColumn f hc he R hR hs (translationLabel (1:ℚ) • (x+ᵥz))=_ at hh
  change cylinderTimeColumn f hc he R hR hs (translationLabel ((1:ℤ):ℚ) • (x+ᵥz))=_ at hh
  rw [cylinder_translationLabel_vadd,Int.cast_one,←add_vadd,add_comm 1 x] at hh
  exact hh

/-- Exact mean cancellation for the literal cylinder packet column. The
remaining centered energy is a diagonal-minus-period-integral expression. -/
theorem cylinderTimeColumn_centered_kernel (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (z : ℍ) :
    ‖cylinderTimeColumn f hc he R hR hs z-
      ∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz)‖^2=
      (radialPoincareKernel 0 (abelProfile (evenCoshLift (timeConvolution f f))) z z).re-
        (∫ y in Icc (0:ℝ) 1,
          radialPoincareKernel 0 (abelProfile (evenCoshLift (timeConvolution f f))) (y+ᵥz) z).re := by
  let c := fun x : ℝ => cylinderTimeColumn f hc he R hR hs (x+ᵥz)
  have hcont : Continuous c :=
    (cylinderAbelColumn_continuous _ _ R hR _).comp (cylinder_vadd_continuous z)
  have hstat (r x y : ℝ) : inner ℂ (c (x+r)) (c (y+r))=inner ℂ (c x) (c y) := by
    dsimp only [c]
    rw [cylinderTimeSquare_kernel_cross f hc he hr R hR hs,
      cylinderTimeSquare_kernel_cross f hc he hr R hR hs]
    rw [add_comm x r,add_comm y r,add_vadd,add_vadd,cylinderRadialKernel_translation]
  have hh := stationary_column_centered_norm c hcont
    (cylinderTimeColumn_periodic f hc he R hR hs z) hstat 0
  have hdiag : ‖cylinderTimeColumn f hc he R hR hs z‖^2=
      (radialPoincareKernel 0 (abelProfile (evenCoshLift (timeConvolution f f))) z z).re := by
    rw [←inner_self_eq_norm_sq (𝕜:=ℂ),cylinderTimeSquare_kernel_cross f hc he hr R hR hs]
    rfl
  simpa only [c,zero_vadd,hdiag,cylinderTimeSquare_kernel_cross f hc he hr R hR hs] using hh

#print axioms gamma_zero_vadd
#print axioms cylinder_vadd_continuous
#print axioms cylinderRadialKernel_translation
#print axioms cylinder_translationLabel_vadd
#print axioms cylinderTimeColumn_periodic
#print axioms cylinderTimeColumn_centered_kernel

end QuantitativeMaass
