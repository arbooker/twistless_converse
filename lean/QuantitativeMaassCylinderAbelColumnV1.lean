module

public import QuantitativeMaassCylinderKernelSupportV1
public import QuantitativeMaassAbelColumnContinuityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Literal Abel kernel rows on the infinite-volume translation cylinder
are L2: their intersection with the translation strip has compact support. -/
theorem cylinderAbelKernel_memLp (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    MemLp (radialPoincareKernel 0 (abelProfile F) x) 2 (quotientMeasure 0) := by
  let K := upperRectangle 0 1 (Real.exp (Real.log x.im-(R+0))) (Real.exp (Real.log x.im+(R+0)))
  have hK : IsCompact K := upperRectangle_compact _ _ _ _ (Real.exp_pos _)
  have hcont : Continuous (radialPoincareKernel 0 (abelProfile F) x) :=
    Continuous.uncurry_left x (oneSidedAbelKernel_joint_continuous 0 F hF R hR hs)
  obtain ⟨D,hD,hbound⟩ := oneSidedAbelKernel_local_bound 0 F hF R hR hs x 0
  have hcompact : HasCompactSupport (K.indicator (radialPoincareKernel 0 (abelProfile F) x)) :=
    hK.of_isClosed_subset isClosed_closure
      (closure_minimal (by
        intro y hy
        by_contra hn
        exact hy (Set.indicator_of_notMem hn _)) hK.isClosed)
  have hLp : MemLp (K.indicator (radialPoincareKernel 0 (abelProfile F) x)) 2 volume := by
    apply hcompact.memLp_of_bound (hcont.aestronglyMeasurable.indicator hK.measurableSet) D
    filter_upwards with y
    by_cases hy : y∈K
    · rw [Set.indicator_of_mem hy]
      exact hbound x (by simp) y
    · rw [Set.indicator_of_notMem hy,norm_zero]
      exact hD
  rw [translation_quotient_measure]
  apply (hLp.restrict strip).ae_eq
  filter_upwards [ae_restrict_mem strip_measurable] with y hy
  by_cases hk : y∈K
  · exact Set.indicator_of_mem hk _
  · rw [Set.indicator_of_notMem hk]
    symm
    by_contra hn
    exact hk (cylinderRadialKernel_strip_support (abelProfile F) R hR (abelProfile_support F _ hs)
      x x 0 (by simp) y hy hn)

def cylinderAbelColumn (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    Lp ℂ 2 (quotientMeasure 0) :=
  (cylinderAbelKernel_memLp F hF R hR hs x).toLp (radialPoincareKernel 0 (abelProfile F) x)

theorem cylinderAbelColumn_coeFn (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (x : ℍ) :
    cylinderAbelColumn F hF R hR hs x=ᵐ[quotientMeasure 0]radialPoincareKernel 0 (abelProfile F) x :=
  (cylinderAbelKernel_memLp F hF R hR hs x).coeFn_toLp

/-- Exact center invariance of the actual cylinder Hilbert columns. -/
theorem cylinderAbelColumn_invariant (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (γ : gamma 0) (x : ℍ) :
    cylinderAbelColumn F hF R hR hs (γ•x)=cylinderAbelColumn F hF R hR hs x := by
  apply Lp.ext
  filter_upwards [cylinderAbelColumn_coeFn F hF R hR hs (γ•x),
    cylinderAbelColumn_coeFn F hF R hR hs x] with y h1 h2
  rw [h1,h2,radialPoincareKernel_center_invariant]

#print axioms cylinderAbelKernel_memLp
#print axioms cylinderAbelColumn_coeFn
#print axioms cylinderAbelColumn_invariant

end QuantitativeMaass
