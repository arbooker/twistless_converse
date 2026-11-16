module

public import QuantitativeMaassPhysicalRadialSeedV1
public import QuantitativeMaassPhysicalProfileExtensionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The usual radial differential expression is valid away from the centre
for a profile smooth only on its physical half-line. -/
theorem radialFunction_laplacian_physical (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ)
    (hs : Function.support g ⊆ Iic B) (w z : ℍ) (hzw : z ≠ w) :
    upperLaplacian (radialFunction g w) z =
      radialLaplacianProfile g (Real.cosh (dist z w)) := by
  let q := Real.cosh (dist z w)
  have hq : 1 < q := Real.one_lt_cosh.mpr (dist_pos.mpr hzw).ne'
  let b := (1+q)/2
  have hb : 1 < b := by dsimp [b]; linarith
  have hbq : b < q := by dsimp [b]; linarith
  obtain ⟨G,hG,_,hGg⟩ := physicalProfile_exists_extension g hg B hs b hb
  have he : G =ᶠ[𝓝 q] g := by
    filter_upwards [Ioi_mem_nhds hbq] with x hx
    exact hGg x hx.le
  have hcoord : ContinuousAt (radialCoordinate w.re w.im) (z.re,z.im) :=
    ((radialCoordinate_smooth w.re w.im (ne_of_gt w.im_pos))
      (z.re,z.im) z.im_pos).continuousWithinAt.continuousAt
        (IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd) z.im_pos)
  have hqeq : radialCoordinate w.re w.im (z.re,z.im) = q :=
    radialCoordinate_eq_cosh_dist z w
  change Tendsto (radialCoordinate w.re w.im) (𝓝 (z.re,z.im))
    (𝓝 (radialCoordinate w.re w.im (z.re,z.im))) at hcoord
  rw [hqeq] at hcoord
  have hr : radialFunction G w =ᶠ[𝓝 (z.re,z.im)] radialFunction g w :=
    he.comp_tendsto hcoord
  have hlap := hyperbolic_congr_eventually hr
  change upperLaplacian (radialFunction G w) z =
    upperLaplacian (radialFunction g w) z at hlap
  rw [← hlap, radialFunction_laplacian G hG]
  change radialLaplacianProfile G q = radialLaplacianProfile g q
  simp only [radialLaplacianProfile, he.deriv_eq, he.deriv.deriv_eq]

#print axioms radialFunction_laplacian_physical

end QuantitativeMaass
