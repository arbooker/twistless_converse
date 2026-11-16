module

public import QuantitativeMaassSchwartzPeriodizationV1
public import QuantitativeMaassCylinderFourierEnergyV1
public import QuantitativeMaassCylinderLatticeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The smooth finite-propagation horizontal profile as an actual Schwartz map. -/
def parabolicLineSchwartz (g : ℝ→ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1))
    (B : ℝ) (hs : Function.support g⊆Iic B) (y : ℝ) (hy : 0<y) : SchwartzMap ℝ ℂ :=
  (parabolicLineProfile_compact g B hs y hy).toSchwartzMap (parabolicLineProfile_smooth g hg y)

theorem cylinderRadialKernel_periodization (g : ℝ→ℂ) (z : ℍ) (x : ℝ) :
    radialPoincareKernel 0 g (x+ᵥz) z=
      ∑' k : ℤ,parabolicLineProfile g z.im (x+k) := by
  rw [radialPoincareKernel_symm,cylinderRadialKernel_line_sum g (x+ᵥz) z (vadd_im x z)]
  apply tsum_congr
  intro k
  simp only [vadd_im,vadd_re]
  congr 1
  ring

/-- Fourier transform values at every integer frequency agree exactly with
Fourier coefficients of the actual cylinder kernel. -/
theorem parabolicLine_fourier_coefficient (g : ℝ→ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1))
    (B : ℝ) (hs : Function.support g⊆Iic B) (z : ℍ) (n : ℤ) :
    𝓕 (parabolicLineProfile g z.im) n=
      ∫ x in Icc (0:ℝ) 1,periodCharacter (-n) x*radialPoincareKernel 0 g (x+ᵥz) z := by
  have hh := schwartz_periodized_fourier (parabolicLineSchwartz g hg B hs z.im z.im_pos) n
  simp_rw [cylinderRadialKernel_periodization]
  exact hh.symm

#print axioms cylinderRadialKernel_periodization
#print axioms parabolicLine_fourier_coefficient

end QuantitativeMaass
