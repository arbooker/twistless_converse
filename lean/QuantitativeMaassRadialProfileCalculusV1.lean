module

public import QuantitativeMaassRadialSeedV1
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Support

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem radialLaplacianProfile_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (radialLaplacianProfile g) := by
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hg'' := (contDiff_infty_iff_deriv.mp hg').2
  have hz : ContDiff ℝ ∞ (fun q : ℝ => (q:ℂ)) := Complex.ofRealCLM.contDiff
  unfold radialLaplacianProfile
  fun_prop

theorem radialLaplacianProfile_support (g : ℝ → ℂ) (B : ℝ)
    (hs : Function.support g⊆Iic B) : Function.support (radialLaplacianProfile g)⊆Iic B := by
  have ht : tsupport g⊆Iic B := closure_minimal hs isClosed_Iic
  have h1 : Function.support (deriv g)⊆Iic B := support_deriv_subset.trans ht
  have h2 : Function.support (deriv (deriv g))⊆Iic B :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans ht)
  intro q hq
  by_contra hn
  have hd1 : deriv g q=0 := by
    by_contra h
    exact hn (h1 h)
  have hd2 : deriv (deriv g) q=0 := by
    by_contra h
    exact hn (h2 h)
  exact hq (by simp [radialLaplacianProfile,hd1,hd2])

theorem deriv_real_profile (g : ℝ → ℂ) (hr : ∀ q,star (g q)=g q) (q : ℝ) :
    star (deriv g q)=deriv g q := by
  rw [← deriv.star]
  simp_rw [hr]

theorem radialLaplacianProfile_real (g : ℝ → ℂ) (hr : ∀ q,star (g q)=g q) (q : ℝ) :
    star (radialLaplacianProfile g q)=radialLaplacianProfile g q := by
  have h1 := deriv_real_profile g hr
  have h2 := deriv_real_profile (deriv g) h1
  simp [radialLaplacianProfile,star_mul,h1,h2]
  ring

/-- The differential column is precisely another radial seed class. -/
theorem radialSeed_laplacian_vector (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (x : ℍ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) :
    poincareSeedVector N (radialSeed g hg x R hR hs).laplacian=
      poincareSeedVector N (radialSeed (radialLaplacianProfile g)
        (radialLaplacianProfile_smooth g hg) x R hR (radialLaplacianProfile_support g _ hs)) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [poincareSeedVector_coeFn N (radialSeed g hg x R hR hs).laplacian,
    poincareSeedVector_coeFn N (radialSeed (radialLaplacianProfile g)
      (radialLaplacianProfile_smooth g hg) x R hR (radialLaplacianProfile_support g _ hs))] with y hy hz
  rw [hy,hz]
  apply tsum_congr
  intro γ
  change upperLaplacian (radialFunction g x) (γ•y)=
    upperFunction (radialFunction (radialLaplacianProfile g) x) (γ•y)
  rw [radialFunction_laplacian g hg,radialFunction_upper]

#print axioms radialLaplacianProfile_smooth
#print axioms radialLaplacianProfile_support
#print axioms radialLaplacianProfile_real
#print axioms radialSeed_laplacian_vector

end QuantitativeMaass
