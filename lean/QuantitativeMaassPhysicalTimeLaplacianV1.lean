module

public import QuantitativeMaassPhysicalTimeIntertwiningV1
public import QuantitativeMaassPhysicalRadialLaplacianV1
public import QuantitativeMaassPhysicalAbelSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The exact differential identity on actual compact time-kernel columns,
including the centre of the radial kernel. -/
theorem physicalTimeRadial_laplacian (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) (w z : ℍ) :
    upperLaplacian (radialFunction (abelProfile (evenCoshLift f)) w) z =
      (1/4 : ℂ) * abelProfile (evenCoshLift f) (Real.cosh (dist z w)) -
        abelProfile (evenCoshLift (deriv (deriv f))) (Real.cosh (dist z w)) := by
  have hsF : Function.support (evenCoshLift f) ⊆ Iic (Real.cosh R) := by
    intro x hx
    by_contra hn
    exact hx (evenCoshLift_zero_above f R hR hs x (lt_of_not_ge hn))
  have hg := abelProfile_smoothOn_physical (evenCoshLift f)
    (evenCoshLift_smoothOn f hf he hc) (Real.cosh R) (Real.one_le_cosh R) hsF
  have haway (z : ℍ) (hz : z ≠ w) :
      upperLaplacian (radialFunction (abelProfile (evenCoshLift f)) w) z =
        (1/4 : ℂ) * abelProfile (evenCoshLift f) (Real.cosh (dist z w)) -
          abelProfile (evenCoshLift (deriv (deriv f))) (Real.cosh (dist z w)) := by
    rw [radialFunction_laplacian_physical _ hg (Real.cosh R)
      (abelProfile_support _ _ hsF) w z hz,
      abelProfile_evenCoshLift_laplacian f hf he hc R hR hs _
        (Real.one_lt_cosh.mpr (dist_pos.mpr hz).ne')]
  by_cases hz : z ≠ w
  · exact haway z hz
  · have hzw : z = w := not_ne_iff.mp hz
    subst z
    have hf2 : ContDiff ℝ ∞ (deriv (deriv f)) :=
      (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2
    have hs2 : Function.support (deriv (deriv f)) ⊆ Icc (-R) R :=
      support_deriv_subset.trans (closure_minimal
        (support_deriv_subset.trans (closure_minimal hs isClosed_Icc)) isClosed_Icc)
    have hsF2 : Function.support (evenCoshLift (deriv (deriv f))) ⊆ Iic (Real.cosh R) := by
      intro x hx
      by_contra hn
      exact hx (evenCoshLift_zero_above _ R hR hs2 x (lt_of_not_ge hn))
    have hg2 := abelProfile_smoothOn_physical _
      (evenCoshLift_smoothOn _ hf2 (even_time_second_deriv_even f he) hc.deriv.deriv)
      (Real.cosh R) (Real.one_le_cosh R) hsF2
    have hleft := upperLaplacian_continuous (radialFunction_smoothOn_physical _ hg w)
    have hright : Continuous (fun z : ℍ =>
        (1/4 : ℂ) * abelProfile (evenCoshLift f) (Real.cosh (dist z w)) -
          abelProfile (evenCoshLift (deriv (deriv f))) (Real.cosh (dist z w))) := by
      have h1 := upperFunction_continuous (radialFunction_smoothOn_physical _ hg w)
      have h2 := upperFunction_continuous (radialFunction_smoothOn_physical _ hg2 w)
      convert (h1.const_mul (1/4 : ℂ)).sub h2 using 1
      ext z
      simp only [Pi.sub_apply, radialFunction_upper]
    have hv : Continuous (fun x : ℝ => x +ᵥ w) := by
      apply continuous_induced_rng.mpr
      fun_prop
    have hall := Continuous.ext_on (dense_compl_singleton (0 : ℝ))
      (hleft.comp hv) (hright.comp hv) (by
        intro t ht
        apply haway
        intro heq
        have hre := congrArg UpperHalfPlane.re heq
        simp only [vadd_re] at hre
        have ht0 : t = 0 := by linarith
        exact ht (by simpa using ht0))
    simpa only [Function.comp_apply, zero_vadd] using congrFun hall 0

#print axioms physicalTimeRadial_laplacian

end QuantitativeMaass
