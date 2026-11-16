module

public import QuantitativeMaassHyperbolicAbelMassV1
public import QuantitativeMaassRadialKernelSymmetryV1
public import QuantitativeMaassPoincareComplexUnfoldV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The absolute Poincare series dominates the norm pointwise. Compact
support and proper discontinuity justify each finite sum in this comparison. -/
theorem poincareSum_norm_le {G A : Type*} [Group G] [TopologicalSpace A]
    [LocallyCompactSpace A] [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (f : A → ℂ) (hc : HasCompactSupport f) (z : A) :
    ‖poincareSum (G:=G) f z‖≤(poincareSum (G:=G) (fun x => (‖f x‖:ℂ)) z).re := by
  classical
  obtain ⟨S,U,hU,hS⟩ := compact_seed_locally_finite (G:=G) f hc z
  have hfin (γ : G) (hγ : γ∉S) : f (γ•z)=0 := hS z (mem_of_mem_nhds hU) γ hγ
  have hnorm (γ : G) (hγ : γ∉S) : (‖f (γ•z)‖:ℂ)=0 := by rw [hfin γ hγ,norm_zero,Complex.ofReal_zero]
  change ‖∑' γ : G,f (γ•z)‖≤(∑' γ : G,(‖f (γ•z)‖:ℂ)).re
  rw [tsum_eq_sum hfin,tsum_eq_sum hnorm]
  simpa using norm_sum_le S (fun γ : G => f (γ•z))

/-- Quotient columns are absolutely integrable and have exactly the ambient
radial mass, by normalized projective-group unfolding. -/
theorem radialPoincareKernel_mass (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (w : ℍ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) :
    Integrable (radialPoincareKernel N g w) (quotientMeasure N) ∧
    (∫ z,radialPoincareKernel N g w z ∂quotientMeasure N)=
      (2*Real.pi:ℂ)*∫ q in Ioi (1:ℝ),g q := by
  have he : upperFunction (radialFunction g w)=(fun z : ℍ => g (Real.cosh (dist z w))) :=
    funext (radialFunction_upper g w)
  have hcont : Continuous (upperFunction (radialFunction g w)) := by
    rw [he]
    exact hg.continuous.comp (Real.continuous_cosh.comp (continuous_id.dist continuous_const))
  have hi : Integrable (upperFunction (radialFunction g w)) := by
    rw [he]
    exact hyperbolic_radial_integrable g hg.continuous w R hR hs
  have h := integral_poincare_unfold volume
    (fun γ : gamma N => AsymptoticRationalGroup.measurePreserving γ.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (upperFunction (radialFunction g w)) hcont.measurable hi
  change Integrable (radialPoincareKernel N g w) (quotientMeasure N) ∧
    (∫ z,radialPoincareKernel N g w z ∂quotientMeasure N)=
      ∫ z : ℍ,upperFunction (radialFunction g w) z at h
  rw [he,integral_hyperbolic_radial] at h
  exact h

/-- Uniform absolute row/column bound for the literal quotient kernel.
This is the geometric bound needed in a Schur operator construction. -/
theorem radialPoincareKernel_integral_norm_le (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (w : ℍ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) :
    (∫ z,‖radialPoincareKernel N g w z‖ ∂quotientMeasure N)≤
      (2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖ := by
  let f : ℍ → ℂ := upperFunction (radialFunction g w)
  have he : f=(fun z : ℍ => g (Real.cosh (dist z w))) := funext (radialFunction_upper g w)
  have hc : HasCompactSupport f := (radialSeed g hg w R hR hs).compact
  have hcont : Continuous f := by
    rw [he]
    exact hg.continuous.comp (Real.continuous_cosh.comp (continuous_id.dist continuous_const))
  have hi : Integrable f := hcont.integrable_of_hasCompactSupport hc
  have hn := integral_poincare_unfold volume
    (fun γ : gamma N => AsymptoticRationalGroup.measurePreserving γ.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (fun x => (‖f x‖:ℂ)) (Complex.continuous_ofReal.comp hcont.norm).measurable
    hi.norm.ofReal
  change Integrable (poincareSum (G:=gamma N) (fun x => (‖f x‖:ℂ))) (quotientMeasure N) ∧
    (∫ z,poincareSum (G:=gamma N) (fun x => (‖f x‖:ℂ)) z ∂quotientMeasure N)=
      ∫ z : ℍ,(‖f z‖:ℂ) at hn
  have hp := (radialPoincareKernel_mass N g hg w R hR hs).1
  have hb := integral_mono hp.norm hn.1.re (fun z => poincareSum_norm_le (G:=gamma N) f hc z)
  rw [integral_re hn.1,hn.2,integral_complex_ofReal] at hb
  change (∫ z,‖radialPoincareKernel N g w z‖ ∂quotientMeasure N)≤
    ∫ z : ℍ,‖f z‖ at hb
  rw [he,integral_hyperbolic_radial_norm] at hb
  exact hb

theorem radialPoincareKernel_row_norm_le (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (z : ℍ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) :
    (∫ w,‖radialPoincareKernel N g w z‖ ∂quotientMeasure N)≤
      (2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖ := by
  simp_rw [radialPoincareKernel_symm N g]
  exact radialPoincareKernel_integral_norm_le N g hg z R hR hs

/-- Exact normalization also survives projective congruence periodization. -/
theorem radialPoincareKernel_abel_mass (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (w : ℍ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫ z,radialPoincareKernel N (abelProfile F) w z ∂quotientMeasure N)=
      ∫ t,coshTimeTest F t*(Real.cosh (t/2):ℂ) := by
  rw [(radialPoincareKernel_mass N _ (abelProfile_smooth F hF hc) w R hR
    (abelProfile_support F _ hs)).2,abelProfile_time_mass F hF hc R hR hs]

#print axioms poincareSum_norm_le
#print axioms radialPoincareKernel_mass
#print axioms radialPoincareKernel_integral_norm_le
#print axioms radialPoincareKernel_row_norm_le
#print axioms radialPoincareKernel_abel_mass

end QuantitativeMaass
