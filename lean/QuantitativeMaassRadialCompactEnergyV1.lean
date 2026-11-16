module

public import QuantitativeMaassAbelEnergyTraceV1
public import QuantitativeMaassPoincareFixedSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass

theorem integral_hyperbolic_radial_norm_square (g : ℝ → ℂ) (x : ℍ) :
    (∫ y : ℍ,‖g (Real.cosh (dist y x))‖^2)=(2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2 := by
  have h := integral_hyperbolic_radial (fun q => ((‖g q‖^2:ℝ):ℂ)) x
  simp only [integral_complex_ofReal] at h
  exact_mod_cast h

theorem hyperbolic_radial_norm_square_integrable (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (x : ℍ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) :
    Integrable (fun y : ℍ => ‖g (Real.cosh (dist y x))‖^2) := by
  have he : upperFunction (radialFunction g x)=(fun y : ℍ => g (Real.cosh (dist y x))) :=
    funext (radialFunction_upper g x)
  have hc : Continuous (upperFunction (radialFunction g x)) := by
    rw [he]
    exact hg.continuous.comp (Real.continuous_cosh.comp (continuous_id.dist continuous_const))
  have hL : MemLp (upperFunction (radialFunction g x)) 2 volume :=
    hc.memLp_of_hasCompactSupport (radialSeed g hg x R hR hs).compact
  have hi := (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
  simpa only [he] using hi

/-- One periodization multiplicity controls the energy of ALL radial
profiles of radius R, at ALL centres in a fixed compact ball. The constant
is chosen before the profile and the centre. Its growth is not asserted. -/
theorem radialKernel_compact_energy_bound (N : ℕ) (o : ℍ) (L R : ℝ) (hR : 0≤R) :
    ∃ M : ℕ,∀ (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
      (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ),dist x o≤L →
      ENNReal.ofReal (‖poincareSeedVector N (radialSeed g hg x R hR hs)‖^2)≤
        (M:ℝ≥0∞)*ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2) := by
  obtain ⟨M,hM⟩ := compact_poincare_uniform_energy_bound volume
    (fun γ : gamma N => AsymptoticRationalGroup.measurePreserving γ.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (Metric.closedBall o (R+L)) (isCompact_closedBall o (R+L))
  refine ⟨M,?_⟩
  intro g hg hs x hx
  let f := upperFunction (radialFunction g x)
  have he : f=(fun y : ℍ => g (Real.cosh (dist y x))) := funext (radialFunction_upper g x)
  have hf : Continuous f := by
    rw [he]
    exact hg.continuous.comp (Real.continuous_cosh.comp (continuous_id.dist continuous_const))
  have hsupport : Function.support f⊆Metric.closedBall o (R+L) := by
    intro y hy
    have hxy : dist y x≤R := radialFunction_support g x R hR hs (subset_tsupport f hy)
    exact (dist_triangle y x o).trans (add_le_add hxy hx)
  have hb := hM f hf.measurable hsupport
  change (∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2) ∂quotientMeasure N)≤
    (M:ℝ≥0∞)*∫⁻ y,ENNReal.ofReal (‖f y‖^2) at hb
  rw [radialKernel_row_energy N g hg R hR hs x,radialKernel_row_lintegral N g hg R hR hs x]
  apply hb.trans_eq
  congr 1
  rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hyperbolic_radial_norm_square_integrable g hg x R hR hs)
    (Eventually.of_forall (fun _ => sq_nonneg _)),integral_hyperbolic_radial_norm_square]

/-- Localized geometric squared-kernel energy is finite, with a uniform
bound in terms of the one-dimensional radial energy. No global cusp
integrability or moving-radius bound is concluded here. -/
theorem radialKernel_local_energy_bound (N : ℕ) [NeZero N] (o : ℍ) (L R : ℝ) (hR : 0≤R) :
    ∃ M : ℕ,∀ (g : ℝ → ℂ) (_hg : ContDiff ℝ ∞ g)
      (_hs : Function.support g⊆Iic (Real.cosh R)),
      (∫⁻ x in Metric.closedBall o L,∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2)
        ∂quotientMeasure N ∂quotientMeasure N)≤
        ((M:ℝ≥0∞)*ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2))*
          quotientMeasure N (Metric.closedBall o L) := by
  obtain ⟨M,hM⟩ := radialKernel_compact_energy_bound N o L R hR
  refine ⟨M,?_⟩
  intro g hg hs
  calc
    _ ≤ ∫⁻ _x in Metric.closedBall o L,
        (M:ℝ≥0∞)*ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2) ∂quotientMeasure N := by
      apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
      intro x hx
      rw [← radialKernel_row_lintegral N g hg R hR hs x,← radialKernel_row_energy N g hg R hR hs x]
      exact hM g hg hs x hx
    _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]

theorem radialKernel_local_energy_finite (N : ℕ) [NeZero N] (o : ℍ) (L R : ℝ) (hR : 0≤R)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hs : Function.support g⊆Iic (Real.cosh R)) :
    (∫⁻ x in Metric.closedBall o L,∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2)
      ∂quotientMeasure N ∂quotientMeasure N)<(∞:ℝ≥0∞) := by
  obtain ⟨M,hM⟩ := radialKernel_local_energy_bound N o L R hR
  apply (hM g hg hs).trans_lt
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)
    (measure_lt_top _ _)

#print axioms integral_hyperbolic_radial_norm_square
#print axioms hyperbolic_radial_norm_square_integrable
#print axioms radialKernel_compact_energy_bound
#print axioms radialKernel_local_energy_bound
#print axioms radialKernel_local_energy_finite

end QuantitativeMaass
