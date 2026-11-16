module

public import QuantitativeArithmeticMaassOverlapTheoryV4
public import QuantitativeMaassRadialCompactEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeMaass
open scoped Topology ContDiff ENNReal

namespace QuantitativeArithmeticMaassOverlap

/-- An explicit multiplicity, uniform in positive level and in all profiles
of radius R and all centres in the L-ball. The extra unit of radius makes
the support inclusion into the larger ball strict. -/
def energyMultiplicity (o : ℍ) (L R : ℝ) : ℕ :=
  (2*⌈Real.exp (R+L+1+dist o I)⌉₊+1)^4

/-- Explicit overlap on the fixed support used by the radial seed. -/
theorem radial_support_overlap (N : ℕ) [NeZero N] (o : ℍ) (L R : ℝ)
    (x : ℍ) (S : Finset (gamma N))
    (hS : ∀ γ∈S, γ•x∈Metric.closedBall o (R+L)) :
    S.card≤energyMultiplicity o L R := by
  apply ball_overlap_explicit N o (R+L+1) x S
  intro γ hγ
  have hc : dist (γ•x) o≤R+L := hS γ hγ
  have hopen : γ•x∈Metric.ball o (R+L+1) := by
    change dist (γ•x) o<R+L+1
    linarith
  exact le_of_lt hopen

/-- An explicit bound for the actual quotient-space radial seed vector.
This is a geometric upper bound and assumes no spectral mass lower bound. -/
theorem radialKernel_compact_energy_explicit (N : ℕ) [NeZero N]
    (o : ℍ) (L R : ℝ) (hR : 0≤R)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ) (hx : dist x o≤L) :
    ENNReal.ofReal (‖poincareSeedVector N (radialSeed g hg x R hR hs)‖^2)≤
      (energyMultiplicity o L R:ℝ≥0∞)*
        ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2) := by
  have hM := compact_poincare_energy_bound_of_overlap volume
    (fun γ : gamma N => AsymptoticRationalGroup.measurePreserving γ.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (Metric.closedBall o (R+L)) (isCompact_closedBall o (R+L))
    (energyMultiplicity o L R) (radial_support_overlap N o L R)
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
    (energyMultiplicity o L R:ℝ≥0∞)*∫⁻ y,ENNReal.ofReal (‖f y‖^2) at hb
  rw [radialKernel_row_energy N g hg R hR hs x,
    radialKernel_row_lintegral N g hg R hR hs x]
  apply hb.trans_eq
  congr 1
  rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hyperbolic_radial_norm_square_integrable g hg x R hR hs)
    (Eventually.of_forall (fun _ => sq_nonneg _)),integral_hyperbolic_radial_norm_square]

/-- The actual localized double-kernel energy with the explicit geometric
multiplicity. Cusp control and uniform localized spectral mass remain separate. -/
theorem radialKernel_local_energy_explicit (N : ℕ) [NeZero N]
    (o : ℍ) (L R : ℝ) (hR : 0≤R)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hs : Function.support g⊆Iic (Real.cosh R)) :
    (∫⁻ x in Metric.closedBall o L,∫⁻ y,
      ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2)
      ∂quotientMeasure N ∂quotientMeasure N)≤
      ((energyMultiplicity o L R:ℝ≥0∞)*
        ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2))*
          quotientMeasure N (Metric.closedBall o L) := by
  calc
    _ ≤ ∫⁻ _x in Metric.closedBall o L,
        (energyMultiplicity o L R:ℝ≥0∞)*
          ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2)
          ∂quotientMeasure N := by
      apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
      intro x hx
      rw [← radialKernel_row_lintegral N g hg R hR hs x,
        ← radialKernel_row_energy N g hg R hR hs x]
      exact radialKernel_compact_energy_explicit N o L R hR g hg hs x hx
    _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]

#print axioms radial_support_overlap
#print axioms radialKernel_compact_energy_explicit
#print axioms radialKernel_local_energy_explicit
end QuantitativeArithmeticMaassOverlap
