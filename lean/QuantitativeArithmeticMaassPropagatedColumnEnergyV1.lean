module

public import QuantitativeArithmeticMaassScheduledColumnEnergyV1
public import QuantitativeArithmeticMaassGrowingRectangleTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- Energy is monotone on center regions; local integrability follows
from continuity of the actual Hilbert-valued Abel column. -/
theorem cylinderTimeColumn_energy_mono (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f:ℝ→ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (S : Set ℍ) (o : ℍ) (L : ℝ) (hS : S⊆Metric.closedBall o L) :
    (∫ z in S,‖cylinderTimeColumn f hc he R hR hs z‖^2)≤
      ∫ z in Metric.closedBall o L,‖cylinderTimeColumn f hc he R hR hs z‖^2 := by
  have hcont : Continuous (cylinderTimeColumn f hc he R hR hs) :=
    cylinderAbelColumn_continuous _ _ R hR _
  exact setIntegral_mono_set
    ((hcont.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall o L))
    (Eventually.of_forall (fun z => sq_nonneg _)) (Eventually.of_forall hS)

/-- A logarithmic height-ratio bound places the actual rectangle inside
one of the center balls controlled by the scheduled energy theorem. -/
theorem rectangle_subset_ball_of_size (a b L : ℝ) (ha : 0<a)
    (hsize : (2+b^2)/a≤Real.exp L) :
    upperRectangle 0 1 a b⊆Metric.closedBall I L := by
  intro z hz
  exact (rectangle_dist_bound a b ha z hz).trans
    ((Real.log_le_iff_le_exp (by positivity)).mpr hsize)

end QuantitativeMaass
namespace QuantitativeMaass.Scheduled

/-- Both actual column energies on varying rectangles, with every geometric
and propagation factor absorbed into a fixed exponential. -/
theorem rectangle_column_energy_schedule (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (a b : ℝ→ℝ) (ha : ∀ t,0<a t) (H : ℝ) (hH : 0≤H)
    (hsize : ∀ᶠ t in atTop,(2+(b t)^2)/(a t)≤Real.exp (H*Strong.strongScale t))
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ E : ℝ,0<E ∧ ∀ᶠ t in atTop,
      (∫ z in upperRectangle 0 1 (a t) (b t),‖column K hc he ε t z‖^2)≤
        (t*ε t)*Real.exp (E*Strong.strongScale t) ∧
      (∫ z in upperRectangle 0 1 (a t) (b t),‖residualColumn K hc he ε t z‖^2)≤
        (t^3*ε t)*Real.exp (E*Strong.strongScale t) := by
  obtain ⟨E₁,hE₁,hsource⟩ := source_column_energy_schedule K hc he hK hm I H hH ε hε hproduct
  obtain ⟨E₂,hE₂,hresid⟩ := residual_column_energy_schedule K hc he hK hm I H hH ε hε hproduct
  refine ⟨max E₁ E₂,lt_of_lt_of_le hE₁ (le_max_left _ _),?_⟩
  filter_upwards [hsource,hresid,hsize,hε,eventually_ge_atTop (1:ℝ)] with t hsource hresid hsize heps ht
  have ht0 : 0≤t := by linarith
  have hscale : 0≤Strong.strongScale t := sq_nonneg _
  have hL : 0≤H*Strong.strongScale t := mul_nonneg hH hscale
  have hsubset := rectangle_subset_ball_of_size (a t) (b t) _ (ha t) hsize
  have hmono₁ := cylinderTimeColumn_energy_mono (time K hc ε t) (time_compact K hc ε t)
    (time_even K hc he ε t) (supportRadius K hc*radius ε t)
    (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t)
    _ I _ hsubset
  have hmono₂ := cylinderTimeColumn_energy_mono (spectralResidualSchwartz t (time K hc ε t))
    (spectralResidualSchwartz_compact t (time K hc ε t) (time_compact K hc ε t))
    (spectralResidualSchwartz_even t (time K hc ε t) (time_even K hc he ε t))
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (spectralTimeResidual_support t (time K hc ε t) _ (time_support K hc ε t)) _ I _ hsubset
  constructor
  · apply (hmono₁.trans (hsource _ hL le_rfl)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg ht0 heps.1.le)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left E₁ E₂) hscale)
  · apply (hmono₂.trans (hresid _ hL le_rfl)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg ht0 _) heps.1.le)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right E₁ E₂) hscale)

/-- Concrete propagated rectangles: no energy or geometric growth bound is
assumed. This supplies the source/residual costs of spectral compression. -/
theorem propagated_rectangle_column_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ E : ℝ,0<E ∧ ∀ᶠ t in atTop,
      (∫ z in propagatedRectangle δ C ε t,‖column K hc he ε t z‖^2)≤
        (t*ε t)*Real.exp (E*Strong.strongScale t) ∧
      (∫ z in propagatedRectangle δ C ε t,‖residualColumn K hc he ε t z‖^2)≤
        (t^3*ε t)*Real.exp (E*Strong.strongScale t) := by
  exact rectangle_column_energy_schedule K hc he hK hm
    (fun t => δ*Real.exp (-(C*radius ε t))) (fun t => Real.exp (Strong.strongScale t))
    (fun _ => mul_pos hδ (Real.exp_pos _)) 4 (by norm_num)
    (propagated_rectangle_size hδ C hC ε hε hproduct) ε hε hproduct

#print axioms rectangle_column_energy_schedule
#print axioms propagated_rectangle_column_energy
end QuantitativeMaass.Scheduled
