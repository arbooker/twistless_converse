module

public import QuantitativeArithmeticMaassMovingCollarEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The difference between sharp area and squared smooth-cutoff mass is
nonnegative and bounded by the actual rectangular collar area. -/
theorem rectangleSmoothSeed_mass_difference (a b h : ℝ) (ha : 0<a) (hh : 0<h) :
    let S := upperRectangle 0 1 a b
    let Ω := S \ upperRectangle h (1-h) (a+h) (b-h)
    let u := upperFunction (rectangleSmoothSeed 0 1 a b h ha hh).toFun
    0≤volume.real S-(∫ z in S,‖u z‖^2) ∧
      volume.real S-(∫ z in S,‖u z‖^2)≤volume.real Ω := by
  intro S Ω u
  have hS := upperRectangle_compact 0 1 a b ha
  have hΩ : MeasurableSet Ω := hS.measurableSet.diff (upperRectangle_measurable _ _ _ _)
  have h1 : IntegrableOn (fun _ : ℍ => (1:ℝ)) S :=
    continuous_const.continuousOn.integrableOn_compact hS
  have hu : Continuous u := upperFunction_continuous (rectangleSmoothSeed 0 1 a b h ha hh).smooth
  have hf : IntegrableOn (fun z => ‖u z‖^2) S := (hu.norm.pow 2).continuousOn.integrableOn_compact hS
  have hid : volume.real S-(∫ z in S,‖u z‖^2)=∫ z in S,1-‖u z‖^2 := by
    rw [integral_sub h1 hf,setIntegral_const]
    simp only [smul_eq_mul,mul_one]
  rw [hid]
  constructor
  · apply setIntegral_nonneg hS.measurableSet
    intro z _
    exact sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) (rectangleCutoffFunction_bounds 0 1 a b h z).2)
  · calc
      _ ≤ ∫ z in S,Ω.indicator (fun _ => (1:ℝ)) z := by
        apply setIntegral_mono_on (h1.sub hf) (h1.indicator hΩ) hS.measurableSet
        intro z hz
        change 1-‖u z‖^2≤_
        by_cases hmem : z∈Ω
        · rw [Set.indicator_of_mem hmem]
          linarith [sq_nonneg ‖u z‖]
        · rw [Set.indicator_of_notMem hmem]
          have hz' := (rectangleSmoothSeed_collar 0 1 a b h ha hh z).2
          simp only [zero_add] at hz'
          have heq : (1:ℂ)=u z := by
            have heq' := hz' hmem
            rw [Set.indicator_of_mem (show z∈upperRectangle 0 1 a b from hz)] at heq'
            exact heq'
          rw [←heq,norm_one,one_pow,sub_self]
      _ = volume.real Ω := by
        rw [integral_indicator_const _ hΩ,measureReal_restrict_apply hΩ,
          inter_eq_left.mpr (show Ω⊆S from sdiff_subset)]
        simp only [smul_eq_mul,mul_one]

/-- Sharp and smooth cutoff masses differ negligibly with every fixed
strong-scale weight for a sufficiently thin, explicitly bounded collar. -/
theorem movingCutoffMass_difference_limit {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (D W : ℝ) (hD : 0≤D) (hDW : W+3≤D) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      ‖volume.real (cutoffRectangle (movingLowerEdge δ C ε t) t)-
        (∫ z in cutoffRectangle (movingLowerEdge δ C ε t) t,
          ‖upperFunction (cutoffSeed (movingLowerEdge δ C ε t) D t
            (movingLowerEdge_pos hδ C ε t)).toFun z‖^2)‖) atTop (𝓝 0) := by
  have hlim := movingCutoffCollar_area_weighted_limit hδ C hC ε hε hp D W hD hDW
  apply squeeze_zero' (Eventually.of_forall (fun _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))) _ hlim
  filter_upwards with t
  have hh := rectangleSmoothSeed_mass_difference (movingLowerEdge δ C ε t)
    (Real.exp (Strong.strongScale t/2)) (Real.exp (-(D*Strong.strongScale t)))
    (movingLowerEdge_pos hδ C ε t) (Real.exp_pos _)
  dsimp only at hh
  simp only [cutoffRectangle,cutoffSeed,cutoffCollar]
  rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
  exact mul_le_mul_of_nonneg_left hh.2 (Real.exp_pos _).le

#print axioms rectangleSmoothSeed_mass_difference
#print axioms movingCutoffMass_difference_limit
end QuantitativeMaass.Scheduled
