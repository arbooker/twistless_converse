module

public import QuantitativeArithmeticMaassPropagatedColumnEnergyV1
public import QuantitativeArithmeticMaassRectangleGradientV1
public import QuantitativeMaassAbelCutoffDerivativeBoundV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The upper edge grows more slowly than the available propagation box;
the collar may shrink at any fixed exponential rate in strongScale. -/
def cutoffRectangle (δ t : ℝ) : Set ℍ :=
  upperRectangle 0 1 δ (Real.exp (Strong.strongScale t/2))

def cutoffSeed (δ D t : ℝ) (hδ : 0<δ) : SmoothUpperSeed :=
  rectangleSmoothSeed 0 1 δ (Real.exp (Strong.strongScale t/2))
    (Real.exp (-(D*Strong.strongScale t))) hδ (Real.exp_pos _)

theorem cutoffSeed_support (δ D t : ℝ) (hδ : 0<δ) :
    tsupport (upperFunction (cutoffSeed δ D t hδ).toFun)⊆cutoffRectangle δ t :=
  rectangleSmoothSeed_support _ _ _ _ _ hδ (Real.exp_pos _)

theorem cutoffSeed_bound (δ D t : ℝ) (hδ : 0<δ) (z : ℍ) :
    ‖upperFunction (cutoffSeed δ D t hδ).toFun z‖≤1 :=
  (rectangleCutoffFunction_bounds 0 1 δ _ _ z).2

theorem cutoffSeed_real (δ D t : ℝ) (hδ : 0<δ) (Z : MaassDifferential.Point) :
    star ((cutoffSeed δ D t hδ).toFun Z)=(cutoffSeed δ D t hδ).toFun Z :=
  rectangleSmoothSeed_real _ _ _ _ _ hδ (Real.exp_pos _) Z

/-- A fixed coefficient times the propagation radius is negligible on
the stronger scale, uniformly for every admissible window schedule. -/
theorem radius_mul_le_half_strong (C : ℝ) (hC : 0≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,C*radius ε t≤Strong.strongScale t/2 := by
  have hp := (propagation_limits slowScale ε
    (slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)))
    (hε.mono (fun _ h => h.1)) hproduct).1
  filter_upwards [radius_eventually_eq ε hε hproduct,
    hp.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    slowScale_tendsto.eventually (eventually_ge_atTop (max 1 (2*C)))] with t hr hp hL
  have hL1 : 1≤slowScale t := (le_max_left _ _).trans hL
  have hLC : 2*C≤slowScale t := (le_max_right _ _).trans hL
  have hRL : radius ε t≤slowScale t := by
    rw [hr]
    exact (div_le_one (by linarith : 0<slowScale t)).mp hp.le
  have hm := mul_le_mul_of_nonneg_left hRL hC
  change _≤(slowScale t)^2/2
  nlinarith

/-- The finite-propagation enlargement of the actual cutoff support fits
inside the rectangles whose source and residual energies were proved. -/
theorem cutoff_propagation_subset {δ : ℝ} (_hδ : 0<δ) (U : ℝ) (hU : 0≤U)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,
      upperRectangle 0 1 (δ*Real.exp (-(U*radius ε t)))
        (Real.exp (Strong.strongScale t/2)*Real.exp (U*radius ε t))⊆
          propagatedRectangle δ U ε t := by
  filter_upwards [radius_mul_le_half_strong U hU ε hε hproduct] with t ht
  intro z hz
  refine ⟨hz.1,hz.2.1,hz.2.2.trans ?_⟩
  rw [←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The moving smooth cutoff has an explicit exponential gradient bound;
there is no compactness constant depending silently on t. -/
theorem cutoffSeed_gradient {δ : ℝ} (hδ : 0<δ) (D : ℝ) :
    ∀ᶠ t in atTop,∀ z∈cutoffRectangle δ t,
      (upperEnergy (cutoffSeed δ D t hδ).toFun (cutoffSeed δ D t hδ).toFun z).re≤
        (Real.exp ((D+2)*Strong.strongScale t))^2 := by
  obtain ⟨B,hB,hderiv⟩ := smoothTransition_deriv_bounded
  filter_upwards [(Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
    (eventually_ge_atTop (4*B))] with t ht
  intro z hz
  have hg := rectangleSmoothSeed_gradient_quantitative B hB hderiv
    0 1 δ (Real.exp (Strong.strongScale t/2)) (Real.exp (-(D*Strong.strongScale t)))
    hδ (Real.exp_pos _) z hz
  apply hg.trans
  apply pow_le_pow_left₀ (by positivity)
  calc
    4*Real.exp (Strong.strongScale t/2)*B/Real.exp (-(D*Strong.strongScale t)) =
      (4*B)*Real.exp ((D+1/2)*Strong.strongScale t) := by
        rw [show (D+1/2)*Strong.strongScale t=Strong.strongScale t/2+D*Strong.strongScale t by ring,
          Real.exp_add,Real.exp_neg]
        field_simp
    _ ≤ Real.exp (Strong.strongScale t)*Real.exp ((D+1/2)*Strong.strongScale t) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ ≤ Real.exp ((D+2)*Strong.strongScale t) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hs : 0≤Strong.strongScale t := sq_nonneg _
      nlinarith

/-- Source/residual energies on precisely the enlarged rectangle appearing
in the global spectral leakage theorem, for the concrete cutoff family. -/
theorem cutoff_propagation_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    {δ : ℝ} (hδ : 0<δ)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ E : ℝ,0<E ∧ ∀ᶠ t in atTop,
      let R := supportRadius K hc*radius ε t
      let Ω := upperRectangle 0 1 (δ*Real.exp (-R))
        (Real.exp (Strong.strongScale t/2)*Real.exp R)
      (∫ z in Ω,‖column K hc he ε t z‖^2)≤(t*ε t)*Real.exp (E*Strong.strongScale t) ∧
      (∫ z in Ω,‖residualColumn K hc he ε t z‖^2)≤(t^3*ε t)*Real.exp (E*Strong.strongScale t) := by
  obtain ⟨E,hE,henergy⟩ := rectangle_column_energy_schedule K hc he hK hm
    (fun t => δ*Real.exp (-(supportRadius K hc*radius ε t)))
    (fun t => Real.exp (Strong.strongScale t/2)*Real.exp (supportRadius K hc*radius ε t))
    (fun _ => mul_pos hδ (Real.exp_pos _)) 4 (by norm_num)
    (by
      filter_upwards [propagated_rectangle_size hδ (supportRadius K hc)
        (supportRadius_pos K hc).le ε hε hproduct,
        radius_mul_le_half_strong (supportRadius K hc) (supportRadius_pos K hc).le ε hε hproduct]
        with t hsize hr
      have hb : Real.exp (Strong.strongScale t/2)*Real.exp (supportRadius K hc*radius ε t)≤
          Real.exp (Strong.strongScale t) := by
        rw [←Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      apply le_trans _ hsize
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact add_le_add le_rfl (pow_le_pow_left₀ (by positivity) hb 2))
    ε hε hproduct
  exact ⟨E,hE,henergy⟩

#print axioms cutoffSeed_gradient
#print axioms cutoff_propagation_energy
end QuantitativeMaass.Scheduled
