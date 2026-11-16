module

public import QuantitativeArithmeticMaassMovingFluxBoundsV1
public import QuantitativeArithmeticMaassScheduledLVCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-! Spectral compression with the concrete moving lower cutoff. -/

theorem moving_supported_cutoff_trace_bound {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ C D : ℝ) (hδ : 0<δ) (hC : 0≤C) (hD : 0≤D) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (T : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (hT : ∀ᶠ t in atTop,‖T t‖≤1)
    (hPT : ∀ᶠ t in atTop,(localCuspidalSpace N hN).starProjection*T t=T t)
    (hTP : ∀ᶠ t in atTop,T t*(localCuspidalSpace N hN).starProjection=T t) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ t in atTop,∀ G η : ℝ,0<η →
      Real.exp (G*Strong.strongScale t)+3≤t →
      |supportedCutoffTraceDifference N hN basis e he hgraph (movingLowerEdge δ C ε t) D (movingLowerEdge_pos hδ C ε t) K hc hKe ε T G t|≤
        (t*ε t)*(η*Real.exp (A*Strong.strongScale t)+
          (1+η⁻¹)*18*Real.exp ((A-2*G)*Strong.strongScale t)) := by
  obtain ⟨E,hE,henergy⟩ := movingCutoff_propagation_energy K hc hKe hK hm hδ C hC ε hε hproduct
  let Z := 2*D+40
  refine ⟨Z+E,by dsimp [Z]; positivity,?_⟩
  filter_upwards [henergy,movingCutoff_flux_coefficients N hδ C D hC hD ε hε hproduct,
    movingCutoffSeed_gradient hδ C D ε,hε,eventually_ge_atTop (1:ℝ),hT,hPT,hTP] with t henergy hcoeff hgrad heps ht hTt hPTt hTPt
  intro G η hη hgap
  let a₀ := movingLowerEdge δ C ε t
  have ha₀ := movingLowerEdge_pos hδ C ε t
  let L := Real.exp (G*Strong.strongScale t)
  let R := supportRadius K hc*radius ε t
  let Ω := upperRectangle 0 1 (a₀*Real.exp (-R)) (Real.exp (Strong.strongScale t/2)*Real.exp R)
  let Src := ∫ z in Ω,‖column K hc hKe ε t z‖^2
  let Res := ∫ z in Ω,‖residualColumn K hc hKe ε t z‖^2
  let m := movingMultiplicity δ C ε t
  let Cgrad := Real.exp ((D+2)*Strong.strongScale t)
  let a := 2*Real.sqrt (m:ℝ)*|Cgrad| *Real.sqrt (m:ℝ)
  let b0 := Real.sqrt (m:ℝ)*1*Real.sqrt (m:ℝ)
  have hSrc : 0≤Src := integral_nonneg (fun _ => sq_nonneg _)
  have hRes : 0≤Res := integral_nonneg (fun _ => sq_nonneg _)
  have hsource : Src≤t*ε t*Real.exp (E*Strong.strongScale t) := henergy.1
  have hresid : Res≤t^3*ε t*Real.exp (E*Strong.strongScale t) := henergy.2
  have hA : ‖cutoffTransfer N a₀ D t ha₀‖^2≤Real.exp (Z*Strong.strongScale t) := hcoeff.1
  have ha : a^2≤Real.exp (Z*Strong.strongScale t) := hcoeff.2.1
  have hb0 : b0^2≤Real.exp (Z*Strong.strongScale t) := hcoeff.2.2
  have hflux := window_flux_cost t (ε t) Src Res a b0
    (Real.exp (Z*Strong.strongScale t)) (Real.exp (E*Strong.strongScale t))
    ht heps.1.le hSrc hRes (Real.exp_pos _).le (Real.exp_pos _).le ha hb0 hsource hresid
  have hraw := cylinderTimeColumn_supported_global_window_error N hN (cutoffSeed a₀ D t ha₀)
    (cutoffRectangle a₀ t) (upperRectangle_compact 0 1 a₀ _ ha₀) (cutoffSeed_support a₀ D t ha₀)
    m m (movingCutoff_overlap N hδ C ε t) (movingCutoff_overlap 0 hδ C ε t) 1 Cgrad (by norm_num)
    (fun z _ => cutoffSeed_bound a₀ D t ha₀ z) hgrad (cutoffSeed_real a₀ D t ha₀)
    basis e he hgraph (time K hc ε t) (time_compact K hc ε t) (time_even K hc hKe ε t)
    R (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t)
    t L (Real.exp_pos _) hgap a₀ (Real.exp (Strong.strongScale t/2)) ha₀
    (fun _ hz => hz.2) (T t) hTt hPTt hTPt η hη
  simp only [cylinderAutomorphic.norm_map] at hraw
  change |supportedCutoffTraceDifference N hN basis e he hgraph (movingLowerEdge δ C ε t) D (movingLowerEdge_pos hδ C ε t) K hc hKe ε T G t|≤
    η*(‖cutoffTransfer N a₀ D t ha₀‖^2*Src)+
      (1+η⁻¹)*((2/L^2)*(5*a^2*Src+(2*a^2+2*b0^2)*Res/(1+(t^2+1/4)))) at hraw
  apply hraw.trans
  calc
    _ ≤ η*(Real.exp (Z*Strong.strongScale t)*(t*ε t*Real.exp (E*Strong.strongScale t)))+
        (1+η⁻¹)*((2/L^2)*(9*t*ε t*Real.exp (Z*Strong.strongScale t)*Real.exp (E*Strong.strongScale t))) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hη.le
        exact mul_le_mul hA hsource hSrc (Real.exp_pos _).le
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hflux (by positivity)
    _ = _ := by
      have hexp : Real.exp ((Z+E)*Strong.strongScale t)=
          Real.exp (Z*Strong.strongScale t)*Real.exp (E*Strong.strongScale t) := by
        rw [←Real.exp_add]; congr 1; ring
      have hratio : Real.exp ((Z+E-2*G)*Strong.strongScale t)=
          Real.exp ((Z+E)*Strong.strongScale t)/L^2 := by
        dsimp [L]
        rw [show (Z+E-2*G)*Strong.strongScale t=(Z+E)*Strong.strongScale t-
          ((G*Strong.strongScale t)+(G*Strong.strongScale t)) by ring,Real.exp_sub,Real.exp_add,pow_two]
      rw [hratio,hexp]
      ring


theorem moving_supported_cutoff_spectral_compression {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ C D : ℝ) (hδ : 0<δ) (hC : 0≤C) (hD : 0≤D) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (T : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (hT : ∀ᶠ t in atTop,‖T t‖≤1)
    (hPT : ∀ᶠ t in atTop,(localCuspidalSpace N hN).starProjection*T t=T t)
    (hTP : ∀ᶠ t in atTop,T t*(localCuspidalSpace N hN).starProjection=T t) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      supportedCutoffTraceDifference N hN basis e he hgraph (movingLowerEdge δ C ε t) D (movingLowerEdge_pos hδ C ε t) K hc hKe ε T G t/
        (t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,hA,hbound⟩ := moving_supported_cutoff_trace_bound N hN basis e he hgraph δ C D hδ hC hD
    K hc hKe hK hm ε hε hproduct T hT hPT hTP
  let G := |W|+A+4
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨G,hG,?_⟩
  have hlim : Tendsto (fun t => 37*Real.exp (-Strong.strongScale t)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp Strong.strongScale_tendsto)).const_mul (37:ℝ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hbound,hε,Strong.exponential_band_width_quarter G hG.le,
    eventually_ge_atTop (6:ℝ)] with t hb heps hwidth ht
  have ht0 : 0<t := by linarith
  have hden : 0<t*ε t := mul_pos ht0 heps.1
  let Q := |W|+A+1
  let η := Real.exp (-(Q*Strong.strongScale t))
  have hh := hb G η (Real.exp_pos _) (by linarith [hwidth.2])
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos hden]
  calc
    _ ≤ Real.exp (W*Strong.strongScale t)*((t*ε t)*(η*Real.exp (A*Strong.strongScale t)+
        (1+η⁻¹)*18*Real.exp ((A-2*G)*Strong.strongScale t)))/(t*ε t) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le) hden.le
    _ = Real.exp (W*Strong.strongScale t)*(η*Real.exp (A*Strong.strongScale t)+
        (1+η⁻¹)*18*Real.exp ((A-2*G)*Strong.strongScale t)) := by
      field_simp [ne_of_gt ht0,ne_of_gt heps.1]
    _ ≤ _ := young_gap_cost (Strong.strongScale t) A W (sq_nonneg _) hA.le

#print axioms moving_supported_cutoff_trace_bound
#print axioms moving_supported_cutoff_spectral_compression
end QuantitativeMaass.Scheduled
