module

public import QuantitativeArithmeticMaassMovingSpectralCompressionV1

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

/-- Adjust the spectral gap so its fixed buffer yields precisely the
exponential window used by the finite-band filter theorems. -/
def exactBandParameter (B t : ℝ) : ℝ :=
  Real.log (Real.exp (B*Strong.strongScale t)-3)/Strong.strongScale t

theorem exactBandParameter_eventually (G : ℝ) (hG : 0≤G) :
    ∀ᶠ t in atTop,G≤exactBandParameter (G+1) t ∧
      Real.exp (exactBandParameter (G+1) t*Strong.strongScale t)+3=
        Real.exp ((G+1)*Strong.strongScale t) := by
  filter_upwards [Strong.strongScale_tendsto.eventually (eventually_ge_atTop (Real.log 4+1))]
    with t ht
  have hs : 0<Strong.strongScale t := by
    have : 0≤Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have h4 : (4:ℝ)≤Real.exp (Strong.strongScale t) := by
    calc
      _=Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _≤_ := Real.exp_le_exp.mpr (by linarith)
  have h1 : 1≤Real.exp (G*Strong.strongScale t) := Real.one_le_exp (mul_nonneg hG hs.le)
  have hex : Real.exp (G*Strong.strongScale t)+3≤Real.exp ((G+1)*Strong.strongScale t) := by
    rw [add_mul,one_mul,Real.exp_add]
    nlinarith
  have hpos : 0<Real.exp ((G+1)*Strong.strongScale t)-3 := by
    linarith [Real.exp_pos (G*Strong.strongScale t)]
  constructor
  · apply (le_div_iff₀ hs).mpr
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log hpos]
    linarith
  · rw [exactBandParameter,div_mul_cancel₀ _ (ne_of_gt hs),Real.exp_log hpos]
    ring

theorem moving_supported_cutoff_exact_band_compression {ι : Type*} (N : ℕ) (hN : 0<N)
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
      supportedCutoffTraceDifference N hN basis e he hgraph (movingLowerEdge δ C ε t) D (movingLowerEdge_pos hδ C ε t) K hc hKe ε T (exactBandParameter G t) t/
        (t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,hA,hbound⟩ := moving_supported_cutoff_trace_bound N hN basis e he hgraph δ C D hδ hC hD
    K hc hKe hK hm ε hε hproduct T hT hPT hTP
  let G := |W|+A+4
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨G+1,by positivity,?_⟩
  have hlim : Tendsto (fun t => 37*Real.exp (-Strong.strongScale t)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp Strong.strongScale_tendsto)).const_mul (37:ℝ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hbound,hε,Strong.exponential_band_width_quarter (G+1) (by positivity),
    exactBandParameter_eventually G hG.le,
    eventually_ge_atTop (6:ℝ)] with t hb heps hwidth hparam ht
  have ht0 : 0<t := by linarith
  have hden : 0<t*ε t := mul_pos ht0 heps.1
  let Q := |W|+A+1
  let η := Real.exp (-(Q*Strong.strongScale t))
  have hh0 := hb (exactBandParameter (G+1) t) η (Real.exp_pos _)
    (by rw [hparam.2]; linarith [hwidth.2])
  have hexp : Real.exp ((A-2*exactBandParameter (G+1) t)*Strong.strongScale t)≤
      Real.exp ((A-2*G)*Strong.strongScale t) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith [hparam.1]) (sq_nonneg _)
  have hh := hh0.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (η*Real.exp (A*Strong.strongScale t))) (mul_le_mul_of_nonneg_left hexp (show 0≤(1+η⁻¹)*18 by positivity))) hden.le)
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos hden]
  calc
    _ ≤ Real.exp (W*Strong.strongScale t)*((t*ε t)*(η*Real.exp (A*Strong.strongScale t)+
        (1+η⁻¹)*18*Real.exp ((A-2*G)*Strong.strongScale t)))/(t*ε t) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le) hden.le
    _ = Real.exp (W*Strong.strongScale t)*(η*Real.exp (A*Strong.strongScale t)+
        (1+η⁻¹)*18*Real.exp ((A-2*G)*Strong.strongScale t)) := by
      field_simp [ne_of_gt ht0,ne_of_gt heps.1]
    _ ≤ _ := young_gap_cost (Strong.strongScale t) A W (sq_nonneg _) hA.le

#print axioms exactBandParameter_eventually
#print axioms moving_supported_cutoff_exact_band_compression
end QuantitativeMaass.Scheduled
