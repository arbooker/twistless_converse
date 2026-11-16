module

public import QuantitativeArithmeticMaassScheduledFluxBoundsV1

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

/-- Difference of the actual localized LV trace and its finite principal
cuspidal spectral compression. The LV degree can vary independently. -/
def supportedCutoffTraceDifference {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ D : ℝ) (hδ : 0<δ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (ε : ℝ→ℝ) (T : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N) (G t : ℝ) : ℝ :=
  let L := Real.exp (G*Strong.strongScale t)
  let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
  letI : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
    N hN basis e he hgraph _ _
  let A := cutoffTransfer N δ D t hδ
  let c := fun z => cylinderAutomorphic (column K hc hKe ε t z)
  let w := fun z => ((W.starProjection
    ((localCuspidalSpace N hN).orthogonalProjectionOnto (A (c z))) : localCuspidalSpace N hN) : AutomorphicSpace N)
  let V := T t
  columnLinearTrace (quotientMeasure 0) (fun z => A (c z)) V-
    columnLinearTrace (quotientMeasure 0) w V


def lvCutoffTraceDifference {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ D : ℝ) (hδ : 0<δ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (ε : ℝ→ℝ) (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N)
    (Ap Bp : ℤ) (hAB : (p:ℤ)*Ap+(N:ℤ)*Bp=1) (degree : ℝ→ℕ) (G t : ℝ) : ℝ :=
  let L := Real.exp (G*Strong.strongScale t)
  let W := cuspPrincipalWindowSpace N hN basis e (t-(L+3)) (t+(L+3))
  letI : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional
    N hN basis e he hgraph _ _
  let A := cutoffTransfer N δ D t hδ
  let c := fun z => cylinderAutomorphic (column K hc hKe ε t z)
  let w := fun z => ((W.starProjection
    ((localCuspidalSpace N hN).orthogonalProjectionOnto (A (c z))) : localCuspidalSpace N hN) : AutomorphicSpace N)
  let V := actualLVFilter N p hN hpN Ap Bp hAB (degree t)
  columnLinearTrace (quotientMeasure 0) (fun z => A (c z)) V-
    columnLinearTrace (quotientMeasure 0) w V


theorem supported_cutoff_trace_bound {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ D : ℝ) (hδ : 0<δ) (hD : 0≤D) (K : SchwartzMap ℝ ℝ)
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
      |supportedCutoffTraceDifference N hN basis e he hgraph δ D hδ K hc hKe ε T G t|≤
        (t*ε t)*(η*Real.exp (A*Strong.strongScale t)+
          (1+η⁻¹)*18*Real.exp ((A-2*G)*Strong.strongScale t)) := by
  obtain ⟨E,hE,henergy⟩ := cutoff_propagation_energy K hc hKe hK hm hδ ε hε hproduct
  let Z := 2*D+40
  refine ⟨Z+E,by dsimp [Z]; positivity,?_⟩
  filter_upwards [henergy,cutoff_flux_coefficients N hδ D hD,
    cutoffSeed_gradient hδ D,hε,eventually_ge_atTop (1:ℝ),hT,hPT,hTP] with t henergy hcoeff hgrad heps ht hTt hPTt hTPt
  intro G η hη hgap
  let L := Real.exp (G*Strong.strongScale t)
  let R := supportRadius K hc*radius ε t
  let Ω := upperRectangle 0 1 (δ*Real.exp (-R)) (Real.exp (Strong.strongScale t/2)*Real.exp R)
  let Src := ∫ z in Ω,‖column K hc hKe ε t z‖^2
  let Res := ∫ z in Ω,‖residualColumn K hc hKe ε t z‖^2
  let m := cutoffMultiplicity δ t
  let C := Real.exp ((D+2)*Strong.strongScale t)
  let a := 2*Real.sqrt (m:ℝ)*|C| *Real.sqrt (m:ℝ)
  let b0 := Real.sqrt (m:ℝ)*1*Real.sqrt (m:ℝ)
  have hSrc : 0≤Src := integral_nonneg (fun _ => sq_nonneg _)
  have hRes : 0≤Res := integral_nonneg (fun _ => sq_nonneg _)
  have hsource : Src≤t*ε t*Real.exp (E*Strong.strongScale t) := henergy.1
  have hresid : Res≤t^3*ε t*Real.exp (E*Strong.strongScale t) := henergy.2
  have hA : ‖cutoffTransfer N δ D t hδ‖^2≤Real.exp (Z*Strong.strongScale t) := hcoeff.1
  have ha : a^2≤Real.exp (Z*Strong.strongScale t) := hcoeff.2.1
  have hb0 : b0^2≤Real.exp (Z*Strong.strongScale t) := hcoeff.2.2
  have hflux := window_flux_cost t (ε t) Src Res a b0
    (Real.exp (Z*Strong.strongScale t)) (Real.exp (E*Strong.strongScale t))
    ht heps.1.le hSrc hRes (Real.exp_pos _).le (Real.exp_pos _).le ha hb0 hsource hresid
  have hraw := cylinderTimeColumn_supported_global_window_error N hN (cutoffSeed δ D t hδ)
    (cutoffRectangle δ t) (upperRectangle_compact 0 1 δ _ hδ) (cutoffSeed_support δ D t hδ)
    m m (cutoff_overlap N δ t hδ) (cutoff_overlap 0 δ t hδ) 1 C (by norm_num)
    (fun z _ => cutoffSeed_bound δ D t hδ z) hgrad (cutoffSeed_real δ D t hδ)
    basis e he hgraph (time K hc ε t) (time_compact K hc ε t) (time_even K hc hKe ε t)
    R (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t)
    t L (Real.exp_pos _) hgap δ (Real.exp (Strong.strongScale t/2)) hδ
    (fun _ hz => hz.2) (T t) hTt hPTt hTPt η hη
  simp only [cylinderAutomorphic.norm_map] at hraw
  change |supportedCutoffTraceDifference N hN basis e he hgraph δ D hδ K hc hKe ε T G t|≤
    η*(‖cutoffTransfer N δ D t hδ‖^2*Src)+
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


theorem supported_cutoff_spectral_compression {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ D : ℝ) (hδ : 0<δ) (hD : 0≤D) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (T : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (hT : ∀ᶠ t in atTop,‖T t‖≤1)
    (hPT : ∀ᶠ t in atTop,(localCuspidalSpace N hN).starProjection*T t=T t)
    (hTP : ∀ᶠ t in atTop,T t*(localCuspidalSpace N hN).starProjection=T t) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      supportedCutoffTraceDifference N hN basis e he hgraph δ D hδ K hc hKe ε T G t/
        (t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,hA,hbound⟩ := supported_cutoff_trace_bound N hN basis e he hgraph δ D hδ hD
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

theorem lv_cutoff_trace_bound {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ D : ℝ) (hδ : 0<δ) (hD : 0≤D) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (hpres : (p:ZMod N)=1) (Ap Bp : ℤ) (hAB : (p:ℤ)*Ap+(N:ℤ)*Bp=1)
    (degree : ℝ→ℕ) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ t in atTop,∀ G η : ℝ,0<η →
      Real.exp (G*Strong.strongScale t)+3≤t →
      |lvCutoffTraceDifference N hN basis e he hgraph δ D hδ K hc hKe ε p hpN Ap Bp hAB degree G t|≤
        (t*ε t)*(η*Real.exp (A*Strong.strongScale t)+
          (1+η⁻¹)*18*Real.exp ((A-2*G)*Strong.strongScale t)) := by
  exact supported_cutoff_trace_bound N hN basis e he hgraph δ D hδ hD K hc hKe hK hm ε hε hproduct
    (fun t => actualLVFilter N p hN hpN Ap Bp hAB (degree t))
    (Eventually.of_forall (fun t => (actualLVFilter_order N p hN hpN Ap Bp hAB (degree t)).2.2))
    (Eventually.of_forall (fun t => localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres Ap Bp hAB (degree t)))
    (Eventually.of_forall (fun t => actualLVFilter_localCuspidalProjection N p hN hpN hNp hpres Ap Bp hAB (degree t)))

theorem lv_cutoff_spectral_compression {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ D : ℝ) (hδ : 0<δ) (hD : 0≤D) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (hpres : (p:ZMod N)=1) (Ap Bp : ℤ) (hAB : (p:ℤ)*Ap+(N:ℤ)*Bp=1)
    (degree : ℝ→ℕ) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      lvCutoffTraceDifference N hN basis e he hgraph δ D hδ K hc hKe ε p hpN Ap Bp hAB degree G t/
        (t*ε t)) atTop (𝓝 0) := by
  exact supported_cutoff_spectral_compression N hN basis e he hgraph δ D hδ hD K hc hKe hK hm ε hε hproduct
    (fun t => actualLVFilter N p hN hpN Ap Bp hAB (degree t))
    (Eventually.of_forall (fun t => (actualLVFilter_order N p hN hpN Ap Bp hAB (degree t)).2.2))
    (Eventually.of_forall (fun t => localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres Ap Bp hAB (degree t)))
    (Eventually.of_forall (fun t => actualLVFilter_localCuspidalProjection N p hN hpN hNp hpres Ap Bp hAB (degree t))) W

#print axioms supported_cutoff_spectral_compression
#print axioms lv_cutoff_trace_bound
#print axioms lv_cutoff_spectral_compression
end QuantitativeMaass.Scheduled
