module

public import QuantitativeArithmeticMaassBroadCrossEnergyV1
public import QuantitativeArithmeticMaassScheduledFluxBoundsV1
public import QuantitativeArithmeticMaassScheduledCutoffLaplacianV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The source residual has order t^3, exactly compensated by the squared
broad-packet denominator. No derivative of the residual is needed. -/
theorem broad_packet_energy_cost (t ε S R C H B M : ℝ)
    (ht : 1≤t) (_hε : 0≤ε) (hS : 0≤S) (hR : 0≤R)
    (hB : 1≤B) (_hM : 0≤M) (hC : C^2≤B) (hH : H^2≤B)
    (hsource : S≤t*ε*M) (hresid : R≤t^3*ε*M) :
    (1+4*C^2)*R+(H^2+8*C^2*(1+(t^2+1/4)))*S≤24*t^3*ε*B*M := by
  have ht0 : 0≤t := by linarith
  have ht2 : 1≤t^2 := by nlinarith
  have hB0 : 0≤B := by linarith
  have hcoeff : H^2+8*C^2*(1+(t^2+1/4))≤19*B*t^2 := by
    calc
      _ ≤ B+8*B*(1+(t^2+1/4)) := by gcongr
      _ ≤ 19*B*t^2 := by nlinarith [mul_nonneg hB0 (sub_nonneg.mpr ht2)]
  calc
    _ ≤ (5*B)*(t^3*ε*M)+(19*B*t^2)*(t*ε*M) := by
      apply add_le_add
      · exact mul_le_mul (by linarith) hresid hR (by positivity)
      · exact mul_le_mul hcoeff hsource hS (by positivity)
    _ = _ := by ring

/-- Squared broad-packet error for the actual compact transfer, integrated
on the finite-propagation rectangle of the original cylinder packet. -/
def broadCutoffError (N : ℕ) (δ D : ℝ) (hδ : 0<δ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (G t : ℝ) : ℝ :=
  let L := Real.exp (G*Strong.strongScale t)
  let R := supportRadius K hc*radius ε t
  let Ω := upperRectangle 0 1 (δ*Real.exp (-R))
    (Real.exp (Strong.strongScale t/2)*Real.exp R)
  let A := cutoffTransfer N δ D t hδ
  ∫ z in Ω, ‖broadQuotientPacket N L (Real.exp_pos _) t
    (A (cylinderAutomorphic (column K hc he ε t z)))-
      A (cylinderAutomorphic (column K hc he ε t z))‖^2

/-- Finite propagation identifies the compact-region estimate with the
full cylinder integral, even after applying the full-quotient broad packet. -/
theorem broadCutoffError_eq_global (N : ℕ) (δ D : ℝ) (hδ : 0<δ)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (G t : ℝ) :
    broadCutoffError N δ D hδ K hc he ε G t=
      ∫ z, ‖broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t
        (cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z)))-
        cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z))‖^2
          ∂quotientMeasure 0 := by
  let f := time K hc ε t
  let R := supportRadius K hc*radius ε t
  have hR : 0≤R := (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
  let b := cutoffSeed δ D t hδ
  let Q := broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t
  have hbound : ∀ᵐ z ∂volume.restrict (cutoffRectangle δ t),‖upperFunction b.toFun z‖≤1 :=
    Eventually.of_forall (fun z => cutoffSeed_bound δ D t hδ z)
  have hi := boundedCrossQuotientLocalization_column_integral N (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) (time_even K hc he ε t) (time_compact K hc ε t))
    R hR (evenCoshLift_support_of_time_support f R hR (time_support K hc ε t))
    (cutoffRectangle δ t) (upperRectangle_compact 0 1 δ _ hδ)
    δ (Real.exp (Strong.strongScale t/2)) hδ (fun _ hz => hz.2)
    (upperFunction b.toFun) (upperFunction_continuous b.smooth).aestronglyMeasurable
    hbound (fun v => ‖Q v-v‖^2) (by simp)
  exact hi.symm

theorem broad_cutoff_energy_bound (N : ℕ) (δ D : ℝ) (hδ : 0<δ) (hD : 0≤D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ t in atTop,∀ G : ℝ,0≤G →
      broadCutoffError N δ D hδ K hc he ε G t≤
        (72*(2*Real.cosh (1/2))^2)*(t*ε t)*Real.exp ((A-2*G)*Strong.strongScale t) := by
  obtain ⟨E,hE,henergy⟩ := cutoff_propagation_energy K hc he hK hm hδ ε hε hproduct
  let Z := 4*D+4
  refine ⟨33+Z+E,by dsimp [Z]; positivity,?_⟩
  filter_upwards [henergy,cutoffMultiplicity_square_bound hδ,
    cutoffSeed_gradient hδ D,cutoffSeed_laplacian D,hε,eventually_ge_atTop (1:ℝ)]
    with t henergy hmult hgrad hlap heps ht
  intro G hG
  have ht0 : 0<t := by linarith
  have heps0 : 0≤ε t := heps.1.le
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  let L := Real.exp (G*Strong.strongScale t)
  let R := supportRadius K hc*radius ε t
  let Ω := upperRectangle 0 1 (δ*Real.exp (-R))
    (Real.exp (Strong.strongScale t/2)*Real.exp R)
  let Src := ∫ z in Ω,‖column K hc he ε t z‖^2
  let Res := ∫ z in Ω,‖residualColumn K hc he ε t z‖^2
  let C := Real.exp ((D+2)*Strong.strongScale t)
  let H := Real.exp ((2*D+2)*Strong.strongScale t)
  let B := Real.exp (Z*Strong.strongScale t)
  let M := Real.exp (E*Strong.strongScale t)
  let m := (cutoffMultiplicity δ t:ℝ)
  have hL : 0<L := Real.exp_pos _
  have hL1 : 1≤L := Real.one_le_exp (mul_nonneg hG hs)
  have hB : 1≤B := Real.one_le_exp (by dsimp [Z]; positivity)
  have hC : C^2≤B := by
    dsimp [C,B,Z]
    rw [pow_two,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hD hs]
  have hH : H^2≤B := by
    dsimp [H,B,Z]
    rw [pow_two,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    exact le_rfl
  have hcost := broad_packet_energy_cost t (ε t) Src Res C H B M ht heps.1.le
    (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _))
    hB (Real.exp_pos _).le hC hH henergy.1 henergy.2
  have hraw := broadPacket_cross_cylinder_energy N (cutoffSeed δ D t hδ)
    (cutoffSeed_real δ D t hδ) (cutoffRectangle δ t)
    (upperRectangle_compact 0 1 δ _ hδ) (cutoffSeed_support δ D t hδ)
    (cutoffMultiplicity δ t) (cutoffMultiplicity δ t)
    (cutoff_overlap N δ t hδ) (cutoff_overlap 0 δ t hδ) 1 H C (by norm_num)
    (Real.exp_pos _).le (fun z _ => cutoffSeed_bound δ D t hδ z)
    (fun z _ => hlap δ hδ z) hgrad t L ht0 hL
    (time K hc ε t) (time_compact K hc ε t) (time_even K hc he ε t)
    R (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t)
    Ω (upperRectangle_compact 0 1 _ _ (mul_pos hδ (Real.exp_pos _)))
  change broadCutoffError N δ D hδ K hc he ε G t≤
    ((2*Real.cosh ((1/L)/2)/(t*L))^2*(3*m*m))*
      ((1^2+4*C^2)*Res+(H^2+8*C^2*(1+(t^2+1/4)))*Src) at hraw
  simp only [one_pow] at hraw
  have hcosh : Real.cosh ((1/L)/2)≤Real.cosh (1/2) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (by norm_num)]
    have : 1/L≤1 := (div_le_one hL).mpr hL1
    linarith
  have hsq : (2*Real.cosh ((1/L)/2))^2≤(2*Real.cosh (1/2))^2 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 2
  apply hraw.trans
  calc
    _ ≤ ((2*Real.cosh ((1/L)/2)/(t*L))^2*(3*m*m))*(24*t^3*ε t*B*M) :=
      mul_le_mul_of_nonneg_left hcost (by dsimp [m]; positivity)
    _ ≤ ((2*Real.cosh (1/2))^2/(t*L)^2)*
        (3*Real.exp (33*Strong.strongScale t))*(24*t^3*ε t*B*M) := by
      rw [div_pow]
      have hm2 : 3*m*m≤3*Real.exp (33*Strong.strongScale t) := by nlinarith [hmult]
      gcongr
    _ = _ := by
      have hratio : Real.exp ((33+Z+E-2*G)*Strong.strongScale t)=
          Real.exp (33*Strong.strongScale t)*B*M/L^2 := by
        dsimp [B,M,L]
        rw [show (33+Z+E-2*G)*Strong.strongScale t=
          (33*Strong.strongScale t+Z*Strong.strongScale t+E*Strong.strongScale t)-
          (G*Strong.strongScale t+G*Strong.strongScale t) by ring,
          Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_add]
        ring
      rw [hratio]
      field_simp [ne_of_gt ht0,ne_of_gt hL]
      ring

/-- Any prescribed fixed exponential weight is absorbed by choosing one
sufficiently broad full-quotient packet. -/
theorem broad_cutoff_energy_decay (N : ℕ) (δ D : ℝ) (hδ : 0<δ) (hD : 0≤D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      broadCutoffError N δ D hδ K hc he ε G t/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,hA,hbound⟩ := broad_cutoff_energy_bound N δ D hδ hD K hc he hK hm ε hε hproduct
  let G := |W|+A+1
  let C := 72*(2*Real.cosh (1/2))^2
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨G,hG,?_⟩
  have hlim : Tendsto (fun t => C*Real.exp (-Strong.strongScale t)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp Strong.strongScale_tendsto)).const_mul C
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    have herror : 0≤broadCutoffError N δ D hδ K hc he ε G t := by
      dsimp [broadCutoffError]
      exact integral_nonneg (fun _ => sq_nonneg _)
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le herror) (mul_pos ht heps.1).le
  · filter_upwards [hbound,hε,eventually_gt_atTop (0:ℝ)] with t hb heps ht
    have hden : 0<t*ε t := mul_pos ht heps.1
    calc
      _ ≤ Real.exp (W*Strong.strongScale t)*
          (C*(t*ε t)*Real.exp ((A-2*G)*Strong.strongScale t))/(t*ε t) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb G hG.le) (Real.exp_pos _).le) hden.le
      _ = C*Real.exp ((W+A-2*G)*Strong.strongScale t) := by
        rw [show (W+A-2*G)*Strong.strongScale t=
          W*Strong.strongScale t+(A-2*G)*Strong.strongScale t by ring,Real.exp_add]
        field_simp [ne_of_gt hden,ne_of_gt ht,ne_of_gt heps.1]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
        apply Real.exp_le_exp.mpr
        dsimp [G]
        have hs : 0≤Strong.strongScale t := sq_nonneg _
        nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self W)) hs,
          mul_nonneg hA.le hs,mul_nonneg (abs_nonneg W) hs]

theorem broad_cutoff_global_energy_decay (N : ℕ) (δ D : ℝ) (hδ : 0<δ) (hD : 0≤D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z, ‖broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t
        (cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z)))-
        cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z))‖^2
          ∂quotientMeasure 0)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨G,hG,hlim⟩ := broad_cutoff_energy_decay N δ D hδ hD K hc he hK hm ε hε hproduct W
  exact ⟨G,hG,by simpa only [broadCutoffError_eq_global] using hlim⟩

/-- Compact transfer gives a genuinely square-integrable family of columns
on the full cylinder, independently of any spectral asymptotic. -/
theorem broadCutoff_column_memLp (N : ℕ) (δ D : ℝ) (hδ : 0<δ)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) :
    MemLp (fun z => cutoffTransfer N δ D t hδ
      (cylinderAutomorphic (column K hc he ε t z))) 2 (quotientMeasure 0) := by
  let f := time K hc ε t
  let R := supportRadius K hc*radius ε t
  have hR : 0≤R := (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
  let b := cutoffSeed δ D t hδ
  have hbound : ∀ᵐ z ∂volume.restrict (cutoffRectangle δ t),‖upperFunction b.toFun z‖≤1 :=
    Eventually.of_forall (fun z => cutoffSeed_bound δ D t hδ z)
  exact boundedCrossQuotientLocalization_column_memLp N (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) (time_even K hc he ε t) (time_compact K hc ε t))
    R hR (evenCoshLift_support_of_time_support f R hR (time_support K hc ε t))
    (cutoffRectangle δ t) (upperRectangle_compact 0 1 δ _ hδ)
    δ (Real.exp (Strong.strongScale t/2)) hδ (fun _ hz => hz.2)
    (upperFunction b.toFun) (upperFunction_continuous b.smooth).aestronglyMeasurable hbound

theorem broadCutoff_error_memLp (N : ℕ) (δ D : ℝ) (hδ : 0<δ)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (G t : ℝ) :
    MemLp (fun z => broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t
      (cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z)))-
      cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z)))
        2 (quotientMeasure 0) := by
  have h := broadCutoff_column_memLp N δ D hδ K hc he ε t
  exact (h.continuousLinearMap_comp
    (broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t)).sub h

theorem broadCutoff_error_integrable (N : ℕ) (δ D : ℝ) (hδ : 0<δ)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (G t : ℝ) :
    Integrable (fun z => ‖broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t
      (cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z)))-
      cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z))‖^2)
        (quotientMeasure 0) := by
  have h := broadCutoff_error_memLp N δ D hδ K hc he ε G t
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

#print axioms broadCutoff_column_memLp
#print axioms broadCutoff_error_memLp
#print axioms broadCutoff_error_integrable
#print axioms broad_packet_energy_cost
#print axioms broad_cutoff_energy_bound
#print axioms broad_cutoff_energy_decay
#print axioms broadCutoffError_eq_global
#print axioms broad_cutoff_global_energy_decay
end QuantitativeMaass.Scheduled
