module

public import QuantitativeArithmeticMaassScheduledBroadErrorV1
public import QuantitativeArithmeticMaassMovingFluxBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- Full-cylinder approximation with the actual moving lower cutoff.
The Laplacian estimate is uniform in that edge; overlap and propagation
costs use their proved moving-region bounds. -/
theorem movingBroad_approximation_bound (N : ℕ) (δ P D : ℝ) (hδ : 0<δ) (hP : 0≤P) (hD : 0≤D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ t in atTop,∀ G : ℝ,0≤G →
      broadCutoffError N (movingLowerEdge δ P ε t) D (movingLowerEdge_pos hδ P ε t) K hc he ε G t≤
        (72*(2*Real.cosh (1/2))^2)*(t*ε t)*Real.exp ((A-2*G)*Strong.strongScale t) := by
  obtain ⟨E,hE,henergy⟩ := movingCutoff_propagation_energy K hc he hK hm hδ P hP ε hε hproduct
  have hmultsq : ∀ᶠ t in atTop, (movingMultiplicity δ P ε t:ℝ)^2 ≤
      Real.exp (34*Strong.strongScale t) := by
    filter_upwards [movingMultiplicity_bound hδ P hP ε hε hproduct] with t ht
    calc
      _ ≤ (Real.exp (17*Strong.strongScale t))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) ht 2
      _ = _ := by rw [pow_two,←Real.exp_add]; congr 1; ring
  let Z := 4*D+4
  refine ⟨34+Z+E,by dsimp [Z]; positivity,?_⟩
  filter_upwards [henergy,hmultsq,
    movingCutoffSeed_gradient hδ P D ε,cutoffSeed_laplacian D,hε,eventually_ge_atTop (1:ℝ)]
    with t henergy hmult hgrad hlap heps ht
  intro G hG
  have ht0 : 0<t := by linarith
  have heps0 : 0≤ε t := heps.1.le
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  let L := Real.exp (G*Strong.strongScale t)
  let R := supportRadius K hc*radius ε t
  let Ω := upperRectangle 0 1 (movingLowerEdge δ P ε t*Real.exp (-R))
    (Real.exp (Strong.strongScale t/2)*Real.exp R)
  let Src := ∫ z in Ω,‖column K hc he ε t z‖^2
  let Res := ∫ z in Ω,‖residualColumn K hc he ε t z‖^2
  let C := Real.exp ((D+2)*Strong.strongScale t)
  let H := Real.exp ((2*D+2)*Strong.strongScale t)
  let B := Real.exp (Z*Strong.strongScale t)
  let M := Real.exp (E*Strong.strongScale t)
  let m := (movingMultiplicity δ P ε t:ℝ)
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
  have hraw := broadPacket_cross_cylinder_energy N (cutoffSeed (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t))
    (cutoffSeed_real (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t)) (cutoffRectangle (movingLowerEdge δ P ε t) t)
    (upperRectangle_compact 0 1 (movingLowerEdge δ P ε t) _ (movingLowerEdge_pos hδ P ε t)) (cutoffSeed_support (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t))
    (movingMultiplicity δ P ε t) (movingMultiplicity δ P ε t)
    (movingCutoff_overlap N hδ P ε t) (movingCutoff_overlap 0 hδ P ε t) 1 H C (by norm_num)
    (Real.exp_pos _).le (fun z _ => cutoffSeed_bound (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) z)
    (fun z _ => hlap (movingLowerEdge δ P ε t) (movingLowerEdge_pos hδ P ε t) z) hgrad t L ht0 hL
    (time K hc ε t) (time_compact K hc ε t) (time_even K hc he ε t)
    R (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t)
    Ω (upperRectangle_compact 0 1 _ _ (mul_pos (movingLowerEdge_pos hδ P ε t) (Real.exp_pos _)))
  change broadCutoffError N (movingLowerEdge δ P ε t) D (movingLowerEdge_pos hδ P ε t) K hc he ε G t≤
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
        (3*Real.exp (34*Strong.strongScale t))*(24*t^3*ε t*B*M) := by
      rw [div_pow]
      have hm2 : 3*m*m≤3*Real.exp (34*Strong.strongScale t) := by nlinarith [hmult]
      gcongr
    _ = _ := by
      have hratio : Real.exp ((34+Z+E-2*G)*Strong.strongScale t)=
          Real.exp (34*Strong.strongScale t)*B*M/L^2 := by
        dsimp [B,M,L]
        rw [show (34+Z+E-2*G)*Strong.strongScale t=
          (34*Strong.strongScale t+Z*Strong.strongScale t+E*Strong.strongScale t)-
          (G*Strong.strongScale t+G*Strong.strongScale t) by ring,
          Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_add]
        ring
      rw [hratio]
      field_simp [ne_of_gt ht0,ne_of_gt hL]
      ring

/-- Any prescribed fixed exponential weight is absorbed by choosing one
sufficiently broad full-quotient packet. -/
theorem movingBroad_approximation_decay (N : ℕ) (δ P D : ℝ) (hδ : 0<δ) (hP : 0≤P) (hD : 0≤D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      broadCutoffError N (movingLowerEdge δ P ε t) D (movingLowerEdge_pos hδ P ε t) K hc he ε G t/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,hA,hbound⟩ := movingBroad_approximation_bound N δ P D hδ hP hD K hc he hK hm ε hε hproduct
  let G := |W|+A+1
  let C := 72*(2*Real.cosh (1/2))^2
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨G,hG,?_⟩
  have hlim : Tendsto (fun t => C*Real.exp (-Strong.strongScale t)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp Strong.strongScale_tendsto)).const_mul C
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    have herror : 0≤broadCutoffError N (movingLowerEdge δ P ε t) D (movingLowerEdge_pos hδ P ε t) K hc he ε G t := by
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

theorem movingBroad_global_approximation_decay (N : ℕ) (δ P D : ℝ) (hδ : 0<δ) (hP : 0≤P) (hD : 0≤D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z, ‖broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t
        (cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z)))-
        cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z))‖^2
          ∂quotientMeasure 0)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨G,hG,hlim⟩ := movingBroad_approximation_decay N δ P D hδ hP hD K hc he hK hm ε hε hproduct W
  exact ⟨G,hG,by simpa only [broadCutoffError_eq_global] using hlim⟩


#print axioms movingBroad_approximation_bound
#print axioms movingBroad_approximation_decay
#print axioms movingBroad_global_approximation_decay
end QuantitativeMaass.Scheduled
