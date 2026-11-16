module

public import QuantitativeArithmeticMaassScheduledCutoffGeometryV1
public import QuantitativeArithmeticMaassLVGlobalWindowV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

def cutoffMultiplicity (δ t : ℝ) : ℕ :=
  (2*⌈(2+(Real.exp (Strong.strongScale t/2))^2)/δ⌉₊+1)^4

theorem cutoff_overlap (N : ℕ) (δ t : ℝ) (hδ : 0<δ)
    (z : ℍ) (S : Finset (gamma N))
    (hS : ∀ g∈S,g•z∈cutoffRectangle δ t) : S.card≤cutoffMultiplicity δ t :=
  rectangle_overlap_bound N δ _ hδ z S hS

def cutoffTransfer (N : ℕ) (δ D t : ℝ) (hδ : 0<δ) :
    AutomorphicSpace 0→L[ℂ]AutomorphicSpace N :=
  crossQuotientLocalization N 0 (cutoffRectangle δ t)
    (upperRectangle_compact 0 1 δ _ hδ) (cutoffSeed δ D t hδ)
    (fun z _ => cutoffSeed_bound δ D t hδ z)

theorem cutoffTransfer_norm_sq (N : ℕ) (δ D t : ℝ) (hδ : 0<δ) :
    ‖cutoffTransfer N δ D t hδ‖^2≤(cutoffMultiplicity δ t:ℝ)^2 := by
  have hn := crossQuotientLocalization_norm_le_of_overlap N 0 (cutoffRectangle δ t)
    (upperRectangle_compact 0 1 δ _ hδ) (cutoffSeed δ D t hδ)
    (cutoffMultiplicity δ t) (cutoffMultiplicity δ t)
    (cutoff_overlap N δ t hδ) (cutoff_overlap 0 δ t hδ) 1 (by norm_num)
    (fun z _ => cutoffSeed_bound δ D t hδ z)
  rw [mul_one,←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)] at hn
  exact pow_le_pow_left₀ (norm_nonneg (cutoffTransfer N δ D t hδ)) hn 2

/-- Orbit multiplicity grows at most exponentially on the chosen cutoff
family, uniformly for both the modular quotient and the cylinder. -/
theorem cutoffMultiplicity_square_bound {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ t in atTop,(cutoffMultiplicity δ t:ℝ)^2≤Real.exp (33*Strong.strongScale t) := by
  have hsize := propagated_rectangle_size hδ 0 (by norm_num) (fun _ => 1)
    (Eventually.of_forall (fun _ => by norm_num)) (by simpa using slowScale_tendsto)
  filter_upwards [hsize,(Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
    (eventually_ge_atTop ((5:ℝ)^8))] with t hsize he
  simp only [zero_mul,neg_zero,Real.exp_zero,mul_one] at hsize
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  have hb : Real.exp (Strong.strongScale t/2)≤Real.exp (Strong.strongScale t) :=
    Real.exp_le_exp.mpr (by linarith)
  have hx : (2+(Real.exp (Strong.strongScale t/2))^2)/δ≤Real.exp (4*Strong.strongScale t) :=
    (div_le_div_of_nonneg_right (add_le_add le_rfl (pow_le_pow_left₀ (Real.exp_pos _).le hb 2)) hδ.le).trans hsize
  have h1 : 1≤Real.exp (4*Strong.strongScale t) := Real.one_le_exp (by positivity)
  have hceil := Nat.ceil_lt_add_one
    (show 0≤(2+(Real.exp (Strong.strongScale t/2))^2)/δ by positivity)
  have hh : 2*(⌈(2+(Real.exp (Strong.strongScale t/2))^2)/δ⌉₊:ℝ)+1≤
      5*Real.exp (4*Strong.strongScale t) := by linarith
  calc
    _ = (2*(⌈(2+(Real.exp (Strong.strongScale t/2))^2)/δ⌉₊:ℝ)+1)^8 := by
      norm_num [cutoffMultiplicity,←pow_mul]
    _ ≤ (5*Real.exp (4*Strong.strongScale t))^8 := pow_le_pow_left₀ (by positivity) hh 8
    _ ≤ Real.exp (Strong.strongScale t)*(Real.exp (4*Strong.strongScale t))^8 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by
      rw [←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      norm_num
      ring

/-- All three coefficients in the cross-quotient flux inequality have a
common explicit exponential bound. -/
theorem cutoff_flux_coefficients (N : ℕ) {δ : ℝ} (hδ : 0<δ) (D : ℝ) (hD : 0≤D) :
    ∀ᶠ t in atTop,
      let m := (cutoffMultiplicity δ t:ℝ)
      let C := Real.exp ((D+2)*Strong.strongScale t)
      ‖cutoffTransfer N δ D t hδ‖^2≤Real.exp ((2*D+40)*Strong.strongScale t) ∧
      (2*Real.sqrt m*|C| *Real.sqrt m)^2≤Real.exp ((2*D+40)*Strong.strongScale t) ∧
      (Real.sqrt m*1*Real.sqrt m)^2≤Real.exp ((2*D+40)*Strong.strongScale t) := by
  filter_upwards [cutoffMultiplicity_square_bound hδ,
    (Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
      (eventually_ge_atTop (4:ℝ))] with t hm h4
  dsimp only
  change 4≤Real.exp (Strong.strongScale t) at h4
  have hs : 0≤Strong.strongScale t := sq_nonneg _
  have hsmall : Real.exp (33*Strong.strongScale t)≤Real.exp ((2*D+40)*Strong.strongScale t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hD hs]
  refine ⟨(cutoffTransfer_norm_sq N δ D t hδ).trans (hm.trans hsmall),?_,?_⟩
  · rw [abs_of_pos (Real.exp_pos _)]
    have hid : (2*Real.sqrt (cutoffMultiplicity δ t:ℝ)*Real.exp ((D+2)*Strong.strongScale t)*
        Real.sqrt (cutoffMultiplicity δ t:ℝ))^2=
        4*(cutoffMultiplicity δ t:ℝ)^2*(Real.exp ((D+2)*Strong.strongScale t))^2 := by
      calc
        _ = 4*((Real.sqrt (cutoffMultiplicity δ t:ℝ))^2)^2*
            (Real.exp ((D+2)*Strong.strongScale t))^2 := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hid]
    calc
      _ ≤ Real.exp (Strong.strongScale t)*Real.exp (33*Strong.strongScale t)*
          (Real.exp ((D+2)*Strong.strongScale t))^2 := by gcongr
      _ = Real.exp ((2*D+38)*Strong.strongScale t) := by
        rw [pow_two,←Real.exp_add,←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · rw [mul_one,←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hm.trans hsmall

/-- The residual t^3 cost loses exactly t^2 against the spectral denominator.
This is the algebraic estimate used on the actual integrated flux bound. -/
theorem window_flux_cost (t ε S R a b G M : ℝ)
    (ht : 1≤t) (hε : 0≤ε) (hS : 0≤S) (hR : 0≤R) (hG : 0≤G) (hM : 0≤M)
    (ha : a^2≤G) (hb : b^2≤G) (hsource : S≤t*ε*M) (hresid : R≤t^3*ε*M) :
    5*a^2*S+(2*a^2+2*b^2)*R/(1+(t^2+1/4))≤9*t*ε*G*M := by
  have ht0 : 0≤t := by linarith
  have hden : 0<1+(t^2+1/4) := by positivity
  have hr : R/(1+(t^2+1/4))≤t*ε*M := by
    apply (div_le_iff₀ hden).mpr
    apply hresid.trans
    calc
      t^3*ε*M = (t*ε*M)*t^2 := by ring
      _ ≤ (t*ε*M)*(1+(t^2+1/4)) := by gcongr; linarith
  rw [mul_div_assoc]
  calc
    _ ≤ 5*G*(t*ε*M)+(4*G)*(t*ε*M) := by
      apply add_le_add
      · gcongr
      · exact mul_le_mul (by linarith) hr (div_nonneg hR hden.le) (by positivity)
    _ = _ := by ring

/-- An explicit gap and Young parameter make the normalized weighted
spectral compression error exponentially small. -/
theorem young_gap_cost (s A W : ℝ) (hs : 0≤s) (hA : 0≤A) :
    let Q := |W|+A+1
    let D := |W|+A+4
    Real.exp (W*s)*(Real.exp (-(Q*s))*Real.exp (A*s)+
      (1+(Real.exp (-(Q*s)))⁻¹)*18*Real.exp ((A-2*D)*s))≤37*Real.exp (-s) := by
  intro Q D
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hi : (Real.exp (-(Q*s)))⁻¹=Real.exp (Q*s) := by rw [Real.exp_neg,inv_inv]
  rw [hi,mul_add]
  have hfirst : Real.exp (W*s)*(Real.exp (-(Q*s))*Real.exp (A*s))≤Real.exp (-s) := by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [Q]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self W)) hs]
  have hsecond : Real.exp (W*s)*((1+Real.exp (Q*s))*18*Real.exp ((A-2*D)*s))≤
      36*Real.exp (-s) := by
    have h1 : 1≤Real.exp (Q*s) := Real.one_le_exp (mul_nonneg hQ hs)
    calc
      _ ≤ Real.exp (W*s)*((2*Real.exp (Q*s))*18*Real.exp ((A-2*D)*s)) := by gcongr; linarith
      _ = 36*Real.exp ((W+Q+A-2*D)*s) := by
        rw [show (W+Q+A-2*D)*s=W*s+Q*s+(A-2*D)*s by ring,Real.exp_add,Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        dsimp [Q,D]
        nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self W)) hs]
  linarith

#print axioms cutoff_flux_coefficients
#print axioms window_flux_cost
#print axioms young_gap_cost
end QuantitativeMaass.Scheduled
