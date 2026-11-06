module

public import SmallLevelTaylorDecayV1
public import SmallLevelTaylorContinuityV1
public import Mathlib.Analysis.MellinTransform

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries
open scoped Topology

/-- A smooth positive envelope with a power singularity and an exponential tail. -/
def mellinEnvelope (K : ℕ) (D E κ : ℝ) (y : ℝ) : ℝ :=
  (D/y^K+E)*Real.exp (-κ*y)

theorem mellinEnvelope_nonneg (K : ℕ) {D E κ y : ℝ}
    (hD : 0≤D) (hE : 0≤E) (hy : 0<y) : 0≤mellinEnvelope K D E κ y := by
  unfold mellinEnvelope
  positivity

theorem mellinEnvelope_continuous (K : ℕ) (D E κ : ℝ) :
    ContinuousOn (mellinEnvelope K D E κ) (Ioi 0) := by
  intro y hy
  unfold mellinEnvelope
  fun_prop (disch := exact pow_ne_zero K (ne_of_gt hy))

theorem mellinEnvelope_small (K : ℕ) {D E κ : ℝ}
    (hD : 0≤D) (hE : 0≤E) (hκ : 0<κ) :
    mellinEnvelope K D E κ =O[𝓝[>] 0] (fun y : ℝ => y^(-(K:ℝ))) := by
  apply IsBigO.of_bound (D+E)
  have hsmall : ∀ᶠ y : ℝ in 𝓝[>] 0, y≤1 :=
    ((eventually_lt_nhds (by norm_num : (0:ℝ)<1)).mono (fun _ h => h.le)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hsmall] with y hy hy1
  change 0<y at hy
  have hp : y^K≤1 := pow_le_one₀ hy.le hy1
  have he : Real.exp (-κ*y)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [Real.norm_eq_abs,abs_of_nonneg (mellinEnvelope_nonneg K hD hE hy),
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hy.le _),Real.rpow_neg hy.le,Real.rpow_natCast]
  unfold mellinEnvelope
  calc
    _≤D/y^K+E := mul_le_of_le_one_right (by positivity) he
    _≤(D+E)*(y^K)⁻¹ := by
      have hEinv : E≤E/y^K := (le_div_iff₀ (pow_pos hy K)).mpr (mul_le_of_le_one_right hE hp)
      simp only [div_eq_mul_inv,add_mul] at *
      linarith

theorem mellinEnvelope_rapid (K : ℕ) {D E κ : ℝ}
    (hD : 0≤D) (hE : 0≤E) (hκ : 0<κ) (s : ℝ) :
    mellinEnvelope K D E κ =O[atTop] (fun y : ℝ => y^s) := by
  have h : mellinEnvelope K D E κ =O[atTop] (fun y : ℝ => Real.exp (-κ*y)) := by
    apply IsBigO.of_bound (D+E)
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hy0 : 0<y := lt_of_lt_of_le zero_lt_one hy
    have hp : 1≤y^K := one_le_pow₀ hy
    rw [Real.norm_eq_abs,abs_of_nonneg (mellinEnvelope_nonneg K hD hE hy0),
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    unfold mellinEnvelope
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hd := div_le_self hD hp
    linarith
  exact h.trans (isLittleO_exp_neg_mul_rpow_atTop hκ s).isBigO

theorem mellinEnvelope_integrable (K : ℕ) {D E κ : ℝ}
    (hD : 0≤D) (hE : 0≤E) (hκ : 0<κ) {s : ℂ} (hs : (K:ℝ)<s.re) :
    IntegrableOn (fun y : ℝ => ‖(y:ℂ)^(s-1)‖*mellinEnvelope K D E κ y) (Ioi 0) := by
  have h := mellin_convergent_of_isBigO_scalar
    ((mellinEnvelope_continuous K D E κ).locallyIntegrableOn measurableSet_Ioi)
    (mellinEnvelope_rapid K hD hE hκ (-(s.re+1))) (by linarith : s.re<s.re+1)
    (mellinEnvelope_small K hD hE hκ) hs
  apply h.congr_fun _ measurableSet_Ioi
  intro y hy
  dsimp only
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.sub_re,Complex.one_re]

/-- One envelope controls every disk value, uniformly in the real translation. -/
theorem deformed_mellin_envelope (k : ℕ) {a : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∃ D E κ : ℝ, 0≤D ∧ 0≤E ∧ 0<κ ∧
      ∀ β y : ℝ, 0<y → ∀ u : ℂ, ‖u‖≤1/2 →
        ‖deformed k a β c y u‖≤mellinEnvelope K D E κ y := by
  obtain ⟨K,D,hD,hpower⟩ := deformed_family_bound k ha ha0 hc
  obtain ⟨E,hE,hexp⟩ := deformed_family_exponential k ha ha0 hc
  let κ : ℝ := 2*Real.pi/(8*c)
  have hκ : 0<κ := by dsimp [κ]; positivity
  refine ⟨K,D*Real.exp (κ*(8*c)),E,κ,by positivity,hE,hκ,?_⟩
  intro β y hy u hu
  by_cases hlarge : 8*c≤y
  · apply (hexp β y hlarge u hu).trans
    unfold mellinEnvelope κ
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact le_add_of_nonneg_left (by positivity)
  · have hsmall : y≤8*c := (lt_of_not_ge hlarge).le
    have hex : 1≤Real.exp (κ*(8*c-y)) := Real.one_le_exp_iff.mpr (mul_nonneg hκ.le (sub_nonneg.mpr hsmall))
    apply (hpower β y hy u hu).trans
    unfold mellinEnvelope
    calc
      D/y^K≤(D/y^K)*Real.exp (κ*(8*c-y)) := le_mul_of_one_le_right (by positivity) hex
      _=(D*Real.exp (κ*(8*c))/y^K)*Real.exp (-κ*y) := by
        rw [show κ*(8*c-y)=κ*(8*c)+(-κ*y) by ring,Real.exp_add]
        ring
      _≤_ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE) (Real.exp_pos _).le

#print axioms mellinEnvelope_integrable
#print axioms deformed_mellin_envelope
end SmallLevelTaylor
