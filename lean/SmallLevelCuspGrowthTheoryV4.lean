module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Tactic
public import SmallLevelOriginalV1

/-! Consolidated chapter: SmallLevelCuspGrowth. Original declarations and local scopes are retained. -/

/-! ## SmallLevelCuspGrowthV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelCuspGrowth

open Complex Filter Asymptotics Function.Periodic
open scoped Topology Manifold

local notation "I∞" => comap Complex.im atTop

/-- A periodic holomorphic function whose product with q tends to zero has
a removable singularity at the cusp. No boundedness premise is assumed. -/
theorem bounded_of_q_mul_zero {h : ℝ} (hh : 0<h) {f : ℂ → ℂ}
    (hp : Function.Periodic f (h:ℂ))
    (hd : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (hz : Tendsto (fun z => qParam h z*f z) I∞ (𝓝 0)) :
    BoundedAtFilter I∞ f := by
  let G := Function.Periodic.cuspFunction h f
  have hG : ∀ᶠ q in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ G q :=
    eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hp hd
  have hprod : Tendsto (fun q : ℂ => q*G q) (𝓝[≠] 0) (𝓝 0) := by
    apply (hz.comp (invQParam_tendsto hh)).congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [Function.comp_def, qParam_right_inv hh.ne' hq, G,
      cuspFunction_eq_of_nonzero _ _ hq]
  have hq : Tendsto (fun q : ℂ => q) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun q : ℂ => q*(G q-G 0)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_sub, zero_mul, sub_zero] using hprod.sub (hq.mul_const (G 0))
  have ho : (fun q : ℂ => G q-G 0) =o[𝓝[≠] 0] (fun q => (q-0)⁻¹) := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · simpa only [sub_zero, div_inv_eq_mul, mul_comm] using hdiff
    · filter_upwards [self_mem_nhdsWithin] with q hq
      simp only [sub_zero, inv_eq_zero]
      exact fun h => (hq h).elim
  have ht := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hG ho
  have hf : Tendsto f I∞ (𝓝 (limUnder (𝓝[≠] (0:ℂ)) G)) := by
    simpa only [Function.comp_def, G, eq_cuspFunction hh.ne' hp] using ht.comp (qParam_tendsto hh)
  exact hf.isBigO_one ℝ

/-- Exponential decay of q dominates any polynomial height growth. -/
theorem q_mul_zero_of_polynomial {h : ℝ} (hh : 0<h) {f : ℂ → ℂ}
    (d : ℕ) (C : ℝ) (hb : ∀ᶠ z in I∞, ‖f z‖ ≤ C*z.im^d) :
    Tendsto (fun z => qParam h z*f z) I∞ (𝓝 0) := by
  have ht : Tendsto (fun y : ℝ => y^d*Real.exp (-(2*Real.pi/h)*y)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d:ℝ) (2*Real.pi/h) (by positivity)
  have him : Tendsto Complex.im I∞ atTop := tendsto_comap
  apply squeeze_zero_norm' _ (by simpa only [Function.comp_def, mul_zero] using (ht.comp him).const_mul C)
  filter_upwards [hb] with z hz
  rw [norm_mul, norm_qParam]
  calc
    _ ≤ Real.exp (-2*Real.pi*z.im/h)*(C*z.im^d) :=
      mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
    _ = C*(z.im^d*Real.exp (-(2*Real.pi/h)*z.im)) := by
      rw [show -2*Real.pi*z.im/h= -(2*Real.pi/h)*z.im by ring]
      ring

theorem bounded_of_polynomial {h : ℝ} (hh : 0<h) {f : ℂ → ℂ}
    (hp : Function.Periodic f (h:ℂ))
    (hd : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (d : ℕ) (C : ℝ) (hb : ∀ᶠ z in I∞, ‖f z‖ ≤ C*z.im^d) :
    BoundedAtFilter I∞ f :=
  bounded_of_q_mul_zero hh hp hd (q_mul_zero_of_polynomial hh d C hb)

/-- Version for actual functions on the upper half-plane. -/
theorem upper_bounded_of_polynomial {h : ℝ} (hh : 0<h) {f : UpperHalfPlane → ℂ}
    (hp : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (h:ℂ))
    (hd : MDiff f) (d : ℕ) (C A : ℝ)
    (hb : ∀ z : UpperHalfPlane, A ≤ z.im → ‖f z‖ ≤ C*z.im^d) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  have hol : ∀ᶠ z in I∞, DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z := by
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0:ℝ))] with z hz
    exact UpperHalfPlane.mdifferentiableAt_iff.mp (hd ⟨z,hz⟩)
  have bound : ∀ᶠ z in I∞, ‖(f ∘ UpperHalfPlane.ofComplex) z‖ ≤ C*z.im^d := by
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0:ℝ)),
      tendsto_comap.eventually (eventually_ge_atTop A)] with z hz hA
    simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.im, UpperHalfPlane.coe_mk] using hb ⟨z,hz⟩ hA
  have res := (bounded_of_polynomial hh hp hol d C bound).comp_tendsto
    UpperHalfPlane.tendsto_coe_atImInfty
  change f =O[UpperHalfPlane.atImInfty] (fun _ => (1:ℝ))
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply, Pi.one_apply] using res

#print axioms bounded_of_q_mul_zero
#print axioms bounded_of_polynomial
#print axioms upper_bounded_of_polynomial

end SmallLevelCuspGrowth
end
end

/-! ## SmallLevelCuspPeriodV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelCuspGrowth

open UpperHalfPlane Complex
open scoped Topology Manifold

theorem periodic_strip_reduction {h : ℝ} (hh : 0<h) {f : ℍ → ℂ}
    (hp : Function.Periodic (f ∘ ofComplex) (h:ℂ)) (z : ℍ) :
    ∃ w : ℍ, |w.re|≤h ∧ w.im=z.im ∧ f w=f z := by
  let n : ℤ := Int.floor (z.re/h)
  let w : ℍ := ⟨(z:ℂ)-(n:ℂ)*(h:ℂ), by simpa using z.im_pos⟩
  have hre : w.re=z.re-(n:ℝ)*h := by simp [w]
  have him : w.im=z.im := by simp [w]
  have hlo : (n:ℝ)*h≤z.re := (le_div_iff₀ hh).mp (Int.floor_le (z.re/h))
  have hhi : z.re<((n:ℝ)+1)*h := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (z.re/h))
  refine ⟨w, ?_,him,?_⟩
  · rw [hre, abs_of_nonneg (by linarith)]
    nlinarith
  · have he := (hp.zsmul n).sub_eq (z:ℂ)
    simpa only [Function.comp_def, zsmul_eq_mul, ← show (w:ℂ)=(z:ℂ)-(n:ℂ)*(h:ℂ) from rfl,
      ofComplex_apply] using he

theorem bounded_of_strip {h : ℝ} (hh : 0<h) {f : ℍ → ℂ}
    (hp : Function.Periodic (f ∘ ofComplex) (h:ℂ)) (hd : MDiff f)
    (d : ℕ) (C A : ℝ)
    (hb : ∀ z : ℍ, |z.re|≤h → A≤z.im → ‖f z‖≤C*z.im^d) :
    IsBoundedAtImInfty f := by
  apply upper_bounded_of_polynomial hh hp hd d C A
  intro z hz
  obtain ⟨w,hw,hi,he⟩ := periodic_strip_reduction hh hp z
  rw [← he, ← hi]
  exact hb w hw (hi.symm ▸ hz)

#print axioms periodic_strip_reduction
#print axioms bounded_of_strip

end SmallLevelCuspGrowth
end
end

/-! ## SmallLevelGammaZeroPeriodV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelCuspGrowth

open UpperHalfPlane ModularGroup Matrix
open scoped ModularForm MatrixGroups

theorem conjugate_translation_mem (N : ℕ) (γ : SL(2,ℤ)) :
    γ*(T^(N:ℤ))*γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  let r : SL(2,ℤ) →* SL(2,ZMod N) := SpecialLinearGroup.map (Int.castRingHom (ZMod N))
  have ht : r (T^(N:ℤ))=1 := by
    apply Subtype.ext
    change ((T^(N:ℤ)).1).map (fun z : ℤ => (z : ZMod N))=1
    rw [ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have he : r (γ*(T^(N:ℤ))*γ⁻¹)=1 := by rw [map_mul, map_mul, map_inv, ht]; group
  exact CongruenceSubgroup.Gamma0_mem.mpr (congrArg (fun A : SL(2,ZMod N) => A 1 0) he)

/-- N is a common period at every cusp for a Gamma0(N)-invariant function. -/
theorem gamma_zero_period (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ : SL(2,ℤ), γ∈CongruenceSubgroup.Gamma0 N → f ∣[k] γ=f)
    (γ : SL(2,ℤ)) :
    Function.Periodic ((f ∣[k] γ) ∘ ofComplex) (N:ℂ) := by
  have he := congrArg (fun F : ℍ → ℂ => F ∣[k] γ) (hf _ (conjugate_translation_mem N γ))
  have hh : (f ∣[k] γ) ∣[k] (T^(N:ℤ))=f ∣[k] γ := by
    simpa only [← SlashAction.slash_mul, mul_assoc, inv_mul_cancel, mul_one] using he
  apply UpperHalfPlane.periodic_comp_ofComplex (h:=(N:ℝ))
  intro z
  have hz := congrFun hh z
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul] at hz
  have hd : denom (T^(N:ℤ) : SL(2,ℤ)) z=1 := by
    rw [ModularGroup.denom_apply]
    rw [ModularGroup.coe_T_zpow]
    norm_num
  simpa only [hd, one_zpow, mul_one, Int.cast_natCast] using hz

#print axioms conjugate_translation_mem
#print axioms gamma_zero_period

end SmallLevelCuspGrowth
end
end

/-! ## SmallLevelSlashGrowthV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelCuspGrowth

open UpperHalfPlane ModularGroup Matrix Complex
open scoped ModularForm MatrixGroups

theorem denom_lower (γ : SL(2,ℤ)) (z : ℍ) (hy : 1≤z.im) : 1≤‖denom γ z‖ := by
  by_cases hc : γ 1 0=0
  · have hd : γ 1 1≠0 := by
      intro hd
      have hh := γ.property
      rw [det_fin_two] at hh
      simp [hc,hd] at hh
    have hd1 : (1:ℝ)≤|(γ 1 1:ℝ)| := by exact_mod_cast Int.one_le_abs hd
    simpa [ModularGroup.denom_apply, hc] using hd1
  · have hc1 : (1:ℝ)≤|(γ 1 0:ℝ)| := by exact_mod_cast Int.one_le_abs hc
    calc
      1 ≤ |(γ 1 0:ℝ)| *z.im := by nlinarith
      _ = |(denom γ z).im| := by
        simp [ModularGroup.denom_apply, abs_mul, abs_of_pos z.im_pos]
      _ ≤ ‖denom γ z‖ := Complex.abs_im_le_norm _

theorem denom_upper (γ : SL(2,ℤ)) {R : ℝ} (hR : 0≤R) (z : ℍ)
    (hx : |z.re|≤R) (hy : 1≤z.im) :
    ‖denom γ z‖ ≤ (|(γ 1 0:ℝ)| *(R+1)+|(γ 1 1:ℝ)|)*z.im := by
  have hz : ‖(z:ℂ)‖ ≤ (R+1)*z.im := by
    calc
      ‖(z:ℂ)‖ ≤ |z.re| +|z.im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ R+z.im := by rw [abs_of_pos z.im_pos]; linarith
      _ ≤ (R+1)*z.im := by nlinarith
  rw [ModularGroup.denom_apply]
  calc
    _ ≤ ‖(γ 1 0:ℂ)*(z:ℂ)‖+‖(γ 1 1:ℂ)‖ := norm_add_le _ _
    _ = |(γ 1 0:ℝ)| *‖(z:ℂ)‖+|(γ 1 1:ℝ)| := by simp
    _ ≤ |(γ 1 0:ℝ)| *((R+1)*z.im)+|(γ 1 1:ℝ)| *z.im := by
      gcongr
      exact le_mul_of_one_le_right (abs_nonneg _) hy
    _ = _ := by ring

/-- A global inverse-height bound gives polynomial growth for every
integral modular-group translate, uniformly on a bounded real strip. -/
theorem slash_polynomial_strip (k b : ℕ) (f : ℍ → ℂ) {M R : ℝ}
    (hM : 0≤M) (hR : 0≤R)
    (hb : ∀ z : ℍ, z.im^b*‖f z‖≤M) (γ : SL(2,ℤ)) (z : ℍ)
    (hx : |z.re|≤R) (hy : 1≤z.im) :
    ‖(f ∣[(k:ℤ)] γ) z‖ ≤
      (M*(|(γ 1 0:ℝ)| *(R+1)+|(γ 1 1:ℝ)|)^(2*b))*z.im^(2*b) := by
  have hd := denom_lower γ z hy
  have hdp : 0<‖denom γ z‖ := lt_of_lt_of_le zero_lt_one hd
  have hf : ‖f (γ • z)‖ ≤ M/(γ • z).im^b :=
    (le_div_iff₀ (pow_pos (γ • z).im_pos b)).mpr (by simpa only [mul_comm] using hb (γ • z))
  have hf' : ‖f (γ • z)‖ ≤ M*‖denom γ z‖^(2*b) := by
    apply hf.trans
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, div_pow,
      div_div_eq_mul_div, ← pow_mul]
    exact div_le_self (mul_nonneg hM (pow_nonneg (norm_nonneg _) _)) (one_le_pow₀ hy)
  have hfac : ‖denom γ z ^ (-(k:ℤ))‖≤1 := by
    rw [norm_zpow, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hd)
  rw [ModularForm.SL_slash_apply, norm_mul]
  calc
    _ ≤ ‖f (γ • z)‖ := mul_le_of_le_one_right (norm_nonneg _) hfac
    _ ≤ M*‖denom γ z‖^(2*b) := hf'
    _ ≤ M*((|(γ 1 0:ℝ)| *(R+1)+|(γ 1 1:ℝ)|)*z.im)^(2*b) := by
      gcongr
      exact denom_upper γ hR z hx hy
    _ = _ := by rw [mul_pow, mul_assoc]

#print axioms denom_lower
#print axioms denom_upper
#print axioms slash_polynomial_strip

end SmallLevelCuspGrowth
end
end
