module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

/-!
Uniqueness of the square-integrable branch in the positive-height ODE.
The squared norm of a solution to F''=qF is convex where q is nonnegative.
A nonzero convex profile vanishing at the initial height has at least
linear growth, which contradicts integrability with hyperbolic weight y^-2.
This will select the actual decaying Bessel branch; no growing-solution
asymptotic or additional spectral assumption is required by these lemmas.
-/

namespace QuantitativeNinaMaass

theorem convex_zero_of_hyperbolic_integrable (a : ℝ) (ha : 0 < a)
    (f : ℝ → ℝ) (hc : ConvexOn ℝ (Ici a) f)
    (hn : ∀ x ∈ Ici a, 0 ≤ f x) (hz : f a = 0)
    (hi : IntegrableOn (fun x => f x / x ^ 2) (Ioi a)) :
    ∀ x ∈ Ici a, f x = 0 := by
  intro t ht
  by_contra hft
  have hpos : 0 < f t := lt_of_le_of_ne (hn t ht) (Ne.symm hft)
  have hat : a < t := lt_of_le_of_ne ht (by intro he; exact hft (he ▸ hz))
  let c : ℝ := f t / (t - a)
  have hcpos : 0 < c := div_pos hpos (sub_pos.mpr hat)
  let R := max t (2 * a)
  have hR : 0 < R := (ha.trans hat).trans_le (le_max_left _ _)
  have haR : a ≤ R := hat.le.trans (le_max_left _ _)
  have hbound (y : ℝ) (hy : R < y) : y⁻¹ ≤ (2 / c) * (f y / y ^ 2) := by
    have hty : t ≤ y := (le_max_left t (2 * a)).trans hy.le
    have hay : a < y := hat.trans_le hty
    have hypos : 0 < y := hR.trans hy
    have h2a : 2 * a ≤ y := (le_max_right t (2 * a)).trans hy.le
    have hs := hc.monotoneOn_slope_gt (show a ∈ Ici a from le_rfl)
      ⟨ht, hat⟩ ⟨hay.le, hay⟩ hty
    rw [slope_def_field, slope_def_field, hz, sub_zero, sub_zero] at hs
    have hlin : c * (y - a) ≤ f y := (le_div_iff₀ (sub_pos.mpr hay)).mp hs
    have hf : c * y ≤ 2 * f y := by nlinarith
    calc
      y⁻¹ = y / y ^ 2 := by field_simp
      _ ≤ (2 * f y / c) / y ^ 2 :=
        div_le_div_of_nonneg_right ((le_div_iff₀ hcpos).mpr (by nlinarith)) (sq_nonneg y)
      _ = (2 / c) * (f y / y ^ 2) := by ring
  apply not_integrableOn_Ioi_inv (a := R)
  apply ((hi.mono_set (fun y hy => haR.trans_lt hy)).const_mul (2 / c)).mono'
  · exact (continuousOn_id.inv₀ (fun y hy => (hR.trans hy).ne')).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hR.trans hy))]
    exact hbound y hy

theorem ode_norm_sq_convex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : ℝ) (F V : ℝ → H) (q : ℝ → ℝ)
    (hF : ∀ t ∈ Ici a, HasDerivAt F (V t) t)
    (hV : ∀ t ∈ Ici a, HasDerivAt V (q t • F t) t)
    (hq : ∀ t ∈ Ici a, 0 ≤ q t) :
    ConvexOn ℝ (Ici a) (fun t => ‖F t‖ ^ 2) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici a)
    (f' := fun t => 2 * inner ℝ (F t) (V t))
    (f'' := fun t => 2 * (inner ℝ (F t) (q t • F t) + inner ℝ (V t) (V t)))
  · intro t ht
    exact (hF t ht).norm_sq.continuousAt.continuousWithinAt
  · intro t ht
    exact (hF t (interior_subset ht)).norm_sq.hasDerivWithinAt
  · intro t ht
    exact (((hF t (interior_subset ht)).inner ℝ (hV t (interior_subset ht))).const_mul 2).hasDerivWithinAt
  · intro t ht
    rw [inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    exact mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg (hq t (interior_subset ht)) (sq_nonneg _)) (sq_nonneg _))

/-- A square-integrable solution on a positive-potential tail is
determined by one value. This is the uniqueness step for the decaying
Fourier--Bessel profile, before matching a particular Bessel function. -/
theorem ode_zero_of_hyperbolic_integrable {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : ℝ) (ha : 0 < a) (F V : ℝ → H) (q : ℝ → ℝ)
    (hF : ∀ t ∈ Ici a, HasDerivAt F (V t) t)
    (hV : ∀ t ∈ Ici a, HasDerivAt V (q t • F t) t)
    (hq : ∀ t ∈ Ici a, 0 ≤ q t) (hz : F a = 0)
    (hi : IntegrableOn (fun t => ‖F t‖ ^ 2 / t ^ 2) (Ioi a)) :
    ∀ t ∈ Ici a, F t = 0 := by
  have h := convex_zero_of_hyperbolic_integrable a ha (fun t => ‖F t‖ ^ 2)
    (ode_norm_sq_convex a F V q hF hV hq) (fun _ _ => sq_nonneg _)
    (by simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]) hi
  intro t ht
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (h t ht))

theorem hyperbolic_integrable_sub {H : Type*} [NormedAddCommGroup H]
    (a : ℝ) (ha : 0 < a) (F G : ℝ → H)
    (hF : ContinuousOn F (Ioi a)) (hG : ContinuousOn G (Ioi a))
    (hiF : IntegrableOn (fun t => ‖F t‖ ^ 2 / t ^ 2) (Ioi a))
    (hiG : IntegrableOn (fun t => ‖G t‖ ^ 2 / t ^ 2) (Ioi a)) :
    IntegrableOn (fun t => ‖F t - G t‖ ^ 2 / t ^ 2) (Ioi a) := by
  apply ((hiF.const_mul 2).add (hiG.const_mul 2)).mono'
  · exact (((hF.sub hG).norm.pow 2).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ha.trans ht).ne')).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg t))]
    have hnorm := norm_sub_le (F t) (G t)
    have hsq : ‖F t - G t‖ ^ 2 ≤ 2 * ‖F t‖ ^ 2 + 2 * ‖G t‖ ^ 2 := by
      nlinarith [norm_nonneg (F t - G t), norm_nonneg (F t), norm_nonneg (G t),
        sq_nonneg (‖F t‖ - ‖G t‖)]
    calc
      _ ≤ (2 * ‖F t‖ ^ 2 + 2 * ‖G t‖ ^ 2) / t ^ 2 :=
        div_le_div_of_nonneg_right hsq (sq_nonneg t)
      _ = _ := by simp only [Pi.add_apply]; ring

theorem ode_unique_of_hyperbolic_integrable {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : ℝ) (ha : 0 < a) (F V G W : ℝ → H) (q : ℝ → ℝ)
    (hF : ∀ t ∈ Ici a, HasDerivAt F (V t) t)
    (hV : ∀ t ∈ Ici a, HasDerivAt V (q t • F t) t)
    (hG : ∀ t ∈ Ici a, HasDerivAt G (W t) t)
    (hW : ∀ t ∈ Ici a, HasDerivAt W (q t • G t) t)
    (hq : ∀ t ∈ Ici a, 0 ≤ q t) (hz : F a = G a)
    (hiF : IntegrableOn (fun t => ‖F t‖ ^ 2 / t ^ 2) (Ioi a))
    (hiG : IntegrableOn (fun t => ‖G t‖ ^ 2 / t ^ 2) (Ioi a)) :
    ∀ t ∈ Ici a, F t = G t := by
  have h := ode_zero_of_hyperbolic_integrable a ha (fun t => F t - G t) (fun t => V t - W t) q
    (fun t ht => (hF t ht).sub (hG t ht))
    (fun t ht => by simpa only [Pi.sub_def, smul_sub] using (hV t ht).sub (hW t ht)) hq
    (sub_eq_zero.mpr hz)
    (hyperbolic_integrable_sub a ha F G
      (fun t ht => (hF t ht.le).continuousAt.continuousWithinAt)
      (fun t ht => (hG t ht.le).continuousAt.continuousWithinAt) hiF hiG)
  exact fun t ht => sub_eq_zero.mp (h t ht)

theorem secondOrderSystem_lipschitz {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (q : ℝ) (K : NNReal) (hK : 1 ≤ (K : ℝ)) (hq : ‖q‖ ≤ K) :
    LipschitzWith K (fun x : H × H => (x.2, q • x.1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change max (dist x.2 y.2) (dist (q • x.1) (q • y.1)) ≤
    (K : ℝ) * max (dist x.1 y.1) (dist x.2 y.2)
  rw [dist_smul₀]
  apply max_le
  · calc
      _ ≤ (K : ℝ) * dist x.2 y.2 := by nlinarith [show 0 ≤ dist x.2 y.2 from dist_nonneg]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) K.coe_nonneg
  · exact mul_le_mul hq (le_max_left _ _) dist_nonneg K.coe_nonneg

/-- The ordinary Cauchy uniqueness theorem on every positive interval,
with the Lipschitz bound obtained from continuity on a compact interval. -/
theorem positive_ode_cauchy_unique {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F V G W : ℝ → H) (q : ℝ → ℝ) (hq : ContinuousOn q (Ioi 0))
    (hF : ∀ t, 0 < t → HasDerivAt F (V t) t)
    (hV : ∀ t, 0 < t → HasDerivAt V (q t • F t) t)
    (hG : ∀ t, 0 < t → HasDerivAt G (W t) t)
    (hW : ∀ t, 0 < t → HasDerivAt W (q t • G t) t)
    (s : ℝ) (hs : 0 < s) (hFs : F s = G s) (hVs : V s = W s) :
    ∀ t, 0 < t → F t = G t := by
  intro t ht
  let a := min s t / 2
  let b := max s t + 1
  have hm : 0 < min s t := lt_min hs ht
  have ha : 0 < a := half_pos hm
  have ham : a < min s t := half_lt_self hm
  have has : a < s := ham.trans_le (min_le_left _ _)
  have hat : a < t := ham.trans_le (min_le_right _ _)
  have hsb : s < b := by dsimp only [b]; linarith [le_max_left s t]
  have htb : t < b := by dsimp only [b]; linarith [le_max_right s t]
  have hpos (y : ℝ) (hy : y ∈ Icc a b) : 0 < y := ha.trans_le hy.1
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    (hq.mono (fun y hy => hpos y hy))
  let K : NNReal := ⟨max 1 C, le_trans zero_le_one (le_max_left _ _)⟩
  have hsys (y : ℝ) (hy : y ∈ Ioo a b) :
      LipschitzOnWith K (fun x : H × H => (x.2, q y • x.1)) univ :=
    (secondOrderSystem_lipschitz (q y) K (le_max_left _ _)
      ((hC y ⟨hy.1.le, hy.2.le⟩).trans (le_max_right _ _))).lipschitzOnWith
  have he := ODE_solution_unique_of_mem_Icc
    (v := fun (y : ℝ) (x : H × H) => (x.2, q y • x.1))
    (s := fun _ => univ) (f := fun y => (F y, V y)) (g := fun y => (G y, W y))
    hsys (show s ∈ Ioo a b from ⟨has, hsb⟩)
    (fun y hy => ((hF y (hpos y hy)).prodMk (hV y (hpos y hy))).continuousAt.continuousWithinAt)
    (fun y hy => (hF y (hpos y ⟨hy.1.le, hy.2.le⟩)).prodMk (hV y (hpos y ⟨hy.1.le, hy.2.le⟩)))
    (fun _ _ => mem_univ _)
    (fun y hy => ((hG y (hpos y hy)).prodMk (hW y (hpos y hy))).continuousAt.continuousWithinAt)
    (fun y hy => (hG y (hpos y ⟨hy.1.le, hy.2.le⟩)).prodMk (hW y (hpos y ⟨hy.1.le, hy.2.le⟩)))
    (fun _ _ => mem_univ _) (Prod.ext hFs hVs)
  exact congrArg Prod.fst (he ⟨hat.le, htb.le⟩)

/-- Equality on an actual tail extends to all positive heights. The
second initial datum is derived from local equality of the functions. -/
theorem positive_ode_unique_of_tail {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F V G W : ℝ → H) (q : ℝ → ℝ) (hq : ContinuousOn q (Ioi 0))
    (hF : ∀ t, 0 < t → HasDerivAt F (V t) t)
    (hV : ∀ t, 0 < t → HasDerivAt V (q t • F t) t)
    (hG : ∀ t, 0 < t → HasDerivAt G (W t) t)
    (hW : ∀ t, 0 < t → HasDerivAt W (q t • G t) t)
    (a : ℝ) (ha : 0 < a) (he : ∀ t, a ≤ t → F t = G t) :
    ∀ t, 0 < t → F t = G t := by
  have hs : 0 < a + 1 := by linarith
  have hlocal : F =ᶠ[𝓝 (a + 1)] G := by
    filter_upwards [Ioi_mem_nhds (show a < a + 1 by linarith)] with y hy
    exact he y hy.le
  have hd : V (a + 1) = W (a + 1) :=
    ((hF (a + 1) hs).congr_of_eventuallyEq hlocal.symm).unique (hG (a + 1) hs)
  exact positive_ode_cauchy_unique F V G W q hq hF hV hG hW (a + 1) hs
    (he (a + 1) (by linarith)) hd

#print axioms convex_zero_of_hyperbolic_integrable
#print axioms ode_norm_sq_convex
#print axioms ode_zero_of_hyperbolic_integrable
#print axioms hyperbolic_integrable_sub
#print axioms ode_unique_of_hyperbolic_integrable
#print axioms secondOrderSystem_lipschitz
#print axioms positive_ode_cauchy_unique
#print axioms positive_ode_unique_of_tail

end QuantitativeNinaMaass
