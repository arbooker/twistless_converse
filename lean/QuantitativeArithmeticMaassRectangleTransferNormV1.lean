module

public import QuantitativeArithmeticMaassCanonicalCutoffTransferV1
public import QuantitativeArithmeticMaassOverlapTheoryV4
public import QuantitativeMaassStrongScaleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane Matrix ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology MatrixGroups
namespace QuantitativeArithmeticMaassOverlap

/-- The integer-box proof applies also to the translation subgroup at
level zero, which is the source of the cross-quotient transfer. -/
theorem ball_overlap_bound_all_levels (N : ℕ) (o : ℍ) (U : ℝ) (B : ℕ)
    (hB : Real.exp (U + dist o I) ≤ (B : ℝ))
    (x : ℍ) (S : Finset (gamma N))
    (hS : ∀ g∈S, dist (g • x) o ≤ U) : S.card ≤ (2*B+1)^4 := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨g₀,hg₀⟩ := hne
    let rel : gamma N → gamma N := fun g => g*g₀⁻¹
    have hrel : Function.Injective rel := (Equiv.mulRight g₀⁻¹).injective
    have hbox : ∀ g∈S.image rel, ∀ i j : Fin 2,
        |((representative g) i j : ℤ)| ≤ (B : ℤ) := by
      intro d hd i j
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
      have hy : dist (g₀ • x) I ≤ U+dist o I :=
        (dist_triangle (g₀ • x) o I).trans (add_le_add (hS g₀ hg₀) le_rfl)
      have hz : dist (g • x) I ≤ U+dist o I :=
        (dist_triangle (g • x) o I).trans (add_le_add (hS g hg) le_rfl)
      have he : rel g • (g₀ • x) = g • x := by
        simp only [rel, mul_smul, inv_smul_smul]
      have hd : dist (rel g • I) I ≤ 2*(U+dist o I) := by
        calc
          _ ≤ dist (rel g • I) (rel g • (g₀ • x)) +
              dist (rel g • (g₀ • x)) I := dist_triangle _ _ _
          _ = dist I (g₀ • x) + dist (g • x) I := by
            rw [QuantitativeMaass.congruence_action_dist, he]
          _ ≤ (U+dist o I)+(U+dist o I) :=
            add_le_add (by simpa only [dist_comm] using hy) hz
          _ = _ := by ring
      have ha : representative (rel g) • I = rel g • I := by
        rw [← integralLabel_action, representative_label]
        rfl
      have hb := entry_abs_le_exp (representative (rel g)) (U+dist o I)
        (by simpa only [ha] using hd) i j
      exact_mod_cast hb.trans hB
    have hc := gamma_entry_card_bound N B (S.image rel) hbox
    rwa [Finset.card_image_of_injective S hrel] at hc
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.zero_le]

end QuantitativeArithmeticMaassOverlap
namespace QuantitativeMaass

/-- A rectangle has logarithmic hyperbolic radius in its height bounds. -/
theorem rectangle_dist_bound (a b : ℝ) (ha : 0<a) (z : ℍ)
    (hz : z∈upperRectangle 0 1 a b) :
    dist z I≤Real.log ((2+b^2)/a) := by
  have hx : 0≤z.re ∧ z.re≤1 := hz.1
  have hy : a≤z.im ∧ z.im≤b := hz.2
  have hb : 0≤b := z.im_pos.le.trans hy.2
  have hcosh : 2*Real.cosh (dist z I)=(z.re^2+z.im^2+1)/z.im := by
    rw [cosh_dist']
    simp only [I_re,I_im,sub_zero,one_pow,mul_one]
    field_simp
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  calc
    Real.exp (dist z I) ≤ 2*Real.cosh (dist z I) := by
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-dist z I)]
    _ = _ := hcosh
    _ ≤ (2+b^2)/a := by
      apply div_le_div₀ (by positivity) _ ha hy.1
      have hx2 : z.re^2≤1 := by nlinarith
      have hy2 : z.im^2≤b^2 := pow_le_pow_left₀ z.im_pos.le hy.2 2
      linarith

/-- Uniform in the level, including level zero; all counts refer to the
actual projective group, not redundant integral matrix representatives. -/
theorem rectangle_overlap_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (z : ℍ) (S : Finset (gamma N))
    (hS : ∀ g∈S,g•z∈upperRectangle 0 1 a b) :
    S.card≤(2*⌈(2+b^2)/a⌉₊+1)^4 := by
  refine QuantitativeArithmeticMaassOverlap.ball_overlap_bound_all_levels N I
    (Real.log ((2+b^2)/a)) _ ?_ z S ?_
  · simpa only [dist_self,add_zero,Real.exp_log (show 0<(2+b^2)/a by positivity)] using
      (Nat.le_ceil ((2+b^2)/a))
  · intro g hg
    exact rectangle_dist_bound a b ha (g•z) (hS g hg)

/-- Explicit norm bound for every measurable multiplier of absolute value
at most one on the rectangle. No unspecified compactness constant remains. -/
theorem rectangle_transfer_norm_sq (N : ℕ) (a b : ℝ) (ha : 0<a)
    (v : ℍ→ℂ) (hv : AEStronglyMeasurable v (volume.restrict (upperRectangle 0 1 a b)))
    (hbound : ∀ᵐ x ∂volume.restrict (upperRectangle 0 1 a b),‖v x‖≤1) :
    ‖boundedCrossQuotientLocalization N 0 (upperRectangle 0 1 a b)
      (upperRectangle_compact 0 1 a b ha) v hv hbound‖^2≤
        (2*(⌈(2+b^2)/a⌉₊:ℝ)+1)^8 := by
  let Ω := upperRectangle 0 1 a b
  let hΩ := upperRectangle_compact 0 1 a b ha
  let m := (2*⌈(2+b^2)/a⌉₊+1)^4
  let RN := quotientRestriction N Ω hΩ hΩ.measurableSet
  let R0 := quotientRestriction 0 Ω hΩ hΩ.measurableSet
  let V := AsymptoticL2Multiplier.operator v hv hbound
  have hn : ‖RN.adjoint‖≤Real.sqrt (m:ℝ) := by
    rw [adjoint.norm_map]
    exact quotientRestriction_norm_le_of_overlap N Ω hΩ m (rectangle_overlap_bound N a b ha)
  have h0 : ‖R0‖≤Real.sqrt (m:ℝ) :=
    quotientRestriction_norm_le_of_overlap 0 Ω hΩ m (rectangle_overlap_bound 0 a b ha)
  have hvn : ‖V‖≤1 := AsymptoticL2Multiplier.operator_norm_le v hv (by norm_num) hbound
  have hop : ‖RN.adjoint.comp (V.comp R0)‖≤(m:ℝ) := by
    calc
      _ ≤ ‖RN.adjoint‖*‖V.comp R0‖ := opNorm_comp_le _ _
      _ ≤ Real.sqrt (m:ℝ)*(1*Real.sqrt (m:ℝ)) := by
        apply mul_le_mul hn _ (norm_nonneg (V.comp R0)) (Real.sqrt_nonneg _)
        exact (opNorm_comp_le V R0).trans (mul_le_mul hvn h0 (norm_nonneg R0) (by norm_num))
      _ = _ := by rw [one_mul,←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
  change ‖RN.adjoint.comp (V.comp R0)‖^2≤_
  calc
    _ ≤ (m:ℝ)^2 := pow_le_pow_left₀ (norm_nonneg (RN.adjoint.comp (V.comp R0))) hop 2
    _ = _ := by norm_num [m,←pow_mul]

/-- Polynomial rectangle costs are absorbed by one extra strong-scale
exponent; this permits the upper height and lower height to vary. -/
theorem rectangle_transfer_norm_schedule (N : ℕ) (a b : ℝ→ℝ) (ha : ∀ t,0<a t)
    (v : ℝ→ℍ→ℂ)
    (hv : ∀ t,AEStronglyMeasurable (v t) (volume.restrict (upperRectangle 0 1 (a t) (b t))))
    (hbound : ∀ t,∀ᵐ x ∂volume.restrict (upperRectangle 0 1 (a t) (b t)),‖v t x‖≤1)
    (Y : ℝ) (hY : 0≤Y)
    (hsize : ∀ᶠ t in atTop,(2+(b t)^2)/a t≤Real.exp (Y*Strong.strongScale t)) :
    ∀ᶠ t in atTop,
      ‖boundedCrossQuotientLocalization N 0 (upperRectangle 0 1 (a t) (b t))
        (upperRectangle_compact 0 1 (a t) (b t) (ha t)) (v t) (hv t) (hbound t)‖^2≤
          Real.exp ((8*Y+1)*Strong.strongScale t) := by
  have hexp := (Real.tendsto_exp_atTop.comp Strong.strongScale_tendsto).eventually
    (eventually_ge_atTop ((5:ℝ)^8))
  filter_upwards [hsize,hexp] with t ht he
  have h1 : 1≤Real.exp (Y*Strong.strongScale t) := Real.one_le_exp (mul_nonneg hY (sq_nonneg _))
  have hat := ha t
  have hceil := Nat.ceil_lt_add_one (show 0≤(2+(b t)^2)/a t by positivity)
  have hb : 2*(⌈(2+(b t)^2)/a t⌉₊:ℝ)+1≤5*Real.exp (Y*Strong.strongScale t) := by linarith
  apply (rectangle_transfer_norm_sq N (a t) (b t) (ha t) (v t) (hv t) (hbound t)).trans
  calc
    _ ≤ (5*Real.exp (Y*Strong.strongScale t))^8 := pow_le_pow_left₀ (by positivity) hb 8
    _ ≤ Real.exp (Strong.strongScale t)*(Real.exp (Y*Strong.strongScale t))^8 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by
      rw [←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      norm_num
      ring

#print axioms QuantitativeArithmeticMaassOverlap.ball_overlap_bound_all_levels
#print axioms rectangle_dist_bound
#print axioms rectangle_overlap_bound
#print axioms rectangle_transfer_norm_sq
#print axioms rectangle_transfer_norm_schedule
end QuantitativeMaass
