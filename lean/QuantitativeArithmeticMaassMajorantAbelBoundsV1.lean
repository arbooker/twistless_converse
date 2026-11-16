module

public import QuantitativeMaassEnlargedWindowBoundsV1
public import QuantitativeMaassMajorantColumnsV1
public import QuantitativeNinaMaassWindowEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology FourierTransform SchwartzMap Convolution
namespace QuantitativeMaass

/-- Scalar multiplication of a time packet scales its convolution square
by the square of the same scalar. -/
theorem timeConvolution_smul_square (c : ℂ) (f : SchwartzMap ℝ ℂ) :
    timeConvolution (c • f) (c • f) = c^2 • timeConvolution f f := by
  ext x
  simp only [timeConvolution, SchwartzMap.convolution_apply, smul_apply]
  change ((c • (f : ℝ→ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (c • (f : ℝ→ℂ))) x =
    (c^2 • ((f : ℝ→ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : ℝ→ℂ))) x
  rw [smul_convolution,convolution_smul,smul_smul,pow_two]

theorem timeSquare_abelProfile_smul (c : ℂ) (f : SchwartzMap ℝ ℂ) (q : ℝ) :
    abelProfile (evenCoshLift (timeConvolution (c • f) (c • f))) q =
      c^2*abelProfile (evenCoshLift (timeConvolution f f)) q := by
  rw [timeConvolution_smul_square]
  change abelProfile (fun x => c^2*evenCoshLift (timeConvolution f f) x) q = _
  exact abelProfile_const_mul _ _ _

namespace Scheduled

/-- Exact normalization of the literal majorant square. The scalar is
`windowEnergyDenominator⁻²`, not the normalization of a different packet. -/
theorem originalMajorantSquare_abel_eq (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t q : ℝ) :
    let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
    let g := windowTimeSchwartz K hc (radius ε t) (radius_pos ε t)
      (t-smoothingWidth (slowScale t) (ε t))
      (t+ε t+smoothingWidth (slowScale t) (ε t))
    abelProfile (evenCoshLift (timeConvolution f f)) q =
      ((QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹:ℂ)^2 *
        abelProfile (evenCoshLift (timeConvolution g g)) q := by
  exact timeSquare_abelProfile_smul _ _ _

/-- The normalization costs at most four, uniformly in the Abel variable. -/
theorem originalMajorantSquare_abel_norm_le (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t q : ℝ) :
    let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
    let g := windowTimeSchwartz K hc (radius ε t) (radius_pos ε t)
      (t-smoothingWidth (slowScale t) (ε t))
      (t+ε t+smoothingWidth (slowScale t) (ε t))
    ‖abelProfile (evenCoshLift (timeConvolution f f)) q‖ ≤
      4*‖abelProfile (evenCoshLift (timeConvolution g g)) q‖ := by
  dsimp only
  rw [originalMajorantSquare_abel_eq,norm_mul,norm_pow,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (QuantitativeNinaMaass.windowEnergyDenominator_pos K ε t)]
  have hd := QuantitativeNinaMaass.windowEnergyDenominator_pos K ε t
  have hi : (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹≤2 := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1/2)
      (le_max_left (1/2:ℝ) (1-(∫ u,|u| * K u)/
        (positiveWindowRadius ε t*smoothingWidth (slowScale t) (ε t))))
    simpa only [QuantitativeNinaMaass.windowEnergyDenominator,one_div,inv_inv] using hh
  exact mul_le_mul_of_nonneg_right (by nlinarith [inv_pos.mpr hd]) (norm_nonneg _)

/-- A single diagonal constant works for every admissible shrinking width. -/
theorem originalMajorantSquare_abel_diagonal_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ B : ℝ,0<B ∧ ∀ ε : ℝ→ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,
        let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
        ‖abelProfile (evenCoshLift (timeConvolution f f)) 1‖≤B*t*ε t := by
  obtain ⟨B,hB,hbound⟩ := enlargedWindowIdentity_bound K he hc hK hm
  refine ⟨4*B,by positivity,?_⟩
  intro ε hε hp
  filter_upwards [hε,eventually_ge_atTop (3:ℝ),radius_resolves_window ε hε hp,
    QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp]
    with t heps ht hresolve hparam
  have hw := hbound (radius ε t) t (ε t)
    (t-smoothingWidth (slowScale t) (ε t))
    (t+ε t+smoothingWidth (slowScale t) (ε t))
    (le_max_left _ _) (by linarith) heps.1.le heps.2 hresolve.2 hparam.2.2
    (by linarith [hparam.1,heps.1]) (by linarith [hparam.2.1,heps.2])
    (by linarith [hparam.2.1])
  exact (originalMajorantSquare_abel_norm_le K hc ε t 1).trans
    ((mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ)≤4)).trans_eq (by ring))

/-- Uniform off-diagonal control for all positive distances. The constant
is chosen before the shrinking width, and the original width stays in the bound. -/
theorem originalMajorantSquare_abel_offdiagonal_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B : ℝ,0<B ∧ ∀ ε : ℝ→ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,∀ d : ℝ,0<d →
        let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
        ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖≤
          B*Real.sqrt t*(radius ε t)^2*(ε t)^2/Real.sqrt (Real.sinh d) := by
  obtain ⟨B,hB,hbound⟩ := enlargedWindowSquare_abel_decay K he hc
  refine ⟨4*B,by positivity,?_⟩
  intro ε hε hp
  filter_upwards [hε,eventually_ge_atTop (3:ℝ),
    QuantitativeNinaMaass.originalWindowMajorant_parameters ε hε hp]
    with t heps ht hparam
  intro d hd
  have hw := hbound (radius ε t) t (ε t)
    (t-smoothingWidth (slowScale t) (ε t))
    (t+ε t+smoothingWidth (slowScale t) (ε t)) d
    (le_max_left _ _) ht heps.1.le heps.2
    (by linarith [hparam.2.1,heps.1]) (by linarith [hparam.1,heps.1])
    (by linarith [hparam.2.1,heps.2]) (by linarith [hparam.2.1]) hd
  exact (originalMajorantSquare_abel_norm_le K hc ε t (Real.cosh d)).trans
    ((mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ)≤4)).trans_eq (by ring))

#print axioms originalMajorantSquare_abel_eq
#print axioms originalMajorantSquare_abel_norm_le
#print axioms originalMajorantSquare_abel_diagonal_bound
#print axioms originalMajorantSquare_abel_offdiagonal_bound
end Scheduled
#print axioms timeConvolution_smul_square
#print axioms abelProfile_const_mul
#print axioms timeSquare_abelProfile_smul
end QuantitativeMaass
