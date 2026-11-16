module

public import QuantitativeMaassEnergyLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Cauchy--Schwarz for the literal two-component hyperbolic energy.
Only the summed energy is used; individual derivatives need not descend
to the quotient. -/
theorem hyperbolicEnergy_norm_sq_le (u v : Point → ℂ) (Z : Point) :
    ‖hyperbolicEnergy u v Z‖^2 ≤
      (hyperbolicEnergy u u Z).re*(hyperbolicEnergy v v Z).re := by
  let a := X u Z
  let b := Y u Z
  let c := X v Z
  let d := Y v Z
  have hn : ‖star a*c+star b*d‖ ≤ ‖a‖*‖c‖+‖b‖*‖d‖ := by
    simpa only [norm_mul,norm_star] using norm_add_le (star a*c) (star b*d)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hcs : ‖star a*c+star b*d‖^2 ≤
      (‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
    nlinarith [sq_nonneg (‖a‖*‖d‖-‖b‖*‖c‖)]
  calc
    _ = Z.2^4*‖star a*c+star b*d‖^2 := by
      simp only [hyperbolicEnergy,norm_mul,norm_pow,Complex.norm_real,
        Real.norm_eq_abs,mul_pow,sq_abs]
      dsimp only [a,b,c,d]
      ring
    _ ≤ Z.2^4*((‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2)) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by
      rw [hyperbolicEnergy_self_eq,hyperbolicEnergy_self_eq]
      dsimp only [a,b,c,d]
      ring

private theorem norm_three_terms_sq (a b c : ℂ) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have hn := (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

/-- The actual differential residual of a real compact cutoff times a
smooth function. The first- and second-derivative cutoff terms are explicit. -/
theorem hyperbolic_cutoff_residual (b u : Point → ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hreal : ∀ W, star (b W)=b W) (μ : ℂ) (Z : Point) (hZ : 0<Z.2) :
    hyperbolic (fun W => b W*u W) Z-μ*(b Z*u Z) =
      b Z*(hyperbolic u Z-μ*u Z)+star (hyperbolic b Z)*u Z-2*hyperbolicEnergy b u Z := by
  have he := hyperbolic_product_star hb hu hZ
  have hfun : (fun W => star (b W)*u W)=fun W => b W*u W := by
    funext W
    rw [hreal W]
  rw [hfun,hreal Z] at he
  rw [he]
  ring

/-- Squared differential residual bound, with no hidden spectral or
regularity assumption on the function being localized. -/
theorem hyperbolic_cutoff_residual_norm_sq (b u : Point → ℂ)
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2})
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hreal : ∀ W, star (b W)=b W) (μ : ℂ) (Z : Point) (hZ : 0<Z.2)
    (B H C : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hbZ : ‖b Z‖ ≤ B) (hΔ : ‖hyperbolic b Z‖ ≤ H)
    (hgrad : (hyperbolicEnergy b b Z).re ≤ C^2) :
    ‖hyperbolic (fun W => b W*u W) Z-μ*(b Z*u Z)‖^2 ≤
      3*(B^2*‖hyperbolic u Z-μ*u Z‖^2+H^2*‖u Z‖^2+
        4*C^2*(hyperbolicEnergy u u Z).re) := by
  rw [hyperbolic_cutoff_residual b u hb hu hreal μ Z hZ,sub_eq_add_neg]
  have he := norm_three_terms_sq (b Z*(hyperbolic u Z-μ*u Z))
    (star (hyperbolic b Z)*u Z) (-(2*hyperbolicEnergy b u Z))
  simp only [norm_mul,norm_star,norm_neg,mul_pow] at he
  norm_num only [Complex.norm_ofNat] at he
  have hb2 := (sq_le_sq₀ (norm_nonneg _) hB).mpr hbZ
  have hΔ2 := (sq_le_sq₀ (norm_nonneg _) hH).mpr hΔ
  have hcross := (hyperbolicEnergy_norm_sq_le b u Z).trans
    (mul_le_mul_of_nonneg_right hgrad (hyperbolicEnergy_self_nonneg u Z))
  have h1 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖hyperbolic u Z-μ*u Z‖)
  have h2 := mul_le_mul_of_nonneg_right hΔ2 (sq_nonneg ‖u Z‖)
  nlinarith

#print axioms hyperbolicEnergy_norm_sq_le
#print axioms hyperbolic_cutoff_residual
#print axioms hyperbolic_cutoff_residual_norm_sq

end QuantitativeMaass
