module

public import QuantitativeNinaMaassMellinSeriesV1
public import QuantitativeMaassEulerPhysicalAxisV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Complex QuantitativeMaass
open scoped Topology ContDiff

/-!
The forward analytic direction: a physical Fricke eigenrelation for the
literal Fourier--Bessel wave gives the original entire finite-order
functional equation. The odd root has the opposite sign, coming from
the actual normal derivative of the Fricke coordinate map.
-/

namespace QuantitativeNinaMaass

theorem eulerWave_fricke_normal {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (L : ℝ) (hL : 0 < L) (r : ℝ) (δ : ℕ) (χ : ℂ)
    (hfr : ∀ x y : ℝ, 0 < y → principalEulerWave b r δ (x, y) =
      χ * principalEulerWave b r δ (MaassDifferential.F L x y))
    (y : ℝ) (hy : 0 < y) :
    deriv (fun x => principalEulerWave b r δ (x, y)) 0 =
      χ * (((-1 / (L * y ^ 2) : ℝ) : ℂ) *
        deriv (fun x => principalEulerWave b r δ (x, 1 / (L * y))) 0) := by
  have hf := principalEulerWave_contDiffOn hb r δ
  have hU : IsOpen {z : ℝ × ℝ | 0 < z.2} := isOpen_lt continuous_const continuous_snd
  have he : (fun x => principalEulerWave b r δ (x, y)) =
      fun x => χ * MaassDifferential.pullback L (principalEulerWave b r δ) (x, y) :=
    funext (fun x => hfr x y hy)
  rw [he, deriv_const_mul_field]
  rw [planeDerivative_horizontal (fricke_pullback_contDiffOn hf L hL) hU 0 y hy,
    fricke_normal_axis hf L y hL hy,
    ← planeDerivative_horizontal hf hU 0 (1 / (L * y))
      (by change 0 < 1 / (L * y); positivity)]

theorem eulerWave_fricke_oddAxis {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (L : ℝ) (hL : 0 < L) (r : ℝ) (χ : ℂ)
    (hfr : ∀ x y : ℝ, 0 < y → principalEulerWave b r 1 (x, y) =
      χ * principalEulerWave b r 1 (MaassDifferential.F L x y))
    (y : ℝ) (hy : 0 < y) :
    principalEulerOddAxis b r y = -χ * principalEulerOddAxis b r (1 / (L * y)) := by
  have h := eulerWave_fricke_normal hb L hL r 1 χ hfr y hy
  unfold principalEulerOddAxis
  rw [h]
  push_cast
  have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hLC : (L : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL.ne'
  field_simp

theorem axisSum_inversion_of_sqrt_relation (L r : ℝ) (δ : ℕ) (b : ℕ → ℂ)
    (ε : ℂ) (l : ℝ)
    (hrel : (Real.sqrt (principalEulerHeight L l) : ℂ) *
        MaassOriginal.axisSum L (.principal r) δ b l =
      ε * (Real.sqrt (principalEulerHeight L (-l)) : ℂ) *
        MaassOriginal.axisSum L (.principal r) δ b (-l)) :
    MaassOriginal.axisSum L (.principal r) δ b l =
      ε * (Real.exp (-l) : ℂ) * MaassOriginal.axisSum L (.principal r) δ b (-l) := by
  have hs : (Real.sqrt (principalEulerHeight L l) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (principalEulerHeight_pos L l)).ne'
  have hbalance : (Real.sqrt (principalEulerHeight L (-l)) : ℂ) =
      (Real.sqrt (principalEulerHeight L l) : ℂ) * (Real.exp (-l) : ℂ) := by
    rw [← ofReal_mul, principalEulerHeight_sqrt_balance]
  apply mul_left_cancel₀ hs
  calc
    _ = _ := hrel
    _ = _ := by rw [hbalance]; ring

theorem eulerWave_even_axisSum_inversion {b : ℕ → ℂ}
    (L : ℝ) (hL : 0 < L) (r : ℝ) (χ : ℂ)
    (hfr : ∀ x y : ℝ, 0 < y → principalEulerWave b r 0 (x, y) =
      χ * principalEulerWave b r 0 (MaassDifferential.F L x y)) (l : ℝ) :
    MaassOriginal.axisSum L (.principal r) 0 b l =
      χ * (Real.exp (-l) : ℂ) * MaassOriginal.axisSum L (.principal r) 0 b (-l) := by
  apply axisSum_inversion_of_sqrt_relation L r 0 b χ l
  have h := hfr 0 (principalEulerHeight L l) (principalEulerHeight_pos L l)
  rw [fricke_axis L _ hL (principalEulerHeight_pos L l),
    ← principalEulerHeight_inverse L hL l] at h
  rw [principalEuler_even_axisSum, principalEuler_even_axisSum]
  unfold principalEulerWave at h
  linear_combination 2 * h

theorem eulerWave_odd_axisSum_inversion {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0 < L) (r : ℝ) (χ : ℂ)
    (hfr : ∀ x y : ℝ, 0 < y → principalEulerWave b r 1 (x, y) =
      χ * principalEulerWave b r 1 (MaassDifferential.F L x y)) (l : ℝ) :
    MaassOriginal.axisSum L (.principal r) 1 b l =
      -χ * (Real.exp (-l) : ℂ) * MaassOriginal.axisSum L (.principal r) 1 b (-l) := by
  apply axisSum_inversion_of_sqrt_relation L r 1 b (-χ) l
  have h := eulerWave_fricke_oddAxis hb L hL r χ hfr
    (principalEulerHeight L l) (principalEulerHeight_pos L l)
  rw [← principalEulerHeight_inverse L hL l,
    principalEulerOddAxis_eq_axisSum hb, principalEulerOddAxis_eq_axisSum hb] at h
  linear_combination 2 * h

theorem eulerWave_axisSum_inversion {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0 < L) (r : ℝ)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (χ : ℂ)
    (hfr : ∀ x y : ℝ, 0 < y → principalEulerWave b r δ (x, y) =
      χ * principalEulerWave b r δ (MaassDifferential.F L x y)) (l : ℝ) :
    MaassOriginal.axisSum L (.principal r) δ b l =
      ((-1 : ℂ) ^ δ * χ) * (Real.exp (-l) : ℂ) *
        MaassOriginal.axisSum L (.principal r) δ b (-l) := by
  rcases hδ with rfl | rfl
  · simpa only [pow_zero, one_mul] using eulerWave_even_axisSum_inversion L hL r χ hfr l
  · simpa only [pow_one, neg_one_mul] using eulerWave_odd_axisSum_inversion hb L hL r χ hfr l

/-- The original completed-series continuation, with its exact parity
Gamma factors, follows from the physical wave and its Fricke eigenrelation. -/
theorem eulerWave_continuation_of_fricke {b : ℕ → ℂ}
    (hb : MaassOriginal.PolynomialGrowth b) (L : ℝ) (hL : 0 < L) (r : ℝ)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (χ : ℂ) (hχ : χ ≠ 0)
    (hfr : ∀ x y : ℝ, 0 < y → principalEulerWave b r δ (x, y) =
      χ * principalEulerWave b r δ (MaassDifferential.F L x y)) :
    MaassOriginal.Continuation L (.principal r) δ b ((-1 : ℂ) ^ δ * χ) := by
  apply parityMellinAxis_continuation hL hb r δ _
    (mul_ne_zero (pow_ne_zero δ (neg_ne_zero.mpr one_ne_zero)) hχ)
  intro t ht
  rw [parityMellinAxis_log L (.principal r) δ b (1 / t) (by positivity),
    parityMellinAxis_log L (.principal r) δ b t ht, one_div, Real.log_inv]
  have h := eulerWave_axisSum_inversion hb L hL r δ hδ χ hfr (-Real.log t)
  simpa only [neg_neg, Real.exp_log ht, mul_assoc] using h

#print axioms eulerWave_fricke_normal
#print axioms eulerWave_fricke_oddAxis
#print axioms axisSum_inversion_of_sqrt_relation
#print axioms eulerWave_even_axisSum_inversion
#print axioms eulerWave_odd_axisSum_inversion
#print axioms eulerWave_axisSum_inversion
#print axioms eulerWave_continuation_of_fricke

end QuantitativeNinaMaass
