module

public import QuantitativeSpectralObservabilityGeneratorsV1
public import QuantitativeHolomorphicCompactBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticCompactBranch QuantitativeHolomorphic
open QuantitativeSpectralDefectCocycle QuantitativeSpectralWordDefect
open scoped MatrixGroups BigOperators lp

def transportPolynomial (B H : ℝ) (t : ℕ) : ℝ := (max 1 (B^2*(H+3)^2))^t

theorem rectangle_ratio_bound (g : SL(2,ℤ)) {B ε H : ℝ}
    (hB : 1≤B) (hg : MatrixEntryBound g.val B) (hε : 0<ε) (t : ℕ)
    (z : ℍ) (hz : z∈terminalRectangle ε H) :
    ratio (realMatrix (rationalGL g)) ε t z ≤ transportPolynomial B H t := by
  have hH : 0<H+3 := by linarith [z.im_pos,hz.2.2.2]
  have hden : 0<B^2*(H+3)^2 := by positivity
  have hh := QuantitativeSpectralObservabilityUnweight.wide_modular_height_lower g
    (by linarith : 0≤B) hg z (abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2.1]⟩)
    (le_refl z.im) hz.2.2.2
  have hheight : z.im ≤ (B^2*(H+3)^2)*(g • z).im := by
    have h := (div_le_iff₀ hden).mp hh
    nlinarith
  have he : realMatrix (rationalGL g) • z = g • z := by
    rw [← integralLabel_action]
    exact (ofMatrix_action _ (rationalGL_positive g) z).symm
  apply compact_ratio_le_of_height _ hε (le_max_left _ _) t z
  rw [he]
  exact hheight.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (g • z).im_pos.le)

/-- The unrefolded cocycle transport has an explicit polynomial norm;
the compactness-chosen metadata in its definition do not affect its action. -/
theorem rectangle_transport_norm (g : SL(2,ℤ)) {B ε H : ℝ}
    (hB : 1≤B) (hg : MatrixEntryBound g.val B) (hε : 0<ε) (t : ℕ) (x : ℍ) :
    ‖transport g (terminalRectangle_compact hε H) hε t x‖≤transportPolynomial B H t := by
  have hC : 0≤transportPolynomial B H t := by unfold transportPolynomial; positivity
  have hc (z : ℍ) :
      ‖coefficient (realMatrix (rationalGL g)) (terminalRectangle ε H) ε t z‖≤
        transportPolynomial B H t := by
    classical
    by_cases hz : z∈terminalRectangle ε H
    · rw [coefficient,indicator_of_mem hz,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (ratio_pos _ hε t z)]
      exact rectangle_ratio_bound g hB hg hε t z hz
    · rw [coefficient,indicator_of_notMem hz,norm_zero]
      exact hC
  let T := AsymptoticOrbitBranch.operator (integralLabel g)
    (coefficient (realMatrix (rationalGL g)) (terminalRectangle ε H) ε t) hC hc x
  have he : transport g (terminalRectangle_compact hε H) hε t x=T := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext a
    rfl
  rw [he]
  exact AsymptoticOrbitBranch.operator_norm_le _ _ hC hc x

/-- An explicit common matrix bound for the suffix products in a word
gives a polynomial word-defect estimate on the original rectangle. -/
theorem word_norm_polynomial (l : List SL(2,ℤ)) {B ε H : ℝ}
    (hB : 1≤B) (hmat : ∀ k : ℕ, MatrixEntryBound (l.drop k).prod.val B)
    (hε : 0<ε) (t : ℕ) {u : Set ℍ} (hu : IsCompact u)
    (hsub : region l (terminalRectangle ε H) ⊆ u)
    (x : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) (D : ℝ)
    (hD : ∀ a∈l, ‖AsymptoticCongruenceDefect.operator a hu hε t x v‖≤D) :
    ‖AsymptoticCongruenceDefect.operator l.prod
      (terminalRectangle_compact hε H) hε t x v‖≤
        l.length*transportPolynomial B H t*D := by
  induction l with
  | nil => simp [defect_one]
  | cons a l ih =>
    have htail : ∀ k : ℕ, MatrixEntryBound (l.drop k).prod.val B := by
      intro k
      simpa only [List.drop_succ_cons] using hmat (k+1)
    have hi := ih htail (fun z hz => hsub (Or.inl hz))
      (fun b hb => hD b (List.mem_cons_of_mem a hb))
    have ha := (defect_restrict_norm
      (image_compact l.prod (terminalRectangle_compact hε H)) hu
      (fun z hz => hsub (Or.inr hz)) a hε t x v).trans (hD a List.mem_cons_self)
    rw [List.prod_cons,defect_mul,_root_.add_apply,ContinuousLinearMap.comp_apply]
    apply (norm_add_le _ _).trans
    have ht := (transport l.prod (terminalRectangle_compact hε H) hε t x).le_of_opNorm_le
      (rectangle_transport_norm l.prod hB (by simpa using htail 0) hε t x)
      (AsymptoticCongruenceDefect.operator a
        (image_compact l.prod (terminalRectangle_compact hε H)) hε t x v)
    have hC : 0≤transportPolynomial B H t := by unfold transportPolynomial; positivity
    have hh := add_le_add hi (ht.trans (mul_le_mul_of_nonneg_left ha hC))
    apply hh.trans_eq
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

#print axioms rectangle_transport_norm
#print axioms word_norm_polynomial

end QuantitativeSpectralObservability
