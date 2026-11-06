module

public import QuantitativeSpectralExceptionalRecombineV1
public import QuantitativeSpectralWordDefectV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticRegularBranchFamily
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralWordDefect
open scoped lp MatrixGroups

theorem correction_apply_norm (b : Branch) (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : QuantitativeSpectralExceptionalUnweight.Data (image b s) ε t) (x : ℍ) (v : Space) :
    ‖correction b γ hs hε t D x v‖ ≤
      D.bound * ‖AsymptoticCongruenceDefect.operator γ (image_compact b hs) hε t x v‖ := by
  have hu := (QuantitativeSpectralExceptionalUnweight.unweight hε t D x).le_of_opNorm_le
    (QuantitativeSpectralExceptionalUnweight.unweight_norm hε t D x)
    (AsymptoticCongruenceDefect.operator γ (image_compact b hs) hε t x v)
  exact ((pull (label b)).le_of_opNorm_le (pull_norm _)
    (QuantitativeSpectralExceptionalUnweight.unweight hε t D x
      (AsymptoticCongruenceDefect.operator γ (image_compact b hs) hε t x v))).trans
    (by simpa only [one_mul] using hu)

/-- A reducing word correction is controlled by the actual generator
observations on one explicitly specified common compact region. -/
theorem correction_word_bound (b : Branch) (w : List SL(2,ℤ))
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u)
    (hsub : region w (image b s) ⊆ u) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : QuantitativeSpectralExceptionalUnweight.Data (image b s) ε t)
    (x : ℍ) (v : Space) (d : ℝ)
    (hd : ∀ a ∈ w, ‖AsymptoticCongruenceDefect.operator a hu hε t x v‖ ≤ d) :
    ‖correction b w.prod hs hε t D x v‖ ≤ D.bound * cost w (image_compact b hs) hε t * d := by
  have hw := word_norm_of_generator_bound w (image_compact b hs) hu hsub hε t x v d hd
  exact (correction_apply_norm b w.prod hs hε t D x v).trans
    ((mul_le_mul_of_nonneg_left hw D.bound_nonneg).trans_eq (mul_assoc _ _ _).symm)

variable {ι : Type*} [Fintype ι]

/-- Finite recombination uses only the fixed-generator residual bound;
it does not assume that the reducing matrices already act invariantly. -/
theorem correctionFamily_word_bound (b : ι → Branch) (w : ι → List SL(2,ℤ)) (c : ι → ℂ)
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u)
    (hsub : ∀ i, region (w i) (image (b i) s) ⊆ u) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t)
    (x : ℍ) (v : Space) (d : ℝ)
    (hd : ∀ i a, a ∈ w i → ‖AsymptoticCongruenceDefect.operator a hu hε t x v‖ ≤ d) :
    ‖correctionFamily b (fun i => (w i).prod) c hs hε t D x v‖ ≤
      (∑ i, ‖c i‖ * (D i).bound * cost (w i) (image_compact (b i) hs) hε t) * d := by
  rw [correctionFamily, _root_.sum_apply, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [smul_apply, norm_smul]
  have hh := correction_word_bound (b i) (w i) hs hu (hsub i) hε t (D i) x v d (hd i)
  exact (mul_le_mul_of_nonneg_left hh (norm_nonneg (c i))).trans_eq (by ring)

#print axioms correction_word_bound
#print axioms correctionFamily_word_bound

end QuantitativeSpectralExceptionalReducedRows
