module

public import QuantitativeSpectralExceptionalUnweightV1
public import QuantitativeSpectralObservabilityDecodedV1
public import AsymptoticCongruenceDefectV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticRegularBranchFamily AsymptoticOrbitDecode AsymptoticRationalBranches
open AsymptoticRationalFreeness AsymptoticCongruenceLabels
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralObservability QuantitativeSpectralObservabilityDecoded
open scoped lp MatrixGroups

attribute [local instance] Classical.propDecidable

abbrev label (b : Branch) : G := ofMatrix b.matrix b.positive

def image (b : Branch) (s : Set ℍ) : Set ℍ := (fun z => label b • z) '' s

theorem image_compact (b : Branch) {s : Set ℍ} (hs : IsCompact s) : IsCompact (image b s) :=
  hs.image (action_continuous _)

/-- Full orbit pullback; it does not refold an already formed defect. -/
def pull (a : G) : Space →L[ℂ] Space :=
  (AsymptoticOrbitBranch.reindex (Equiv.mulLeft a)).toContinuousLinearMap

theorem pull_apply (a : G) (v : Space) (g : G) : pull a v g = v (a*g) := rfl

theorem pull_norm (a : G) : ‖pull a‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change ‖(AsymptoticOrbitBranch.reindex (Equiv.mulLeft a)) v‖ ≤ 1 * ‖v‖
  rw [LinearIsometry.norm_map, one_mul]

/-- The actual compact branch after removing its output cap. -/
def rawBranch (b : Branch) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (D : QuantitativeSpectralExceptionalUnweight.Data s ε t) (x : ℍ) :
    Space →L[ℂ] Space :=
  (QuantitativeSpectralExceptionalUnweight.unweight hε t D x).comp (compact b hs hε t x)

theorem rawBranch_apply (b : Branch) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (D : QuantitativeSpectralExceptionalUnweight.Data s ε t) (x : ℍ) (v : Space) (g : G) :
    rawBranch b hs hε t D x v g =
      if g • x ∈ s then decode ε t x v (label b*g) else 0 := by
  classical
  rw [rawBranch, comp_apply, QuantitativeSpectralExceptionalUnweight.unweight_apply, compact_decode]
  by_cases hg : g • x ∈ s
  · simp only [QuantitativeSpectralExceptionalUnweight.coefficient, Set.indicator_of_mem hg,
      ite_eq_left hg]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (AsymptoticCompactBranch.cap_pos hε t _).ne']
    simp
  · simp only [QuantitativeSpectralExceptionalUnweight.coefficient, Set.indicator_of_notMem hg,
      ite_eq_right hg, zero_mul]

/-- A genuine transported modular defect at the branch image. -/
def correction (b : Branch) (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : QuantitativeSpectralExceptionalUnweight.Data (image b s) ε t) (x : ℍ) :
    Space →L[ℂ] Space :=
  (pull (label b)).comp ((QuantitativeSpectralExceptionalUnweight.unweight hε t D x).comp
    (AsymptoticCongruenceDefect.operator γ (image_compact b hs) hε t x))

theorem correction_apply (b : Branch) (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : QuantitativeSpectralExceptionalUnweight.Data (image b s) ε t)
    (x : ℍ) (v : Space) (g : G) (hg : g • x ∈ s) :
    correction b γ hs hε t D x v g =
      decode ε t x v ((integralLabel γ * label b)*g) - decode ε t x v (label b*g) := by
  have hb : (label b*g) • x ∈ image b s := ⟨g • x,hg,(mul_smul _ _ _).symm⟩
  rw [correction, comp_apply, pull_apply, comp_apply,
    QuantitativeSpectralExceptionalUnweight.unweight_apply, AsymptoticCongruenceDefect.operator_decode]
  simp only [QuantitativeSpectralExceptionalUnweight.coefficient, Set.indicator_of_mem hb,
    ite_eq_left hb]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (AsymptoticCompactBranch.cap_pos hε t _).ne']
  simp only [Complex.ofReal_one, one_mul, mul_assoc]

theorem correction_norm (b : Branch) (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : QuantitativeSpectralExceptionalUnweight.Data (image b s) ε t) (x : ℍ) :
    ‖correction b γ hs hε t D x‖ ≤
      D.bound * AsymptoticCongruenceDefect.bound γ (image_compact b hs) hε t := by
  have h1 : ‖(QuantitativeSpectralExceptionalUnweight.unweight hε t D x).comp
      (AsymptoticCongruenceDefect.operator γ (image_compact b hs) hε t x)‖ ≤
      D.bound * AsymptoticCongruenceDefect.bound γ (image_compact b hs) hε t :=
    (opNorm_comp_le _ _).trans (mul_le_mul
      (QuantitativeSpectralExceptionalUnweight.unweight_norm hε t D x)
      (AsymptoticCongruenceDefect.operator_norm_le γ (image_compact b hs) hε t x)
      (norm_nonneg _) D.bound_nonneg)
  exact (opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_right (pull_norm _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using h1))

/-- Retained reduced branch values equal the literal compact residual
plus a bounded transported generator defect. The only reduction premise
is geometric membership in the actual sampling set. -/
theorem retained_branch_identity (N : ℕ) (hN : 0 < N) (H : ℝ)
    (b : Branch) (γ : SL(2,ℤ)) {s E : Set ℍ} (hs : IsCompact s) (hEs : E ⊆ s)
    (hred : ∀ z ∈ E, (integralLabel γ * label b) • z ∈ wideCompactCover N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : QuantitativeSpectralExceptionalUnweight.Data (image b s) ε t) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner E x).comp
      ((pull (integralLabel γ * label b)).comp (sampling N hN H hε t x)) =
    (AsymptoticOrbitDiagonal.corner E x).comp
      (rawBranch b hs hε t Ds x + correction b γ hs hε t Db x) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  simp only [comp_apply, AsymptoticOrbitDiagonal.corner_apply]
  by_cases hg : g • x ∈ E
  · rw [ite_eq_left hg, ite_eq_left hg, pull_apply, sampling_decode]
    have hr : ((integralLabel γ * label b)*g) • x ∈ wideCompactCover N H := by
      rw [mul_smul]
      exact hred _ hg
    rw [ite_eq_left hr]
    change _ = rawBranch b hs hε t Ds x v g + correction b γ hs hε t Db x v g
    rw [rawBranch_apply, ite_eq_left (hEs hg), correction_apply b γ hs hε t Db x v g (hEs hg)]
    ring
  · simp only [ite_eq_right hg]

#print axioms rawBranch_apply
#print axioms correction_norm
#print axioms retained_branch_identity

end QuantitativeSpectralExceptionalReducedRows
