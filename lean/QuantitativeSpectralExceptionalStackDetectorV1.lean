module

public import QuantitativeSpectralExceptionalStackObservabilityV1
public import AsymptoticRegularStackPolarV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticObservationStack
open AsymptoticRegularBranchFamily AsymptoticRegularTrace AsymptoticPolarIsometry
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

def enlargedRowBound (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch) (c : ∀ j, I j → ℂ)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) (t : ℕ) : J ⊕ ↥A → ℝ
  | Sum.inl j => familyBound (b j) (c j) hu hε t
  | Sum.inr a => AsymptoticCongruenceDefect.bound a.val hu hε t

omit [Fintype J] in
theorem enlargedRowBound_nonneg (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch) (c : ∀ j, I j → ℂ)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : J ⊕ ↥A) :
    0≤enlargedRowBound A b c hu hε t a := by
  cases a with
  | inl j => exact familyBound_nonneg (b j) (c j) hu hε t
  | inr a => exact add_nonneg (bound_nonneg _ hu hε t) (bound_nonneg _ hu hε t)

omit [Fintype J] in
theorem enlargedRows_regular (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch) (c : ∀ j, I j → ℂ)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : J ⊕ ↥A) :
    (∀ g h, Measurable (fun x => matrix (enlargedRows A b c hu hε t x a) g h)) ∧
      Covariant (fun x => enlargedRows A b c hu hε t x a) := by
  cases a with
  | inl j => exact ⟨family_matrix_measurable (b j) (c j) hu hε t,
      family_covariant (b j) (c j) hu hε t⟩
  | inr a => exact AsymptoticCongruenceDefect.operator_regular a.val hu hε t

/-- A concrete uniform bound for the enlarged finite stack at fixed compact
cutoff. It is computed from the bounds of its actual rows. -/
theorem enlargedStack_bounded (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch) (c : ∀ j, I j → ℂ)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ x, ‖stack (enlargedRows A b c hu hε t x)‖≤M := by
  let M := ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : J ⊕ ↥A => Space)).symm.toContinuousLinearMap‖*
    ∑ a, enlargedRowBound A b c hu hε t a
  refine ⟨M,mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun a _ =>
    enlargedRowBound_nonneg A b c hu hε t a)),?_⟩
  intro x
  apply stack_norm_le _ _ (enlargedRowBound_nonneg A b c hu hε t)
  intro a
  cases a with
  | inl j => exact family_norm_le (b j) (c j) hu hε t x
  | inr a => exact AsymptoticCongruenceDefect.operator_norm_le a.val hu hε t x

/-- The square detector required by the existing spectral-cut API is the
actual absolute value of the constructed finite stack. -/
def enlargedDetector (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch) (c : ∀ j, I j → ℂ)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  absolute (stack (enlargedRows A b c hu hε t x))

theorem enlargedDetector_norm_apply (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch) (c : ∀ j, I j → ℂ)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space) :
    ‖enlargedDetector A b c hu hε t x f‖=‖stack (enlargedRows A b c hu hε t x) f‖ :=
  (absolute_norm _ _).symm

theorem enlargedDetector_regular (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch) (c : ∀ j, I j → ℂ)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    ∃ M : ℝ, 0≤M ∧ (∀ x, ‖enlargedDetector A b c hu hε t x‖≤M) ∧
      (∀ g h, Measurable (fun x => matrix (enlargedDetector A b c hu hε t x) g h)) ∧
      Covariant (enlargedDetector A b c hu hε t) := by
  obtain ⟨M,hM,hbound⟩ := enlargedStack_bounded A b c hu hε t
  have hr := stack_absolute_regular (fun x => enlargedRows A b c hu hε t x)
    (fun a => (enlargedRows_regular A b c hu hε t a).1)
    (fun a => (enlargedRows_regular A b c hu hε t a).2) M hbound
  refine ⟨M,hM,?_,hr.1,hr.2⟩
  intro x
  simpa only [enlargedDetector,absolute_opNorm] using hbound x

#print axioms enlargedStack_bounded
#print axioms enlargedDetector_norm_apply
#print axioms enlargedDetector_regular

end QuantitativeSpectralExceptionalReducedRows
