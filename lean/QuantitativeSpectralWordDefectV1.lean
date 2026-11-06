module

public import QuantitativeSpectralDefectCocycleV1
public import AsymptoticCompactRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralWordDefect

open Matrix UpperHalfPlane ContinuousLinearMap AsymptoticCongruenceLabels
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch AsymptoticRationalFreeness
open QuantitativeSpectralDefectCocycle
open scoped MatrixGroups Classical

def region : List SL(2,ℤ) → Set ℍ → Set ℍ
  | [],s => s
  | _::l,s => region l s ∪ image l.prod s

theorem region_compact (l : List SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s) :
    IsCompact (region l s) := by
  induction l with
  | nil => exact hs
  | cons a l ih => exact ih.union (image_compact l.prod hs)

def cost : List SL(2,ℤ) → {s : Set ℍ} → IsCompact s → {ε : ℝ} →
    (0 < ε) → ℕ → ℝ
  | [],_,_,_,_,_ => 0
  | _::l,_,hs,_,hε,t => cost l hs hε t + (data (realMatrix (rationalGL l.prod)) hs hε t).bound

theorem cost_nonneg (l : List SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) : 0 ≤ cost l hs hε t := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact add_nonneg ih (data _ hs hε t).bound_nonneg

theorem defect_one {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (x : ℍ) : AsymptoticCongruenceDefect.operator 1 hs hε t x=0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  simp [AsymptoticCongruenceDefect.operator_decode,map_one]

theorem defect_restrict {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u)
    (hsub : s ⊆ u) (a : SL(2,ℤ)) {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner s x).comp (AsymptoticCongruenceDefect.operator a hu hε t x) =
      AsymptoticCongruenceDefect.operator a hs hε t x := by
  simp only [AsymptoticCongruenceDefect.operator,comp_sub,
    AsymptoticRegularBranchFamily.compact_restrict _ hs hu hsub hε t x]

theorem defect_restrict_norm {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u)
    (hsub : s ⊆ u) (a : SL(2,ℤ)) {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖AsymptoticCongruenceDefect.operator a hs hε t x v‖ ≤
      ‖AsymptoticCongruenceDefect.operator a hu hε t x v‖ := by
  rw [← defect_restrict hs hu hsub a hε t x,ContinuousLinearMap.comp_apply]
  simpa only [one_mul] using (AsymptoticOrbitDiagonal.corner s x).le_of_opNorm_le
    (AsymptoticOrbitRegion.corner_norm_le s x) (AsymptoticCongruenceDefect.operator a hu hε t x v)

/-- Finite-word telescoping on one explicitly constructed compact region.
Every residual on the right is a literal generator observation. -/
theorem word_norm_of_generator_bound (l : List SL(2,ℤ)) {s u : Set ℍ}
    (hs : IsCompact s) (hu : IsCompact u) (hsub : region l s ⊆ u)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) (v : Space) (D : ℝ)
    (hD : ∀ a ∈ l, ‖AsymptoticCongruenceDefect.operator a hu hε t x v‖ ≤ D) :
    ‖AsymptoticCongruenceDefect.operator l.prod hs hε t x v‖ ≤ cost l hs hε t * D := by
  induction l with
  | nil => simp [cost,defect_one]
  | cons a l ih =>
    have hi := ih (fun z hz => hsub (Or.inl hz))
      (fun b hb => hD b (List.mem_cons_of_mem a hb))
    have ha := (defect_restrict_norm (image_compact l.prod hs) hu
      (fun z hz => hsub (Or.inr hz)) a hε t x v).trans (hD a List.mem_cons_self)
    apply (defect_mul_norm a l.prod hs hε t x v).trans
    dsimp only [cost]
    calc
      _ ≤ cost l hs hε t*D + (data (realMatrix (rationalGL l.prod)) hs hε t).bound*D :=
        add_le_add hi (mul_le_mul_of_nonneg_left ha (data _ hs hε t).bound_nonneg)
      _ = _ := by ring

theorem word_norm (l : List SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖AsymptoticCongruenceDefect.operator l.prod hs hε t x v‖ ≤
      cost l hs hε t * ∑ i : Fin l.length,
        ‖AsymptoticCongruenceDefect.operator (l.get i) (region_compact l hs) hε t x v‖ := by
  classical
  apply word_norm_of_generator_bound l hs (region_compact l hs) (Set.Subset.refl _) hε t x v
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
  exact Finset.single_le_sum (f := fun j : Fin l.length =>
    ‖AsymptoticCongruenceDefect.operator (l.get j) (region_compact l hs) hε t x v‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

#print axioms word_norm

end QuantitativeSpectralWordDefect
