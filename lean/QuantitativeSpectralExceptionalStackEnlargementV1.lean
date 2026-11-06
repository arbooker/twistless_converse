module

public import QuantitativeSpectralExceptionalStackRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane Set ContinuousLinearMap AsymptoticObservationStack AsymptoticOrbitDiagonal
open AsymptoticRegularBranchFamily QuantitativeSpectralWordDefect
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

variable {J : Type*} [Fintype J] {I K : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, Fintype (K j)]

/-- All original rational rows and the actual fixed generator defects,
observed on one compact region. This is a literal finite stack. -/
def enlargedRows (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch) (c : ∀ j, I j → ℂ)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    J ⊕ ↥A → Space →L[ℂ] Space
  | Sum.inl j => family (b j) (c j) hu hε t x
  | Sum.inr a => AsymptoticCongruenceDefect.operator a.val hu hε t x

/-- The extra compact region can include the terminal word region needed
by observability. Every rational-row source and every intermediate word
image is included by construction. -/
def enlargedRegion (b : ∀ j, I j → Branch) (w : ∀ j, K j → I j → List SL(2,ℤ))
    (s : J → Set ℍ) (v : Set ℍ) : Set ℍ :=
  v ∪ ⋃ j, (s j ∪ commonRegion (b j) (w j) (s j))

theorem enlargedRegion_compact (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (s : J → Set ℍ)
    (hs : ∀ j, IsCompact (s j)) {v : Set ℍ} (hv : IsCompact v) :
    IsCompact (enlargedRegion b w s v) :=
  hv.union (isCompact_iUnion (fun j => (hs j).union (commonRegion_compact (b j) (w j) (hs j))))

omit [Fintype J] [∀ j, Fintype (I j)] [∀ j, Fintype (K j)] in
theorem source_subset_enlarged (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (s : J → Set ℍ) (v : Set ℍ) (j : J) :
    s j⊆enlargedRegion b w s v :=
  fun _ hz => Or.inr (mem_iUnion.mpr ⟨j,Or.inl hz⟩)

omit [Fintype J] [∀ j, Fintype (I j)] [∀ j, Fintype (K j)] in
theorem common_subset_enlarged (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (s : J → Set ℍ) (v : Set ℍ) (j : J) :
    commonRegion (b j) (w j) (s j)⊆enlargedRegion b w s v :=
  fun _ hz => Or.inr (mem_iUnion.mpr ⟨j,Or.inr hz⟩)

/-- Exact restriction from the single enlarged stack to any row's actual
common residual stack. There is no residual-smallness hypothesis. -/
theorem commonResidualStack_enlarged (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (c : ∀ j, I j → ℂ)
    (s : J → Set ℍ) (hs : ∀ j, IsCompact (s j)) {v : Set ℍ} (hv : IsCompact v)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (j : J) :
    (stackRestriction A j (s j) (commonRegion (b j) (w j) (s j)) x).comp
      (stack (enlargedRows A b c (enlargedRegion_compact b w s hs hv) hε t x)) =
        commonResidualStack A (b j) (w j) (c j) (hs j) hε t x := by
  apply ContinuousLinearMap.ext
  intro f
  ext1 o
  cases o with
  | none =>
    change corner (s j) x (family (b j) (c j) (enlargedRegion_compact b w s hs hv) hε t x f) =
      family (b j) (c j) (hs j) hε t x f
    exact congrArg (fun T : Space →L[ℂ] Space => T f)
      (family_restrict (b j) (c j) (hs j) (enlargedRegion_compact b w s hs hv)
        (source_subset_enlarged b w s v j) hε t x)
  | some a =>
    change corner (commonRegion (b j) (w j) (s j)) x
      (AsymptoticCongruenceDefect.operator a.val (enlargedRegion_compact b w s hs hv) hε t x f) =
      AsymptoticCongruenceDefect.operator a.val (commonRegion_compact (b j) (w j) (hs j)) hε t x f
    exact congrArg (fun T : Space →L[ℂ] Space => T f)
      (defect_restrict (commonRegion_compact (b j) (w j) (hs j))
        (enlargedRegion_compact b w s hs hv) (common_subset_enlarged b w s v j) a.val hε t x)

/-- Enlarging all compact regions and retaining all original rows controls
each actual common residual stack with constant one. -/
theorem commonResidualStack_norm_le_enlarged (A : Finset SL(2,ℤ)) (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (c : ∀ j, I j → ℂ)
    (s : J → Set ℍ) (hs : ∀ j, IsCompact (s j)) {v : Set ℍ} (hv : IsCompact v)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (j : J) (f : Space) :
    ‖commonResidualStack A (b j) (w j) (c j) (hs j) hε t x f‖≤
      ‖stack (enlargedRows A b c (enlargedRegion_compact b w s hs hv) hε t x) f‖ := by
  rw [←commonResidualStack_enlarged A b w c s hs hv hε t x j,comp_apply]
  simpa only [one_mul] using (stackRestriction A j (s j) (commonRegion (b j) (w j) (s j)) x).le_of_opNorm_le
    (stackRestriction_norm A j (s j) (commonRegion (b j) (w j) (s j)) x) _

#print axioms commonResidualStack_enlarged
#print axioms commonResidualStack_norm_le_enlarged

end QuantitativeSpectralExceptionalReducedRows
