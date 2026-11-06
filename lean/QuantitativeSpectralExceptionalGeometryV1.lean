module

public import QuantitativeSpectralExceptionalReducedRowsV1
public import QuantitativeSpectralObservabilityReductionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open UpperHalfPlane Set MeasureTheory AsymptoticRegularBranchFamily
open AsymptoticCongruenceLabels AsymptoticRationalBranches
open QuantitativeSpectralExceptionalReducedRows QuantitativeSpectralFiniteReduction
open QuantitativeSpectralObservability
open scoped MatrixGroups

/-- Both height and reciprocal height are bounded on a fixed compact source.
The bound also works when the source is empty. -/
theorem compact_height_band {s : Set ℍ} (hs : IsCompact s) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ s, B⁻¹ ≤ z.im ∧ z.im ≤ B := by
  have hc : Continuous (fun z : ℍ => z.im + z.im⁻¹) :=
    continuous_im.add (continuous_im.inv₀ (fun z => z.im_pos.ne'))
  obtain ⟨C,hC⟩ := hs.bddAbove_image hc.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  have hh : z.im + z.im⁻¹ ≤ max C 1 :=
    (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hi : z.im⁻¹ ≤ max C 1 := by linarith [z.im_pos]
  exact ⟨(inv_le_comm₀ z.im_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _))).mp hi,
    by linarith [inv_pos.mpr z.im_pos]⟩

variable {ι : Type*} [Fintype ι]

/-- The fixed compact union of the actual rational branch images. -/
def branchImages (b : ι → Branch) (s : Set ℍ) : Set ℍ := ⋃ i, image (b i) s

theorem branchImages_compact (b : ι → Branch) {s : Set ℍ} (hs : IsCompact s) :
    IsCompact (branchImages b s) := isCompact_iUnion (fun i => image_compact (b i) hs)

/-- A piece is defined by literal membership of every reduced branch image
in the fixed open cover. Its definition is independent of the later cutoff. -/
def piece (N : ℕ) (b : ι → Branch) (s : Set ℍ) (w : ι → List SL(2,ℤ)) : Set ℍ :=
  s ∩ ⋂ i, (fun z => (integralLabel (w i).prod * label (b i)) • z) ⁻¹' openCover N

theorem piece_measurable (N : ℕ) (b : ι → Branch) {s : Set ℍ} (hs : MeasurableSet s)
    (w : ι → List SL(2,ℤ)) : MeasurableSet (piece N b s w) := by
  exact hs.inter (MeasurableSet.iInter (fun i =>
    ((openCover_open N).preimage (action_continuous _)).measurableSet))

/-- On a fixed compact source, one finite set of actual generator words
and one height threshold work simultaneously for every rational branch.
Neither the words nor their open-cover pieces depend on H. -/
theorem finite_compact_branch_reduction (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : ι → Branch) {s : Set ℍ} (hs : IsCompact s) :
    ∃ W : Finset (List SL(2,ℤ)), ∃ B : ℝ, 0 < B ∧
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      (∀ z ∈ s, ∃ w : ι → List SL(2,ℤ), (∀ i, w i ∈ W) ∧ z ∈ piece N b s w) ∧
      ∀ w : ι → List SL(2,ℤ), ∀ H : ℝ, B ≤ H →
        ∀ z ∈ piece N b s w, ∀ i,
          (integralLabel (w i).prod * label (b i)) • z ∈ wideCompactCover N H := by
  classical
  have hk := branchImages_compact b hs
  obtain ⟨W,hW,hr⟩ := finite_reduction_words N S hS hk
  obtain ⟨B,hB,hband⟩ := compact_height_band hk
  refine ⟨W,B,hB,hW,?_,?_⟩
  · intro z hz
    have hi (i : ι) : label (b i) • z ∈ branchImages b s :=
      mem_iUnion.mpr ⟨i,mem_image_of_mem _ hz⟩
    choose w hw hcover using fun i => hr _ (hi i)
    refine ⟨w,hw,hz,?_⟩
    exact mem_iInter.mpr (fun i => by simpa only [mem_preimage,mul_smul] using hcover i)
  · intro w H hH z hz i
    have hi : label (b i) • z ∈ branchImages b s :=
      mem_iUnion.mpr ⟨i,mem_image_of_mem _ hz.1⟩
    have ho : integralLabel (w i).prod • (label (b i) • z) ∈ openCover N := by
      simpa only [mem_preimage,mul_smul] using mem_iInter.mp hz.2 i
    have hh : (B⁻¹)⁻¹ ≤ H := by simpa only [inv_inv] using hH
    simpa only [mul_smul] using reduced_mem_wideCompactCover N (w i).prod
      (inv_pos.mpr hB) hh (label (b i) • z) (hband _ hi).1 ((hband _ hi).2.trans hH) ho

#print axioms compact_height_band
#print axioms finite_compact_branch_reduction

end QuantitativeSpectralExceptionalGeometry
