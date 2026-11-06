module

public import QuantitativeEulerEndpointEnlargementLabelsV1
public import QuantitativeSpectralObservabilityCoverV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode AsymptoticCongruenceLabels
open AsymptoticRegularBranchFamily QuantitativeSpectralExceptionalReducedRows
open QuantitativeSpectralObservability
open scoped Classical MatrixGroups Pointwise

def wideCoverLabels (N : ℕ) [NeZero N] : Finset G := by
  letI := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  exact Finset.univ.image (fun q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
    (integralLabel q.out)⁻¹)

theorem wideCompactCover_subset_labels (N : ℕ) [NeZero N] (H : ℝ) :
    wideCompactCover N H⊆labelRegion (wideCoverLabels N) (wideBox H) := by
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  intro z hz
  obtain ⟨q,y,hy,he⟩ := Set.mem_iUnion.mp hz
  refine ⟨(integralLabel q.out)⁻¹,?_,y,hy,he⟩
  exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩

variable {J : Type*} [Fintype J]

def sourceHeightScale (C : J → ℝ) : ℝ := 1+∑ j, |(C j)⁻¹|

theorem sourceHeightScale_one_le (C : J → ℝ) : 1≤sourceHeightScale C := by
  have hh := Finset.sum_nonneg (fun j (_ : j∈(Finset.univ : Finset J)) => abs_nonneg ((C j)⁻¹))
  unfold sourceHeightScale
  linarith

theorem sourceHeightScale_div (C : J → ℝ) (j : J) {H : ℝ} (hH : 0≤H) :
    H/C j≤sourceHeightScale C*H := by
  have hj := Finset.single_le_sum
    (fun i (_ : i∈(Finset.univ : Finset J)) => abs_nonneg ((C i)⁻¹)) (Finset.mem_univ j)
  have hc : (C j)⁻¹≤sourceHeightScale C := by
    unfold sourceHeightScale
    linarith [le_abs_self ((C j)⁻¹)]
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_right hc hH

variable {I K : J → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (K j)]

/-- Explicit geometry for the full enlargement used by the newspace
sampler: constants precede both epsilon and the sampling height. All finite
word/branch/coset labels are composed before the common height is selected. -/
theorem enlarged_new_region_geometry (N : ℕ) [NeZero N]
    (W : Finset (List SL(2,ℤ))) (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (C : J → ℝ) :
    ∃ B : ℝ, 1≤B ∧ ∃ D : ℝ, 1≤D ∧
      ∀ (ε : ℝ), 0<ε → ∀ (H : ℝ), 0≤H →
      enlargedRegion b w (fun j => wideCompactCover N (H/C j)) (wordRegion W ε H) ⊆
        wideImageRegion B 2 (min ε (1/4)) (D*H) := by
  let F := enlargementLabels (wordLabels W) b w (fun _ => wideCoverLabels N)
  obtain ⟨B,hB,hgeo⟩ := finite_labels_wide_geometry F
  let D := sourceHeightScale C
  have hD : 1≤D := sourceHeightScale_one_le C
  refine ⟨B,hB,D,hD,?_⟩
  intro ε hε H hH
  let Y := min ε (1/4)
  have hY : 0<Y := lt_min hε (by norm_num)
  have hHD : H≤D*H := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hD hH
  have hv : wordRegion W ε H⊆labelRegion (wordLabels W) (observationRectangle 2 Y (D*H)) := by
    apply (wordRegion_subset_labels W ε H).trans
    apply labelRegion_mono
    intro z hz
    refine ⟨?_,(min_le_left _ _).trans hz.2.2.1,hz.2.2.2.trans hHD⟩
    rw [abs_of_nonneg hz.1]
    exact hz.2.1.trans (by norm_num)
  have hs (j : J) : wideCompactCover N (H/C j)⊆
      labelRegion (wideCoverLabels N) (observationRectangle 2 Y (D*H)) := by
    apply (wideCompactCover_subset_labels N (H/C j)).trans
    apply labelRegion_mono
    intro z hz
    refine ⟨abs_le.mpr ⟨?_,hz.2.1⟩,(min_le_right _ _).trans hz.2.2.1,
      hz.2.2.2.trans (sourceHeightScale_div C j hH)⟩
    linarith [hz.1]
  exact (enlargedRegion_subset_labels (wordLabels W) b w (fun _ => wideCoverLabels N)
    (fun j => wideCompactCover N (H/C j)) hv hs).trans (hgeo 2 Y (D*H) hY)

#print axioms wideCompactCover_subset_labels
#print axioms sourceHeightScale_div
#print axioms enlarged_new_region_geometry
end QuantitativeEulerEndpointPrepared
