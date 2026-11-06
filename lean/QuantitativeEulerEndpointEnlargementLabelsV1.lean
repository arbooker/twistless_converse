module

public import QuantitativeEulerEndpointRegionLabelsV1
public import QuantitativeSpectralExceptionalStackEnlargementV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode AsymptoticCongruenceLabels
open AsymptoticRegularBranchFamily QuantitativeSpectralExceptionalReducedRows
open scoped Classical MatrixGroups

theorem labelRegion_labels_mono {F E : Finset G} (hFE : F⊆E) (s : Set ℍ) :
    labelRegion F s⊆labelRegion E s := by
  rintro z ⟨g,hg,y,hy,he⟩
  exact ⟨g,hFE hg,y,hy,he⟩

def commonLabels {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → Branch) (w : κ → ι → List SL(2,ℤ)) (F : Finset G) : Finset G :=
  Finset.univ.biUnion (fun k => Finset.univ.biUnion (fun i =>
    (wordSuffixes (w k i)).biUnion (fun a => F.image (fun g => integralLabel a*label (b i)*g))))

theorem commonRegion_subset_labels {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → Branch) (w : κ → ι → List SL(2,ℤ)) (F : Finset G)
    {s u : Set ℍ} (hs : s⊆labelRegion F u) :
    commonRegion b w s⊆labelRegion (commonLabels b w F) u := by
  intro z hz
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hz
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hk
  obtain ⟨a,ha,z',hz',he⟩ := region_suffix (w k i) hi
  obtain ⟨y,hy,rfl⟩ := hz'
  obtain ⟨g,hg,v,hv,hgv⟩ := hs hy
  refine ⟨integralLabel a*label (b i)*g,?_,v,hv,?_⟩
  · exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr
        ⟨a,ha,Finset.mem_image.mpr ⟨g,hg,rfl⟩⟩⟩⟩
  · simpa only [mul_smul,hgv] using he

variable {J : Type*} [Fintype J] {I K : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, Fintype (K j)]

def enlargementLabels (F : Finset G) (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (r : J → Finset G) : Finset G :=
  F ∪ Finset.univ.biUnion (fun j => r j ∪ commonLabels (b j) (w j) (r j))

/-- The entire detector enlargement uses finitely many composed labels,
including all source labels and all intermediate old-row word images. -/
theorem enlargedRegion_subset_labels (F : Finset G) (b : ∀ j, I j → Branch)
    (w : ∀ j, K j → I j → List SL(2,ℤ)) (r : J → Finset G)
    (s : J → Set ℍ) {v u : Set ℍ} (hv : v⊆labelRegion F u)
    (hs : ∀ j, s j⊆labelRegion (r j) u) :
    enlargedRegion b w s v⊆labelRegion (enlargementLabels F b w r) u := by
  intro z hz
  rcases hz with hz | hz
  · exact labelRegion_labels_mono (Finset.subset_union_left) u (hv hz)
  · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
    have hr : r j⊆enlargementLabels F b w r := by
      intro g hg
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_univ _,Finset.mem_union_left _ hg⟩)
    have hc : commonLabels (b j) (w j) (r j)⊆enlargementLabels F b w r := by
      intro g hg
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_univ _,Finset.mem_union_right _ hg⟩)
    rcases hj with hj | hj
    · exact labelRegion_labels_mono hr u (hs j hj)
    · exact labelRegion_labels_mono hc u
        (commonRegion_subset_labels (b j) (w j) (r j) (hs j) hj)

#print axioms commonRegion_subset_labels
#print axioms enlargedRegion_subset_labels
end QuantitativeEulerEndpointPrepared
