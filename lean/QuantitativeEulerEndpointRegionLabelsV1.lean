module

public import QuantitativeEulerEndpointWideGeometryV1
public import QuantitativeEulerIntegerHeightV1
public import QuantitativeSpectralObservabilityTerminalV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeHolomorphic QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels QuantitativeSpectralWordDefect
open QuantitativeSpectralObservability
open scoped Classical MatrixGroups

/-- Finite labels covering all actual suffix images in the word region. -/
def wordSuffixes : List SL(2,ℤ) → Finset SL(2,ℤ)
  | [] => {1}
  | _::l => insert l.prod (wordSuffixes l)

theorem region_suffix (l : List SL(2,ℤ)) {s : Set ℍ} {z : ℍ}
    (hz : z∈region l s) :
    ∃ a∈wordSuffixes l, ∃ y∈s, integralLabel a • y=z := by
  induction l with
  | nil => exact ⟨1,by simp [wordSuffixes],z,hz,by simp⟩
  | cons a l ih =>
    rcases hz with hz | hz
    · obtain ⟨b,hb,y,hy,he⟩ := ih hz
      exact ⟨b,Finset.mem_insert_of_mem hb,y,hy,he⟩
    · obtain ⟨y,hy,rfl⟩ := hz
      exact ⟨l.prod,Finset.mem_insert_self _ _,y,hy,rfl⟩

/-- A finite union of literal rational images, with no compactness choice. -/
def labelRegion (F : Finset G) (s : Set ℍ) : Set ℍ :=
  {z | ∃ g∈F, ∃ y∈s, g • y=z}

def wordLabels (W : Finset (List SL(2,ℤ))) : Finset G :=
  W.biUnion (fun l => (wordSuffixes l).image integralLabel)

theorem wordRegion_subset_labels (W : Finset (List SL(2,ℤ))) (ε H : ℝ) :
    wordRegion W ε H⊆labelRegion (wordLabels W) (terminalRectangle ε H) := by
  intro z hz
  obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hz
  obtain ⟨a,ha,y,hy,he⟩ := region_suffix l.val hl
  exact ⟨integralLabel a,Finset.mem_biUnion.mpr
    ⟨l.val,l.property,Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩,y,hy,he⟩

theorem labelRegion_mono (F : Finset G) {s u : Set ℍ} (hsu : s⊆u) :
    labelRegion F s⊆labelRegion F u := by
  rintro z ⟨g,hg,y,hy,he⟩
  exact ⟨g,hg,y,hsu hy,he⟩

/-- A finite family of composed labels admits one height before every
rectangle parameter. This avoids successive inflation by individual images. -/
theorem finite_labels_wide_geometry (F : Finset G) :
    ∃ B : ℝ, 1≤B ∧ ∀ (R Y H : ℝ), 0<Y →
      labelRegion F (observationRectangle R Y H)⊆wideImageRegion B R Y H := by
  obtain ⟨B,hB,hmat⟩ := QuantitativeEulerIntegerHeight.finite_family_height
    (fun g : ↥F => g.val)
  refine ⟨B,hB,?_⟩
  intro R Y H hY z hz
  obtain ⟨g,hg,y,hy,rfl⟩ := hz
  obtain ⟨M,hM,hMb⟩ := hmat ⟨g,hg⟩
  exact wide_integer_image_mem hM (zero_le_one.trans hB) hMb hY y hy.1 hy.2.1 hy.2.2

#print axioms region_suffix
#print axioms wordRegion_subset_labels
#print axioms finite_labels_wide_geometry
end QuantitativeEulerEndpointPrepared
