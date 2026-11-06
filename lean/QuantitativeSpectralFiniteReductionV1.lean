module

public import QuantitativeSpectralCongruenceCoverV1
public import AsymptoticCongruenceGeneratorsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralFiniteReduction

open Matrix UpperHalfPlane Set MeasureTheory
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticCongruenceCover
open AsymptoticRationalBranches
open scoped MatrixGroups Pointwise

/-- A slightly overlapping reduction strip makes the reduction cover
open. Its three unit-width translates are still a fixed finite cover. -/
def openStrip : Set ℍ := {z | (-1:ℝ)<z.re ∧ z.re<2 ∧ (1:ℝ)/4<z.im}

theorem openStrip_open : IsOpen openStrip :=
  (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_re continuous_const).inter (isOpen_lt continuous_const continuous_im))

def openCover (N : ℕ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (integralLabel q.out)⁻¹ • openStrip

theorem openCover_open (N : ℕ) : IsOpen (openCover N) := by
  apply isOpen_iUnion
  intro q
  rw [← preimage_smul_inv]
  exact openStrip_open.preimage (action_continuous _)

theorem cover_subset_openCover (N : ℕ) : cover N ⊆ openCover N := by
  intro z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  apply mem_iUnion.mpr
  refine ⟨q,w,?_,rfl⟩
  exact ⟨by linarith [hw.1.1],by linarith [hw.1.2],hw.2⟩

/-- Compactness produces a fixed finite collection of actual Gamma0
reduction labels. It is applied to the fixed lower part of the terminal
strip, so these labels do not depend on the growing cusp cutoff. -/
theorem finite_reduction (N : ℕ) {s : Set ℍ} (hs : IsCompact s) :
    ∃ F : Finset (gamma N), ∀ z ∈ s, ∃ g ∈ F, g.val • z ∈ openCover N := by
  obtain ⟨F,hF⟩ := hs.elim_finite_subcover
    (fun g : gamma N => (fun z => g.val • z) ⁻¹' openCover N)
    (fun g => (openCover_open N).preimage (action_continuous g.val)) (by
      intro z _
      obtain ⟨g,hg⟩ := orbit_meets_cover N z
      exact mem_iUnion.mpr ⟨g,cover_subset_openCover N hg⟩)
  refine ⟨F,?_⟩
  intro z hz
  obtain ⟨g,hg⟩ := mem_iUnion.mp (hF hz)
  obtain ⟨hgF,hgz⟩ := mem_iUnion.mp hg
  exact ⟨g,hgF,hgz⟩

/-- Every literal congruence matrix is a finite word in the chosen
integral generators and their inverses. -/
theorem congruence_word (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ l : List SL(2,ℤ), l.prod=g ∧ ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S := by
  rw [← hS] at hg
  apply Subgroup.closure_induction_left (p := fun g _ =>
    ∃ l : List SL(2,ℤ), l.prod=g ∧ ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ?_ ?_ ?_ hg
  · exact ⟨[],rfl,by simp⟩
  · intro a ha b _ hb
    obtain ⟨l,rfl,hl⟩ := hb
    refine ⟨a::l,rfl,?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl ha
    · exact hl c hc
  · intro a ha b _ hb
    obtain ⟨l,rfl,hl⟩ := hb
    refine ⟨a⁻¹::l,rfl,?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inr (by simpa using ha)
    · exact hl c hc

/-- Compact terminal reduction uses a finite collection of actual
words in any fixed generating set. Hence their lengths and every
intermediate compact image can be bounded before choosing H. -/
theorem finite_reduction_words (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    {s : Set ℍ} (hs : IsCompact s) :
    ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ z ∈ s, ∃ l ∈ W, integralLabel l.prod • z ∈ openCover N := by
  classical
  obtain ⟨F,hF⟩ := finite_reduction N hs
  choose l hl using fun g : gamma N =>
    congruence_word N S hS (representative g) (representative_mem g)
  refine ⟨F.image l,?_,?_⟩
  · intro w hw
    obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hw
    exact (hl g).2
  · intro z hz
    obtain ⟨g,hg,hgz⟩ := hF z hz
    refine ⟨l g,Finset.mem_image.mpr ⟨g,hg,rfl⟩,?_⟩
    rwa [(hl g).1,representative_label]

#print axioms finite_reduction_words

#print axioms finite_reduction

end QuantitativeSpectralFiniteReduction
