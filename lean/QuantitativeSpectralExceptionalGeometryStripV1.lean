module

public import QuantitativeSpectralExceptionalGeometryCuspV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open UpperHalfPlane Set AsymptoticRegularBranchFamily
open AsymptoticCongruenceLabels QuantitativeSpectralObservability
open QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups

def stripBox (R ε Y : ℝ) : Set ℍ :=
  {z | -R ≤ z.re ∧ z.re ≤ R ∧ ε ≤ z.im ∧ z.im ≤ Y}

theorem stripBox_compact (R : ℝ) {ε : ℝ} (hε : 0 < ε) (Y : ℝ) :
    IsCompact (stripBox R ε Y) := by
  have he : UpperHalfPlane.coe '' stripBox R ε Y =
      Complex.measurableEquivRealProd.symm '' (Icc (-R) R ×ˢ Icc ε Y) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(w.re,w.im),⟨⟨hw.1,hw.2.1⟩,hw.2.2⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨⟨x,y⟩,hε.trans_le hxy.2.1⟩,⟨hxy.1.1,hxy.1.2,hxy.2⟩,rfl⟩
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff,he]
  apply (isCompact_Icc.prod isCompact_Icc).image
  exact Complex.equivRealProdCLM.symm.continuous

/-- Combining the fixed compact lower box with the affine cusp reduction
produces fixed words for the entire unbounded positive-height strip. -/
theorem finite_strip_branch_words (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : Branch) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ H : ℝ, B ≤ H → ∀ z : ℍ, |z.re| ≤ R → ε ≤ z.im → z.im ≤ H/C →
        ∃ l ∈ W, (integralLabel l.prod * label b) • z ∈ wideCompactCover N H := by
  classical
  obtain ⟨C,Y,hC,_,W₁,hW₁,hhigh⟩ := finite_cusp_branch_words N S hS b R
  obtain ⟨W₀,B,hB,hW₀,hcover,hlow⟩ := finite_compact_branch_reduction N S hS
    (fun _ : Unit => b) (stripBox_compact R hε Y)
  refine ⟨C,B,hC,hB,W₀ ∪ W₁,?_,?_⟩
  · intro l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · exact hW₀ l hl
    · exact hW₁ l hl
  · intro H hH z hx hy ht
    by_cases hz : z.im ≤ Y
    · have hzbox : z ∈ stripBox R ε Y := ⟨(abs_le.mp hx).1,(abs_le.mp hx).2,hy,hz⟩
      obtain ⟨w,hw,hzpiece⟩ := hcover z hzbox
      exact ⟨w (),Finset.mem_union_left _ (hw ()),hlow w H hH z hzpiece ()⟩
    · obtain ⟨l,hl,hlz⟩ := hhigh H z hx (le_of_lt (lt_of_not_ge hz)) ht
      exact ⟨l,Finset.mem_union_right _ hl,hlz⟩

/-- A finite rational branch family has one uniform cusp-height factor,
one initial cutoff, and one fixed finite generator-word set. -/
theorem finite_strip_family_words {ι : Type*} [Fintype ι]
    (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : ι → Branch) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ H : ℝ, B ≤ H → ∀ z : ℍ, |z.re| ≤ R → ε ≤ z.im → z.im ≤ H/C →
        ∀ i, ∃ l ∈ W, (integralLabel l.prod * label (b i)) • z ∈ wideCompactCover N H := by
  classical
  choose C B hC hB W hW hr using fun i => finite_strip_branch_words N S hS (b i) R hε
  let C₀ : ℝ := 1 + ∑ i, C i
  let B₀ : ℝ := 1 + ∑ i, B i
  have hc : 0 < C₀ := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hC i).le))
  have hb : 0 < B₀ := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hB i).le))
  have hci (i) : C i ≤ C₀ := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hC j).le) (Finset.mem_univ i)
    dsimp [C₀]
    linarith
  have hbi (i) : B i ≤ B₀ := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hB j).le) (Finset.mem_univ i)
    dsimp [B₀]
    linarith
  refine ⟨C₀,B₀,hc,hb,Finset.univ.biUnion W,?_,?_⟩
  · intro l hl
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hl
    exact hW i l hi
  · intro H hH z hx hy ht i
    have hdiv : H/C₀ ≤ H/C i := div_le_div_of_nonneg_left (hb.le.trans hH) (hC i) (hci i)
    obtain ⟨l,hl,hlz⟩ := hr i H ((hbi i).trans hH) z hx hy (ht.trans hdiv)
    exact ⟨l,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hl⟩,hlz⟩

#print axioms finite_strip_branch_words
#print axioms finite_strip_family_words

end QuantitativeSpectralExceptionalGeometry
