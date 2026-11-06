module

public import QuantitativeSpectralFiniteReductionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralTerminalReduction

open Matrix UpperHalfPlane Set MeasureTheory
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticCongruenceCover
open AsymptoticHyperbolicArea
open QuantitativeSpectralFiniteReduction
open scoped MatrixGroups Pointwise Classical

/-- The lower part of a fixed terminal strip is compact, independently
of every later growing cusp cutoff. -/
def lowerPart (ε : ℝ) : Set ℍ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ ε ≤ z.im ∧ z.im ≤ 1/2}

theorem lowerPart_compact {ε : ℝ} (hε : 0 < ε) : IsCompact (lowerPart ε) := by
  have he : UpperHalfPlane.coe '' lowerPart ε =
      Complex.measurableEquivRealProd.symm '' (Icc (0:ℝ) 1 ×ˢ Icc ε ((1:ℝ)/2)) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(w.re,w.im),⟨⟨hw.1,hw.2.1⟩,hw.2.2⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨⟨x,y⟩,hε.trans_le hxy.2.1⟩,⟨hxy.1.1,hxy.1.2,hxy.2⟩,rfl⟩
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff,he]
  apply (isCompact_Icc.prod isCompact_Icc).image
  change Continuous (fun p : ℝ×ℝ => (⟨p.1,p.2⟩:ℂ))
  exact Complex.equivRealProdCLM.symm.continuous

/-- One fixed congruence label reduces the whole high translation strip;
this avoids applying compactness separately at each cutoff height. -/
theorem high_strip_reduction (N : ℕ) :
    ∃ g : gamma N, ∀ z ∈ terminal ((1:ℝ)/4), g.val • z ∈ openCover N := by
  let q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N := QuotientGroup.mk 1
  have hmem : q.out⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    simpa only [mul_one] using QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  refine ⟨⟨integralLabel q.out⁻¹,Subgroup.mem_map.mpr ⟨_,hmem,rfl⟩⟩,?_⟩
  intro z hz
  apply mem_iUnion.mpr
  refine ⟨q,z,?_,?_⟩
  · exact ⟨by linarith [hz.1.1],by linarith [hz.1.2],hz.2⟩
  · change (integralLabel q.out)⁻¹ • z = integralLabel (q.out⁻¹) • z
    rw [map_inv]

/-- A fixed finite set of Gamma0 labels reduces the entire terminal
strip. Neither the number of labels nor their generator-word lengths
can grow with a subsequent height cutoff H. -/
theorem finite_terminal_reduction (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (gamma N), ∀ z ∈ terminal ε,
      ∃ g ∈ F, g.val • z ∈ openCover N := by
  obtain ⟨F,hF⟩ := finite_reduction N (lowerPart_compact hε)
  obtain ⟨g,hg⟩ := high_strip_reduction N
  refine ⟨insert g F,?_⟩
  intro z hz
  by_cases hy : z.im ≤ 1/2
  · obtain ⟨a,ha,haz⟩ := hF z ⟨hz.1.1,hz.1.2.le,hz.2.le,hy⟩
    exact ⟨a,Finset.mem_insert_of_mem ha,haz⟩
  · have hh : (1:ℝ)/2 < z.im := lt_of_not_ge hy
    exact ⟨g,Finset.mem_insert_self _ _,hg z ⟨hz.1,lt_trans (by norm_num) hh⟩⟩

theorem finite_terminal_words (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ z ∈ terminal ε, ∃ l ∈ W, integralLabel l.prod • z ∈ openCover N := by
  obtain ⟨F,hF⟩ := finite_terminal_reduction N hε
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

#print axioms finite_terminal_reduction
#print axioms finite_terminal_words

end QuantitativeSpectralTerminalReduction
