module

public import QuantitativeSpectralTerminalReductionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane MeasureTheory Set
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticHyperbolicArea
open AsymptoticCongruenceCover AsymptoticRationalBranches AsymptoticRegularTrace
open QuantitativeSpectralFiniteReduction QuantitativeSpectralTerminalReduction
open scoped MatrixGroups ENNReal NNReal Pointwise

/-- The compact cutoff matches the overlapping strip used by finite-word
reduction. Its width is fixed, independent of the cusp height. -/
def wideBox (H : ℝ) : Set ℍ :=
  {z | -1 ≤ z.re ∧ z.re ≤ 2 ∧ (1:ℝ)/4 ≤ z.im ∧ z.im ≤ H}

def wideTail (H : ℝ) : Set ℍ := {z | -1 ≤ z.re ∧ z.re < 2 ∧ H < z.im}

theorem wideBox_compact (H : ℝ) : IsCompact (wideBox H) := by
  have he : UpperHalfPlane.coe '' wideBox H =
      Complex.measurableEquivRealProd.symm '' (Icc (-1:ℝ) 2 ×ˢ Icc ((1:ℝ)/4) H) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(w.re,w.im),⟨⟨hw.1,hw.2.1⟩,hw.2.2⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨⟨x,y⟩,lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hxy.2.1⟩,
        ⟨hxy.1.1,hxy.1.2,hxy.2⟩,rfl⟩
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff,he]
  apply (isCompact_Icc.prod isCompact_Icc).image
  change Continuous (fun p : ℝ×ℝ => (⟨p.1,p.2⟩:ℂ))
  exact Complex.equivRealProdCLM.symm.continuous

theorem wideTail_measurable (H : ℝ) : MeasurableSet (wideTail H) := by
  exact (measurableSet_Ici.preimage continuous_re.measurable).inter
    ((measurableSet_Iio.preimage continuous_re.measurable).inter
      (measurableSet_Ioi.preimage continuous_im.measurable))

theorem wideTail_area {H : ℝ} (hH : 0<H) :
    (volume : Measure ℍ) (wideTail H)=3*ENNReal.ofReal H⁻¹ := by
  have he : UpperHalfPlane.coe '' wideTail H =
      Complex.measurableEquivRealProd.symm '' (Ico (-1:ℝ) 2 ×ˢ Ioi H) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(w.re,w.im),⟨⟨hw.1,hw.2.1⟩,hw.2.2⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨⟨x,y⟩,hH.trans hxy.2⟩,⟨hxy.1.1,hxy.1.2,hxy.2⟩,rfl⟩
  rw [UpperHalfPlane.volume_eq_lintegral,he]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  change (∫⁻ p : ℝ×ℝ in Ico (-1:ℝ) 2 ×ˢ Ioi H,
    (↑((1/‖p.2‖₊)^2 : ℝ≥0) : ℝ≥0∞))=3*ENNReal.ofReal H⁻¹
  rw [Measure.volume_eq_prod,setLIntegral_prod _ (by fun_prop)]
  simp only [vertical_area hH]
  norm_num [mul_comm]

def wideCompactCover (N : ℕ) (H : ℝ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (integralLabel q.out)⁻¹ • wideBox H

def wideTailCover (N : ℕ) (H : ℝ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (integralLabel q.out)⁻¹ • wideTail H

theorem wideCompactCover_compact (N : ℕ) (hN : 0<N) (H : ℝ) :
    IsCompact (wideCompactCover N H) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply isCompact_iUnion
  intro q
  exact (wideBox_compact H).image (action_continuous _)

theorem wideTailCover_measurable (N : ℕ) (hN : 0<N) (H : ℝ) :
    MeasurableSet (wideTailCover N H) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply MeasurableSet.iUnion
  intro q
  rw [← preimage_smul_inv]
  exact (wideTail_measurable H).preimage
    (AsymptoticRationalGroup.measurePreserving (integralLabel q.out)).measurable

/-- The actual open reduction cover is contained in this compact/tail split;
there is no mismatch between its horizontal overlap and sampling cutoff. -/
theorem openCover_subset_wide_split (N : ℕ) (H : ℝ) :
    openCover N ⊆ wideCompactCover N H ∪ wideTailCover N H := by
  intro z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  by_cases hh : w.im ≤ H
  · exact Or.inl (mem_iUnion.mpr ⟨q,w,⟨hw.1.le,hw.2.1.le,hw.2.2.le,hh⟩,rfl⟩)
  · exact Or.inr (mem_iUnion.mpr ⟨q,w,⟨hw.1.le,hw.2.1,lt_of_not_ge hh⟩,rfl⟩)

theorem wideTailCover_area (N : ℕ) (hN : 0<N) {H : ℝ} (hH : 0<H) :
    (volume : Measure ℍ) (wideTailCover N H) ≤
      (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ≥0∞)*
        (3*ENNReal.ofReal H⁻¹) := by
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  apply (measure_iUnion_le _).trans_eq
  have he (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      (volume : Measure ℍ) ((integralLabel q.out)⁻¹ • wideTail H)=3*ENNReal.ofReal H⁻¹ := by
    rw [←preimage_smul_inv,inv_inv]
    rw [(AsymptoticRationalGroup.measurePreserving (integralLabel q.out)).measure_preimage
      (wideTail_measurable H).nullMeasurableSet,wideTail_area hH]
  simp only [he,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]

theorem wideTailCover_trace (N : ℕ) (hN : 0<N) {H : ℝ} (hH : 0<H) :
    trace volume (AsymptoticOrbitDiagonal.corner (G:=AsymptoticRationalGroup.Group)
      (wideTailCover N H)) ≤
      (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ≥0∞)*
        (3*ENNReal.ofReal H⁻¹) := by
  rw [AsymptoticOrbitDiagonal.trace_corner volume (wideTailCover_measurable N hN H)]
  exact wideTailCover_area N hN hH

/-- One fixed finite word family works simultaneously for all cusp cutoffs. -/
theorem finite_terminal_words_wide (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ W : Finset (List SL(2,ℤ)),
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ H : ℝ, ∀ z∈terminal ε, ∃ l∈W,
        integralLabel l.prod • z ∈ wideCompactCover N H ∪ wideTailCover N H := by
  obtain ⟨W,hW,hw⟩ := finite_terminal_words N S hS hε
  refine ⟨W,hW,?_⟩
  intro H z hz
  obtain ⟨l,hl,hlz⟩ := hw z hz
  exact ⟨l,hl,openCover_subset_wide_split N H hlz⟩

#print axioms openCover_subset_wide_split
#print axioms wideTailCover_trace
#print axioms finite_terminal_words_wide
end QuantitativeSpectralObservability
