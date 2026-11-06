module

public import AsymptoticCongruenceFiniteCoverV1
public import AsymptoticRationalBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralCongruenceCover

open Matrix UpperHalfPlane MeasureTheory Set
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticHyperbolicArea
open AsymptoticCongruenceCover AsymptoticRationalBranches AsymptoticRegularTrace
open scoped MatrixGroups ENNReal Pointwise

/-- A literal compact truncation of the modular reduction strip. -/
def box (H : ℝ) : Set ℍ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ (1:ℝ)/4 ≤ z.im ∧ z.im ≤ H}

theorem box_image (H : ℝ) : UpperHalfPlane.coe '' box H =
    Complex.measurableEquivRealProd.symm '' (Icc (0:ℝ) 1 ×ˢ Icc ((1:ℝ)/4) H) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨(w.re,w.im),⟨⟨hw.1,hw.2.1⟩,hw.2.2⟩,rfl⟩
  · rintro ⟨⟨x,y⟩,hxy,rfl⟩
    exact ⟨⟨⟨x,y⟩,lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hxy.2.1⟩,
      ⟨hxy.1.1,hxy.1.2,hxy.2⟩,rfl⟩

theorem box_compact (H : ℝ) : IsCompact (box H) := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff, box_image]
  apply (isCompact_Icc.prod isCompact_Icc).image
  change Continuous (fun p : ℝ×ℝ => (⟨p.1,p.2⟩:ℂ))
  exact Complex.equivRealProdCLM.symm.continuous

def compactCover (N : ℕ) (H : ℝ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (integralLabel q.out)⁻¹ • box H

def tailCover (N : ℕ) (H : ℝ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (integralLabel q.out)⁻¹ • terminal H

theorem compactCover_compact (N : ℕ) (hN : 0 < N) (H : ℝ) : IsCompact (compactCover N H) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply isCompact_iUnion
  intro q
  exact (box_compact H).image (action_continuous _)

theorem tailCover_measurable (N : ℕ) (hN : 0 < N) (H : ℝ) : MeasurableSet (tailCover N H) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply MeasurableSet.iUnion
  intro q
  rw [← preimage_smul_inv]
  exact (terminal_measurable H).preimage
    (AsymptoticRationalGroup.measurePreserving (integralLabel q.out)).measurable

/-- The complete congruence cover splits into an actual compact set and a
finite collection of explicit cusp tails; no cusp classification is assumed. -/
theorem cover_subset_compact_tail (N : ℕ) (H : ℝ) :
    cover N ⊆ compactCover N H ∪ tailCover N H := by
  intro z hz
  obtain ⟨q,hq⟩ := mem_iUnion.mp hz
  obtain ⟨w,hw,rfl⟩ := hq
  by_cases hheight : w.im ≤ H
  · apply Or.inl
    apply mem_iUnion.mpr
    refine ⟨q,w,?_,rfl⟩
    exact ⟨hw.1.1,hw.1.2.le,hw.2.le,hheight⟩
  · apply Or.inr
    apply mem_iUnion.mpr
    exact ⟨q,w,⟨hw.1,lt_of_not_ge hheight⟩,rfl⟩

/-- Every actual Gamma0 orbit meets the compact truncation or one of the
listed cusp tails. This uses the integral congruence coset representatives. -/
theorem orbit_meets_compact_tail (N : ℕ) (H : ℝ) (z : ℍ) :
    ∃ g : gamma N, g.val • z ∈ compactCover N H ∪ tailCover N H := by
  obtain ⟨g,hg⟩ := orbit_meets_cover N z
  exact ⟨g,cover_subset_compact_tail N H hg⟩

/-- Explicit cusp-tail area with the genuine finite Gamma0 index. -/
theorem tailCover_area (N : ℕ) (hN : 0 < N) {H : ℝ} (hH : 0 < H) :
    (volume : Measure ℍ) (tailCover N H) ≤
      (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ≥0∞) * ENNReal.ofReal H⁻¹ := by
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  apply (measure_iUnion_le _).trans_eq
  have he (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      (volume : Measure ℍ) ((integralLabel q.out)⁻¹ • terminal H) = ENNReal.ofReal H⁻¹ := by
    rw [← preimage_smul_inv, inv_inv]
    rw [(AsymptoticRationalGroup.measurePreserving (integralLabel q.out)).measure_preimage
      (terminal_measurable H).nullMeasurableSet, terminal_area hH]
  simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- The boundary target is a concrete regular diagonal projection with the
required `index/H` trace estimate. -/
theorem tailCover_trace (N : ℕ) (hN : 0 < N) {H : ℝ} (hH : 0 < H) :
    trace volume (AsymptoticOrbitDiagonal.corner (G:=AsymptoticRationalGroup.Group) (tailCover N H)) ≤
      (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℝ≥0∞) * ENNReal.ofReal H⁻¹ := by
  rw [AsymptoticOrbitDiagonal.trace_corner volume (tailCover_measurable N hN H)]
  exact tailCover_area N hN hH

#print axioms box_compact
#print axioms compactCover_compact
#print axioms orbit_meets_compact_tail
#print axioms tailCover_area
#print axioms tailCover_trace

end QuantitativeSpectralCongruenceCover
