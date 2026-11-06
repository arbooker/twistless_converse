module

public import QuantitativeEulerEndpointWideExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeHolomorphic AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily
open scoped Classical

/-- The explicit wide data defines the existing compact operator exactly. -/
theorem compact_eq_wideData (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {M : IntegerMatrix2} {B R Y H ε : ℝ}
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix b.matrix b.positive) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) :
    compact b hs hε t x = AsymptoticRegularCompactBranch.operator b.matrix b.positive hε t
      (wideCompactData b.matrix b.positive hM hB hb hY hε hre hlo hhi t) x :=
  regular_compact_data_independent b.matrix b.positive hε t _ _ x

/-- Explicit norm bound for the actual compact branch on an arbitrary-width
rectangle; no auxiliary compactness-selected constant remains. -/
theorem compact_wide_norm (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {M : IntegerMatrix2} {B R Y H ε : ℝ}
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix b.matrix b.positive) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) :
    ‖compact b hs hε t x‖≤(2*(wideCompactCutoff B R Y H : ℝ)+1)*(wideDistortion B R H)^t := by
  rw [compact_eq_wideData b hs hM hB hb hY hε hre hlo hhi t x]
  have h := AsymptoticRegularCompactBranch.operator_norm_le b.matrix b.positive hε t
    (wideCompactData b.matrix b.positive hM hB hb hY hε hre hlo hhi t) x
  have hc : (wideCompactData b.matrix b.positive hM hB hb hY hε hre hlo hhi t).folds.card =
      2*wideCompactCutoff B R Y H+1 := by
    simp [wideCompactData, Int.card_Icc]
    omega
  rw [hc] at h
  push_cast at h
  exact h

theorem family_wide_norm {ι : Type*} [Fintype ι] (b : ι → Branch) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) (M : ι → IntegerMatrix2) {B R Y H ε : ℝ}
    (hM : ∀ i, IntegerAction (AsymptoticRationalBranches.ofMatrix (b i).matrix (b i).positive) (M i))
    (hB : 0≤B) (hb : ∀ i, MatrixEntryBound (M i) B) (hY : 0<Y) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) :
    ‖family b c hs hε t x‖≤(∑ i, ‖c i‖)*
      ((2*(wideCompactCutoff B R Y H : ℝ)+1)*(wideDistortion B R H)^t) := by
  unfold family
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (compact_wide_norm (b i) hs (hM i) hB (hb i) hY hε hre hlo hhi t x) (norm_nonneg _)

#print axioms compact_eq_wideData
#print axioms compact_wide_norm
#print axioms family_wide_norm
end QuantitativeEulerEndpointPrepared
