module

public import QuantitativeHolomorphicMatrixActionV1
public import QuantitativeHolomorphicFilterExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch

/-- Actual integer representatives of every label, with a common entry
height. Coefficients are handled separately by the proved expression-mass
bounds. -/
def ExpressionMatrixBound (E : Expression) (B : ℝ) : Prop :=
  ∀ b ∈ E, ∃ M : IntegerMatrix2, IntegerAction b.label M ∧ MatrixEntryBound M B

theorem ExpressionMatrixBound.mono {E : Expression} {B C : ℝ}
    (hE : ExpressionMatrixBound E B) (hBC : B ≤ C) : ExpressionMatrixBound E C := by
  intro b hb
  obtain ⟨M,ha,hm⟩ := hE b hb
  exact ⟨M,ha,fun i j => (hm i j).trans hBC⟩

theorem expressionMatrixBound_identity : ExpressionMatrixBound [identity] 1 := by
  intro b hb
  have hb' : b=identity := by simpa only [List.mem_singleton] using hb
  subst b
  refine ⟨1,integerAction_one,?_⟩
  intro i j
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem ExpressionMatrixBound.append {E F : Expression} {B C : ℝ}
    (hE : ExpressionMatrixBound E B) (hF : ExpressionMatrixBound F C) :
    ExpressionMatrixBound (E++F) (max B C) := by
  intro b hb
  rcases List.mem_append.mp hb with hb|hb
  · exact hE.mono (le_max_left B C) b hb
  · exact hF.mono (le_max_right B C) b hb

theorem ExpressionMatrixBound.scale {E : Expression} {B : ℝ}
    (hE : ExpressionMatrixBound E B) (a : ℂ) : ExpressionMatrixBound (scaleExpression a E) B := by
  intro b hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  exact hE c hc

theorem ExpressionMatrixBound.adjoint {E : Expression} {B : ℝ}
    (hE : ExpressionMatrixBound E B) : ExpressionMatrixBound (adjointExpression E) B := by
  intro b hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  obtain ⟨M,ha,hm⟩ := hE c hc
  exact ⟨M.adjugate,ha.inv,matrix_entry_bound_adjugate hm⟩

theorem ExpressionMatrixBound.compose {E F : Expression} {B C : ℝ}
    (hE : ExpressionMatrixBound E B) (hF : ExpressionMatrixBound F C)
    (hC : 0 ≤ C) :
    ExpressionMatrixBound (composeExpression E F) (2*B*C) := by
  intro b hb
  obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  obtain ⟨M,hm,hM⟩ := hE a ha
  obtain ⟨L,hl,hL⟩ := hF c hc
  refine ⟨L*M,hl.mul hm,?_⟩
  have hh := matrix_entry_bound_mul hC hL hM
  convert hh using 1
  ring

theorem ExpressionMatrixBound.power {E : Expression} {B : ℝ}
    (hB : 0 ≤ B) (hE : ExpressionMatrixBound E B) (d : ℕ) :
    ExpressionMatrixBound (powerExpression E d) ((2*B)^d) := by
  induction d with
  | zero => exact expressionMatrixBound_identity
  | succ d ih =>
    have hh := hE.compose ih (by positivity)
    simpa only [powerExpression,pow_succ'] using hh

theorem expressionMatrixBound_sum {ι : Type*} (qs : Finset ι) (E : ι → Expression) {B : ℝ}
    (hE : ∀ i ∈ qs, ExpressionMatrixBound (E i) B) :
    ExpressionMatrixBound (sumExpressions qs E) B := by
  intro b hb
  obtain ⟨i,hi,hb⟩ := List.mem_flatMap.mp hb
  exact hE i (Finset.mem_toList.mp hi) b hb

/-- The matrix height of a Gram stack does not depend on its number of rows;
row count enters coefficient mass separately. -/
theorem expressionMatrixBound_observationGram {ι : Type*} (qs : Finset ι)
    (rows : ι → Expression) (V : Expression) {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hr : ∀ i ∈ qs, ExpressionMatrixBound (rows i) R) (hv : ExpressionMatrixBound V B) :
    ExpressionMatrixBound (observationGramExpression qs rows V) (8*R^2*B^2) := by
  apply expressionMatrixBound_sum
  intro i hi
  have h := (hr i hi).compose hv hB
  have hh := h.adjoint.compose h (by positivity : 0 ≤ 2*R*B)
  convert hh using 1
  ring

/-- Explicit integer-entry height for the single global positive filter,
including both reconstruction factors. It grows exponentially in the filter
degree, with no expansion-count factor. -/
theorem expressionMatrixBound_observationFilter {ι : Type*} (qs : Finset ι)
    (rows : ι → Expression) (V : Expression) (b : ι → ℝ) {R B : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hr : ∀ i ∈ qs, ExpressionMatrixBound (rows i) R) (hv : ExpressionMatrixBound V B) (d : ℕ) :
    ExpressionMatrixBound (observationFilterExpression qs rows V b d)
      (4*B^2*(2*max 1 (8*R^2*B^2))^d) := by
  have hg := expressionMatrixBound_observationGram qs rows V hR hB hr hv
  have hs := expressionMatrixBound_identity.append (hg.scale (-(((finiteRowBound qs b)⁻¹:ℝ):ℂ)))
  have hp := hs.power (le_trans zero_le_one (le_max_left _ _)) d
  have hh := hv.compose (hp.compose hv.adjoint hB) (by positivity : 0 ≤ 2*(2*max 1 (8*R^2*B^2))^d*B)
  convert hh using 1
  · rfl
  · ring

/-- Matrix-height certificates supply the trace geometry directly. -/
def ExpressionMatrixBound.geometry {E : Expression} {B : ℝ} (hE : ExpressionMatrixBound E B)
    (hB : 0 ≤ B) (Y H : ℝ) (S : Finset ℤ) (b : Branch) (hb : b ∈ E) (hne : b.label ≠ 1) :
    RetainedBranchGeometry b Y H (B*(H+2)) S := by
  let M := Classical.choose (hE b hb)
  have hh := Classical.choose_spec (hE b hb)
  exact retainedBranchGeometry_of_global_matrix b Y H B S M hB hh.2 hh.1.1 hh.1.2 hne

#print axioms ExpressionMatrixBound.compose
#print axioms ExpressionMatrixBound.adjoint
#print axioms ExpressionMatrixBound.power
#print axioms expressionMatrixBound_observationFilter

end QuantitativeHolomorphic
