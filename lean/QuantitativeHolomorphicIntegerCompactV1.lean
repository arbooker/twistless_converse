module

public import QuantitativeHolomorphicCompactReplacementV1
public import QuantitativeHolomorphicMatrixCompactGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane MeasureTheory AsymptoticRationalFreeness
open AsymptoticCompactBranch AsymptoticFiniteBranch

def integerCompactCutoff (B Y H : ℝ) : ℕ := ⌈B*(H+2)/min 1 Y⌉₊
def integerCompactDistortion (B H : ℝ) : ℝ := max 1 ((B*(H+2))^2)

/-- Fully explicit observation data for an actual integer representative
on a retained unit rectangle. The ratio bound is independent of the lower
cutoff and of epsilon; the lower cutoff enters only the fold count. -/
def integerCompactData (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {M : IntegerMatrix2} {B Y H ε : ℝ}
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix g hg) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y) (hε : 0<ε)
    {s : Set UpperHalfPlane} (hre : ∀ z∈s, |z.re|≤1)
    (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H) (t : ℕ) :
    Data (realMatrix g) s ε t where
  folds := Finset.Icc (-(integerCompactCutoff B Y H : ℤ)) (integerCompactCutoff B Y H)
  fold_mem := by
    intro z hz
    have he := hM.image_re_bound hB hb hY z (hre z hz) (hlo z hz) (hhi z hz)
    rw [AsymptoticRationalBranches.ofMatrix_action] at he
    have hj : |(realMatrix g • z).re| ≤ integerCompactCutoff B Y H := he.trans (Nat.le_ceil _)
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa using (abs_le.mp hj).1
    · simpa using Int.floor_mono (abs_le.mp hj).2
  bound := (integerCompactDistortion B H)^t
  bound_nonneg := by unfold integerCompactDistortion; positivity
  ratio_le := by
    intro z hz
    dsimp only [integerCompactDistortion]
    apply compact_ratio_le_of_height (realMatrix g) hε (le_max_left _ _) t z
    have hh := hM.height_distortion hB hb z (hre z hz) (hhi z hz)
    rw [AsymptoticRationalBranches.ofMatrix_action] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (realMatrix g • z).im_pos.le)

/-- The height bound only needs the explicit fold interval; coefficient
and norm metadata may be chosen by either quantitative construction. -/
theorem compactExpression_matrix_bound_of_folds (g : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) {s : Set UpperHalfPlane} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t J : ℕ) (D : Data (realMatrix g) s ε t)
    (hfold : ∀ n∈D.folds, |(n:ℝ)|≤J)
    {M : IntegerMatrix2} {B : ℝ} (hB0 : 0≤B)
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix g hg) M)
    (hB : MatrixEntryBound M B) :
    ExpressionMatrixBound (compactExpression g hg hs hε t D) (4*(1+(J:ℝ))*B) := by
  have hraw : ExpressionMatrixBound (compactRawExpression g hg hs hε t D) (2*(1+(J:ℝ))*B) := by
    intro b hb
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
    obtain ⟨L,hl,hL⟩ := compactFold_integer_height g hg hM hB n
    have hnJ := hfold n (Finset.mem_toList.mp hn)
    refine ⟨L,hl,fun a b => (hL a b).trans ?_⟩
    nlinarith
  have hh := hraw.compose (expressionMatrixBound_singleton_one
    (corner AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable) rfl) zero_le_one
  convert hh using 1
  · rfl
  · ring

theorem compactExpression_complexity (g : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) {s : Set UpperHalfPlane} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t) :
    (compactExpression g hg hs hε t D).length = D.folds.card ∧
      expressionBound (compactExpression g hg hs hε t D) = D.folds.card * D.bound := by
  constructor
  · simp [compactExpression, length_composeExpression, compactRawExpression, ofFinset]
  · rw [compactExpression, expressionBound_compose]
    simp only [compactRawExpression, expressionBound, ofFinset, List.map_map,
      Function.comp_def, compactFold, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, corner, add_zero, mul_one]
    rw [Finset.sum_map_toList]
    simp

/-- The actual integer-based observation expression has explicit branch
count, mass and height, with no unspecified compactness constant. -/
theorem integerCompactExpression_bounds (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {M : IntegerMatrix2} {B Y H ε : ℝ}
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix g hg) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y) (hε : 0<ε)
    {s : Set UpperHalfPlane} (hs : MeasurableSet s) (hre : ∀ z∈s, |z.re|≤1)
    (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H) (t : ℕ) :
    let J := integerCompactCutoff B Y H
    let E := compactExpression g hg hs hε t (integerCompactData g hg hM hB hb hY hε hre hlo hhi t)
    E.length = 2*J+1 ∧
      expressionBound E = (2*(J:ℝ)+1)*(integerCompactDistortion B H)^t ∧
      ExpressionMatrixBound E (4*(1+(J:ℝ))*B) := by
  dsimp only
  have hc : (integerCompactData g hg hM hB hb hY hε hre hlo hhi t).folds.card =
      2*integerCompactCutoff B Y H+1 := by
    simp [integerCompactData, Int.card_Icc]
    omega
  have he := compactExpression_complexity g hg hs hε t
    (integerCompactData g hg hM hB hb hY hε hre hlo hhi t)
  refine ⟨he.1.trans hc, ?_, ?_⟩
  · rw [he.2,hc]
    push_cast
    rfl
  · apply compactExpression_matrix_bound_of_folds g hg hs hε t _ _ _ hB hM hb
    intro n hn
    have hh := Finset.mem_Icc.mp hn
    apply abs_le.mpr
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2

#print axioms integerCompactData
#print axioms compactExpression_matrix_bound_of_folds
#print axioms compactExpression_complexity
#print axioms integerCompactExpression_bounds

end QuantitativeHolomorphic
