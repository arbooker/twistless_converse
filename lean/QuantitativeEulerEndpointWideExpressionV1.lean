module

public import QuantitativeEulerEndpointWideGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory QuantitativeHolomorphic AsymptoticRationalFreeness
open AsymptoticCompactBranch AsymptoticFiniteBranch

def wideCompactCutoff (B R Y H : ℝ) : ℕ := ⌈B*(H+R+1)/min 1 Y⌉₊

/-- Explicit compact data on a wide rectangle. Its weight ratio and finite
fold interval are proved from the actual integer representative. -/
def wideCompactData (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {M : IntegerMatrix2} {B R Y H ε : ℝ}
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix g hg) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y) (hε : 0<ε)
    {s : Set ℍ} (hre : ∀ z∈s, |z.re|≤R)
    (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H) (t : ℕ) :
    Data (realMatrix g) s ε t where
  folds := Finset.Icc (-(wideCompactCutoff B R Y H : ℤ)) (wideCompactCutoff B R Y H)
  fold_mem := by
    intro z hz
    have he := (Complex.abs_re_le_norm _).trans
      (wide_integer_image_norm hM hB hb hY z (hre z hz) (hlo z hz) (hhi z hz))
    rw [AsymptoticRationalBranches.ofMatrix_action] at he
    have hj : |(realMatrix g • z).re| ≤ wideCompactCutoff B R Y H := he.trans (Nat.le_ceil _)
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa using (abs_le.mp hj).1
    · simpa using Int.floor_mono (abs_le.mp hj).2
  bound := (wideDistortion B R H)^t
  bound_nonneg := pow_nonneg (wideDistortion_pos B R H).le t
  ratio_le := by
    intro z hz
    apply compact_ratio_le_of_height (realMatrix g) hε (le_max_left _ _) t z
    have hh := wide_integer_height_distortion hM hB hb z (hre z hz) (hhi z hz)
    rwa [AsymptoticRationalBranches.ofMatrix_action] at hh

/-- Exact branch count and coefficient mass, and an explicit matrix-height
bound, for the wide-rectangle compact expression. -/
theorem wideCompactExpression_bounds (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {M : IntegerMatrix2} {B R Y H ε : ℝ}
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix g hg) M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (hY : 0<Y) (hε : 0<ε)
    {s : Set ℍ} (hs : MeasurableSet s) (hre : ∀ z∈s, |z.re|≤R)
    (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H) (t : ℕ) :
    let J := wideCompactCutoff B R Y H
    let E := compactExpression g hg hs hε t (wideCompactData g hg hM hB hb hY hε hre hlo hhi t)
    E.length = 2*J+1 ∧
      expressionBound E = (2*(J:ℝ)+1)*(wideDistortion B R H)^t ∧
      ExpressionMatrixBound E (4*(1+(J:ℝ))*B) := by
  dsimp only
  have hc : (wideCompactData g hg hM hB hb hY hε hre hlo hhi t).folds.card =
      2*wideCompactCutoff B R Y H+1 := by
    simp [wideCompactData, Int.card_Icc]
    omega
  have he := compactExpression_complexity g hg hs hε t
    (wideCompactData g hg hM hB hb hY hε hre hlo hhi t)
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

#print axioms wideCompactData
#print axioms wideCompactExpression_bounds
end QuantitativeEulerEndpointPrepared
