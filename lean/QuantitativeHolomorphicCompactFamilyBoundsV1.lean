module

public import QuantitativeHolomorphicIntegerCompactV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane MeasureTheory AsymptoticRationalFreeness
open AsymptoticCompactBranch AsymptoticFiniteBranch

variable {ι : Type*} [Fintype ι]

/-- Common branch expression with supplied quantitative compact data for
each actual observation matrix. -/
def compactFamilyDataExpression (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set UpperHalfPlane} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : ∀ i, Data (realMatrix (b i).matrix) s ε t) : Expression :=
  sumExpressions Finset.univ (fun i => scaleExpression (c i)
    (compactExpression (b i).matrix (b i).positive hs.measurableSet hε t (D i)))

theorem compactFamilyDataExpression_physical (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set UpperHalfPlane} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ)
    (D : ∀ i, Data (realMatrix (b i).matrix) s ε t) :
    holomorphicSum (compactFamilyDataExpression b c hs hε t D) m =
      holomorphicSum (compactFamilyExpression b c hs hε t) m := by
  simp only [compactFamilyDataExpression, compactFamilyExpression,
    holomorphicSum_sumExpressions, holomorphicSum_scale]
  apply Finset.sum_congr rfl
  intro i _
  rw [compactExpression_physical_replacement (b i).matrix (b i).positive hs hε t m (D i)]

theorem compactFamilyDataExpression_regular (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set UpperHalfPlane} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : ∀ i, Data (realMatrix (b i).matrix) s ε t) (z : UpperHalfPlane) :
    regularSum (compactFamilyDataExpression b c hs hε t D) z =
      regularSum (compactFamilyExpression b c hs hε t) z := by
  simp only [compactFamilyDataExpression, compactFamilyExpression,
    regularSum_sumExpressions, regularSum_scale]
  apply Finset.sum_congr rfl
  intro i _
  rw [compactExpression_regular_replacement (b i).matrix (b i).positive hs hε t (D i) z]

theorem compactFamilyDataExpression_complexity (b : ι → AsymptoticRegularBranchFamily.Branch)
    (c : ι → ℂ) {s : Set UpperHalfPlane} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : ∀ i, Data (realMatrix (b i).matrix) s ε t) :
    (compactFamilyDataExpression b c hs hε t D).length = ∑ i, (D i).folds.card ∧
    expressionBound (compactFamilyDataExpression b c hs hε t D) =
      ∑ i, ‖c i‖ * ((D i).folds.card * (D i).bound) := by
  have he := fun i => compactExpression_complexity (b i).matrix (b i).positive hs.measurableSet hε t (D i)
  constructor
  · simp only [compactFamilyDataExpression, length_sumExpressions, scaleExpression,
      List.length_map, (he _).1]
  · simp only [compactFamilyDataExpression, expressionBound_sumExpressions,
      expressionBound_scale, (he _).2]

/-- Every fixed finite observation family admits exact physical and regular
expressions with explicit cutoff-dependent complexity. The sole constant B
depends only on its literal rational matrices, not on coefficients, weight,
region, lower height, upper height or capping exponent. -/
theorem compactFamily_uniform_integer_bounds (b : ι → AsymptoticRegularBranchFamily.Branch) :
    ∃ B : ℝ, 1≤B ∧ ∀ (c : ι → ℂ) {s : Set UpperHalfPlane} (hs : IsCompact s)
      {Y H ε : ℝ} (_hY : 0<Y) (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_hhi : ∀ z∈s, z.im≤H) (t : ℕ),
      ∃ E : Expression,
        (∀ m, holomorphicSum E m = holomorphicSum (compactFamilyExpression b c hs hε t) m) ∧
        (∀ z, regularSum E z = regularSum (compactFamilyExpression b c hs hε t) z) ∧
        E.length = Fintype.card ι * (2*integerCompactCutoff B Y H+1) ∧
        expressionBound E = (∑ i, ‖c i‖) *
          (2*(integerCompactCutoff B Y H:ℝ)+1)*(integerCompactDistortion B H)^t ∧
        ExpressionMatrixBound E (4*(1+(integerCompactCutoff B Y H:ℝ))*B) := by
  obtain ⟨B,hB,hrep⟩ := QuantitativeEulerIntegerHeight.finite_family_height
    (fun i => AsymptoticRationalBranches.ofMatrix (b i).matrix (b i).positive)
  choose M hM hb using hrep
  refine ⟨B,hB,?_⟩
  intro c s hs Y H ε hY hε hre hlo hhi t
  let D := fun i => integerCompactData (b i).matrix (b i).positive (hM i)
    (zero_le_one.trans hB) (hb i) hY hε hre hlo hhi t
  let E := compactFamilyDataExpression b c hs hε t D
  have he := fun i => integerCompactExpression_bounds (b i).matrix (b i).positive (hM i)
    (zero_le_one.trans hB) (hb i) hY hε hs.measurableSet hre hlo hhi t
  refine ⟨E, fun m => compactFamilyDataExpression_physical b c hs hε t m D,
    fun z => compactFamilyDataExpression_regular b c hs hε t D z, ?_, ?_, ?_⟩
  · dsimp only [E, compactFamilyDataExpression, D]
    simp only [length_sumExpressions, scaleExpression, List.length_map, (he _).1]
    simp
  · dsimp only [E, compactFamilyDataExpression, D]
    simp only [expressionBound_sumExpressions, expressionBound_scale, (he _).2.1]
    rw [← Finset.sum_mul]
    ring
  · apply expressionMatrixBound_sum
    intro i _
    exact (he i).2.2.scale (c i)

#print axioms compactFamilyDataExpression_physical
#print axioms compactFamilyDataExpression_regular
#print axioms compactFamilyDataExpression_complexity
#print axioms compactFamily_uniform_integer_bounds

end QuantitativeHolomorphic
