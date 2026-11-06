module

public import QuantitativeEulerEndpointWideOperatorV1
public import AsymptoticFiniteBranchFamilyV1
public import QuantitativeHolomorphicCompactReplacementV1
public import QuantitativeHolomorphicFilterExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeHolomorphic AsymptoticRationalFreeness
open AsymptoticFiniteBranch
open scoped Classical

variable {ι : Type*} [Fintype ι] (b : ι → AsymptoticRegularBranchFamily.Branch) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) (M : ι → IntegerMatrix2) {B R Y H ε : ℝ}
    (hM : ∀ i, IntegerAction (AsymptoticRationalBranches.ofMatrix (b i).matrix (b i).positive) (M i))
    (hB : 0≤B) (hb : ∀ i, MatrixEntryBound (M i) B) (hY : 0<Y) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤R) (hlo : ∀ z∈s, Y≤z.im) (hhi : ∀ z∈s, z.im≤H) (t : ℕ)

def wideFamilyExpression : Expression :=
  sumExpressions Finset.univ (fun i => scaleExpression (c i)
    (compactExpression (b i).matrix (b i).positive hs.measurableSet hε t
      (wideCompactData (b i).matrix (b i).positive (hM i) hB (hb i) hY hε hre hlo hhi t)))

local notation "E" => wideFamilyExpression b c hs M hM hB hb hY hε hre hlo hhi t

theorem wideFamily_regular (x : ℍ) : regularSum E x=AsymptoticRegularBranchFamily.family b c hs hε t x := by
  rw [wideFamilyExpression,regularSum_sumExpressions]
  unfold AsymptoticRegularBranchFamily.family
  apply Finset.sum_congr rfl
  intro i _
  rw [regularSum_scale,regularSum_compactExpression]
  rw [compact_eq_wideData (b i) hs (hM i) hB (hb i) hY hε hre hlo hhi t x]

theorem wideFamily_holomorphic (m : ℕ) :
    holomorphicSum E m=holomorphicSum (compactFamilyExpression b c hs hε t) m := by
  rw [wideFamilyExpression,compactFamilyExpression,holomorphicSum_sumExpressions,holomorphicSum_sumExpressions]
  apply Finset.sum_congr rfl
  intro i _
  rw [holomorphicSum_scale,holomorphicSum_scale,
    compactExpression_physical_replacement (b i).matrix (b i).positive hs hε t m]

theorem wideFamily_mass : expressionBound E=(∑ i, ‖c i‖)*
    ((2*(wideCompactCutoff B R Y H:ℝ)+1)*(wideDistortion B R H)^t) := by
  rw [wideFamilyExpression,expressionBound_sumExpressions,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [expressionBound_scale,(wideCompactExpression_bounds (b i).matrix (b i).positive
    (hM i) hB (hb i) hY hε hs.measurableSet hre hlo hhi t).2.1]

theorem wideFamily_matrix : ExpressionMatrixBound E (4*(1+(wideCompactCutoff B R Y H:ℝ))*B) := by
  apply expressionMatrixBound_sum
  intro i _
  exact ((wideCompactExpression_bounds (b i).matrix (b i).positive
    (hM i) hB (hb i) hY hε hs.measurableSet hre hlo hhi t).2.2).scale (c i)

#print axioms wideFamily_regular
#print axioms wideFamily_holomorphic
#print axioms wideFamily_mass
#print axioms wideFamily_matrix
end QuantitativeEulerEndpointPrepared
