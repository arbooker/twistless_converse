module

public import QuantitativeMaassCrossCompactBranchV1
public import QuantitativeMaassCrossCompactGeometryV1
public import QuantitativeMaassNormalizerRadialV1
public import QuantitativeHolomorphicMatrixExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels

namespace QuantitativeMaass.CrossCompactBranch

/-- The rational branch moves the source ball before the congruence
overlap is counted. Its displacement is retained explicitly. -/
theorem image_subset_ball (o : ℍ) (K : Set ℍ) (R Q : ℝ)
    (hK : K ⊆ Metric.closedBall o R) (q : AsymptoticRationalGroup.Group)
    (hq : dist (q • o) o ≤ Q) :
    (fun x : ℍ => q • x) '' K ⊆ Metric.closedBall o (R+Q) := by
  rintro y ⟨x,hx,rfl⟩
  have hx' : dist x o ≤ R := hK hx
  have ht := dist_triangle (q • x) (q • o) o
  rw [rationalNormalizer_action_dist] at ht
  exact ht.trans (add_le_add hx' hq)

/-- A uniform cardinal bound for the actual labels in the finite
localized expression, including cylinder level zero. -/
theorem overlap_card_bound (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L) (o : ℍ) (R S Q : ℝ)
    (hKR : K ⊆ Metric.closedBall o R) (hLS : L ⊆ Metric.closedBall o S)
    (q : AsymptoticRationalGroup.Group) (hq : dist (q • o) o ≤ Q) :
    (overlap N K L hK hL q).card ≤
      QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+Q+S) := by
  exact compact_overlap_card_bound N o ((fun x : ℍ => q • x) '' K) L
    (R+Q) S (image_subset_ball o K R Q hKR q hq) hLS
    (overlap N K L hK hL q)
    (fun g hg => (mem_overlap N K L hK hL q g).mp hg)

/-- The selected determinant-one congruence representative gives the
integer action of the actual projective congruence label. -/
theorem representative_integerAction (N : ℕ) (g : gamma N) :
    IntegerAction g.val (representative g).val := by
  refine ⟨?_,fun z => congruence_action_fractional N g z⟩
  rw [(representative g).property]
  exact one_ne_zero

/-- Both the integer representative and its height are explicit for
the composite label `g*q`; a bound for `g` alone would not suffice. -/
theorem overlap_product_matrix_bound (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L) (o : ℍ) (R S Q B : ℝ)
    (hKR : K ⊆ Metric.closedBall o R) (hLS : L ⊆ Metric.closedBall o S)
    (q : AsymptoticRationalGroup.Group) (hq : dist (q • o) o ≤ Q)
    (M : IntegerMatrix2) (hM : IntegerAction q M) (hMB : MatrixEntryBound M B)
    (g : gamma N) (hg : g ∈ overlap N K L hK hL q) :
    IntegerAction (g.val*q) ((representative g).val*M) ∧
      MatrixEntryBound ((representative g).val*M)
        (2*Real.exp ((R+Q+S)/2+dist o I)*B) := by
  refine ⟨(representative_integerAction N g).mul hM,?_⟩
  apply matrix_entry_bound_mul (Real.exp_pos _).le _ hMB
  exact compact_overlap_entry_bound N o ((fun x : ℍ => q • x) '' K) L
    (R+Q) S (image_subset_ball o K R Q hKR q hq) hLS g
    ((mem_overlap N K L hK hL q g).mp hg)

/-- A uniform height certificate for every branch of the finite
localized expression. This constructs the product integer matrix,
rather than choosing a new uncontrolled projective representative. -/
theorem localExpression_matrix_bound (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x, ‖b₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ B₂)
    (E : Expression) (o : ℍ) (R S Q B : ℝ)
    (hKR : K ⊆ Metric.closedBall o R) (hLS : L ⊆ Metric.closedBall o S)
    (hmotion : ∀ q ∈ E, dist (q.label • o) o ≤ Q)
    (hE : ExpressionMatrixBound E B) :
    ExpressionMatrixBound (localExpression N K L hK hL b₁ b₂ hb₁ hb₂
      B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E)
      (2*Real.exp ((R+Q+S)/2+dist o I)*B) := by
  intro a ha
  obtain ⟨q,hq,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ha
  obtain ⟨M,hM,hMB⟩ := hE q hq
  exact ⟨(representative g).val*M,
    overlap_product_matrix_bound N K L hK hL o R S Q B hKR hLS q.label
      (hmotion q hq) M hM hMB g (Finset.mem_toList.mp hg)⟩

#print axioms image_subset_ball
#print axioms overlap_card_bound
#print axioms representative_integerAction
#print axioms overlap_product_matrix_bound
#print axioms localExpression_matrix_bound

end QuantitativeMaass.CrossCompactBranch
