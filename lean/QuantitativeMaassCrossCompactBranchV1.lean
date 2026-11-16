module

public import QuantitativeMaassQuotientExpressionBaseV1
public import QuantitativeMaassPoincareQuotientDenseV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass.CrossCompactBranch

/-- Only these projective congruence labels can connect the two compact
supports after the displayed rational branch. No central labels are repeated. -/
theorem overlap_finite (N : ℕ) (K L : Set ℍ) (hK : IsCompact K)
    (hL : IsCompact L) (q : AsymptoticRationalGroup.Group) :
    {g : gamma N | ((fun x : ℍ => g • x) ''
      ((fun x : ℍ => q • x) '' K) ∩ L).Nonempty}.Finite := by
  exact ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := gamma N)
    (hK.image (AsymptoticRationalBranches.action_continuous q)) hL

def overlap (N : ℕ) (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (q : AsymptoticRationalGroup.Group) : Finset (gamma N) :=
  (overlap_finite N K L hK hL q).toFinset

theorem mem_overlap (N : ℕ) (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (q : AsymptoticRationalGroup.Group) (g : gamma N) :
    g ∈ overlap N K L hK hL q ↔
      ((fun x : ℍ => g • x) '' ((fun x : ℍ => q • x) '' K) ∩ L).Nonempty := by
  classical
  exact (overlap_finite N K L hK hL q).mem_toFinset

/-- This finite truncation is valid for every function `f`; smoothness and
integrability of `f` are unnecessary for the pointwise identity. -/
theorem poincare_eq_overlap (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L)
    (b f : ℍ → ℂ) (hb : tsupport b ⊆ L)
    (q : AsymptoticRationalGroup.Group) (x : ℍ) (hx : x ∈ K) :
    poincareSum (G := gamma N) (fun y => b y*f y) (q • x) =
      ∑ g ∈ overlap N K L hK hL q, b (g • (q • x))*f (g • (q • x)) := by
  classical
  apply tsum_eq_sum
  intro g hg
  have hz : g • (q • x) ∉ L := by
    intro hz
    apply hg
    apply (mem_overlap N K L hK hL q g).mpr
    exact ⟨g • (q • x), ⟨q • x, ⟨x,hx,rfl⟩,rfl⟩,hz⟩
  have hbz : b (g • (q • x)) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (hb h))
  change b (g • (q • x))*f (g • (q • x)) = 0
  rw [hbz,zero_mul]

/-- A genuine bounded common branch, retaining both cutoff factors. The
label order is `g.val*q.label`, since periodization acts after `q`. -/
def localBranch (N : ℕ) (b₁ b₂ : ℍ → ℂ)
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x, ‖b₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ B₂)
    (q : Branch) (g : gamma N) : Branch where
  label := g.val*q.label
  coefficient x := star (b₁ x)*q.coefficient x*b₂ ((g.val*q.label) • x)
  measurable := by
    have ha := (AsymptoticRationalBranches.action_continuous (g.val*q.label)).measurable
    exact ((continuous_star.measurable.comp hb₁).mul q.measurable).mul (hb₂.comp ha)
  bound := B₁*q.bound*B₂
  bound_nonneg := mul_nonneg (mul_nonneg hB₁ q.bound_nonneg) hB₂
  norm_le x := by
    simp only [norm_mul,norm_star]
    exact mul_le_mul
      (mul_le_mul (hbound₁ x) (q.norm_le x) (norm_nonneg _) hB₁)
      (hbound₂ _) (norm_nonneg _) (mul_nonneg hB₁ q.bound_nonneg)

/-- The explicit finite list replacing localized Poincare summation. Its
construction uses only compact overlap and the original finite expression. -/
def localExpression (N : ℕ) (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x, ‖b₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ B₂)
    (E : Expression) : Expression :=
  E.flatMap (fun q => ofFinset (overlap N K L hK hL q.label)
    (localBranch N b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q))

theorem branch_expansion (N : ℕ) (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (hs₁ : tsupport b₁ ⊆ K) (hs₂ : tsupport b₂ ⊆ L)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x, ‖b₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ B₂)
    (q : Branch) (f : ℍ → ℂ) (x : ℍ) :
    star (b₁ x)*(q.coefficient x*
      poincareSum (G := gamma N) (fun y => b₂ y*f y) (q.label • x)) =
      expressionFunction (ofFinset (overlap N K L hK hL q.label)
        (localBranch N b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q)) f x := by
  classical
  rw [expressionFunction_ofFinset]
  simp only [LinearMap.sum_apply,Finset.sum_apply]
  change _ = ∑ g ∈ overlap N K L hK hL q.label,
    (star (b₁ x)*q.coefficient x*b₂ ((g.val*q.label) • x))*f ((g.val*q.label) • x)
  by_cases hx : x ∈ K
  · rw [poincare_eq_overlap N K L hK hL b₂ f hs₂ q.label x hx]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    change star (b₁ x)*(q.coefficient x*(b₂ (g.val • (q.label • x))*
      f (g.val • (q.label • x)))) = _
    rw [mul_smul]
    ring
  · have hb : b₁ x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs₁ h))
    simp only [hb,star_zero,zero_mul,Finset.sum_const_zero]

/-- Exact compact-transfer expression identity, before any Hilbert-space
identification or wave insertion. The two cutoffs stay in their original
positions and no cuspidal or spectral approximation is assumed. -/
theorem expression_expansion (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (hs₁ : tsupport b₁ ⊆ K) (hs₂ : tsupport b₂ ⊆ L)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x, ‖b₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ B₂)
    (E : Expression) (f : ℍ → ℂ) (x : ℍ) :
    star (b₁ x)*expressionFunction E
      (poincareSum (G := gamma N) (fun y => b₂ y*f y)) x =
      expressionFunction (localExpression N K L hK hL b₁ b₂ hb₁ hb₂
        B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E) f x := by
  induction E with
  | nil => simp [localExpression,expressionFunction]
  | cons q E ih =>
    rw [localExpression,List.flatMap_cons,expressionFunction_append]
    change star (b₁ x)*(q.coefficient x*
      poincareSum (G := gamma N) (fun y => b₂ y*f y) (q.label • x)+
        expressionFunction E (poincareSum (G := gamma N) (fun y => b₂ y*f y)) x) =
      expressionFunction (ofFinset (overlap N K L hK hL q.label)
        (localBranch N b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q)) f x+
      expressionFunction (localExpression N K L hK hL b₁ b₂ hb₁ hb₂
        B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E) f x
    rw [mul_add,branch_expansion N K L hK hL b₁ b₂ hb₁ hb₂ hs₁ hs₂
      B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q f x,ih]

/-- The coefficient cost keeps every overlap cardinal explicit. Further
quantitative geometry must bound these cardinals; finiteness alone is not
an asymptotic trace estimate. -/
theorem localExpression_bound (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x, ‖b₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ B₂)
    (E : Expression) :
    expressionBound (localExpression N K L hK hL b₁ b₂ hb₁ hb₂
      B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E) =
      (E.map (fun q => ((overlap N K L hK hL q.label).card : ℝ)*
        (B₁*q.bound*B₂))).sum := by
  induction E with
  | nil => simp [localExpression,expressionBound]
  | cons q E ih =>
    have hhead : expressionBound (ofFinset (overlap N K L hK hL q.label)
        (localBranch N b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q)) =
        ((overlap N K L hK hL q.label).card : ℝ)*(B₁*q.bound*B₂) := by
      simp [expressionBound,ofFinset,localBranch,List.map_map,Finset.sum_map_toList]
    change expressionBound (_ ++ localExpression N K L hK hL b₁ b₂ hb₁ hb₂
      B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E) = _
    rw [show ∀ F G : Expression, expressionBound (F++G)=expressionBound F+expressionBound G
      from fun F G => by simp only [expressionBound,List.map_append,List.sum_append]]
    rw [hhead,ih]
    rfl

/-- Local bounds for a supported cutoff give the global branch bounds
required above. In particular this applies to `upperFunction b.toFun`
for every compact smooth cutoff seed. -/
theorem cutoff_global_bound (b : ℍ → ℂ) (K : Set ℍ)
    (hs : tsupport b ⊆ K) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x ∈ K, ‖b x‖ ≤ B) : ∀ x, ‖b x‖ ≤ B := by
  intro x
  by_cases hx : x ∈ K
  · exact hb x hx
  · have hz : b x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    simpa only [hz,norm_zero] using hB

#print axioms overlap_finite
#print axioms poincare_eq_overlap
#print axioms branch_expansion
#print axioms expression_expansion
#print axioms localExpression_bound

end QuantitativeMaass.CrossCompactBranch
