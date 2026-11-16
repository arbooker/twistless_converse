module

public import QuantitativeMaassCrossCompactBranchV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticCongruenceStrip AsymptoticRegularTrace ContinuousLinearMap
namespace QuantitativeMaass.CrossCompactBranch

attribute [local instance] Classical.propDecidable

/-- A regular diagonal selects the identity group label, without any
assumption that the action on the upper half plane is free. -/
theorem regularSum_identity_coefficient (E : Expression) (x : ℍ) :
    matrix (regularSum E x) 1 1 =
      (E.map (fun q => if q.label=1 then q.coefficient x else 0)).sum := by
  classical
  have hb (q : Branch) : matrix (regular q x) 1 1 = if q.label=1 then q.coefficient x else 0 := by
    simp only [regular,AsymptoticOrbitBranch.operator_matrix,mul_one,one_smul]
  induction E with
  | nil => simp [regularSum,AsymptoticRegularTrace.matrix]
  | cons q E ih =>
    change matrix (regular q x+regularSum E x) 1 1 = _
    change matrix (regular q x) 1 1+matrix (regularSum E x) 1 1 = _
    rw [hb,ih]
    rfl

/-- The localized returning label is unique. It exists exactly when
the original rational label belongs to the congruence subgroup. -/
theorem localBranch_regular_diagonal (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ→ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (B₁ B₂ : ℝ) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (hbound₁ : ∀ x,‖b₁ x‖≤B₁) (hbound₂ : ∀ x,‖b₂ x‖≤B₂)
    (q : Branch) (x : ℍ) (hxK : x∈K) (hxL : x∈L) :
    matrix (regularSum (ofFinset (overlap N K L hK hL q.label)
      (localBranch N b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q)) x) 1 1 =
      if q.label∈gamma N then star (b₁ x)*q.coefficient x*b₂ x else 0 := by
  classical
  rw [regularSum_ofFinset]
  simp only [AsymptoticRegularTrace.matrix,sum_apply,lp.coeFn_sum,Finset.sum_apply]
  change (∑ g∈overlap N K L hK hL q.label,
    matrix (regular (localBranch N b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q g) x) 1 1) = _
  have hdiag (g : gamma N) :
      matrix (regular (localBranch N b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q g) x) 1 1 =
        if g.val*q.label=1 then star (b₁ x)*q.coefficient x*b₂ x else 0 := by
    simp only [regular,AsymptoticOrbitBranch.operator_matrix,localBranch,mul_one,one_smul]
    split_ifs with hg
    · rw [hg,one_smul]
    · rfl
  simp_rw [hdiag]
  by_cases hq : q.label∈gamma N
  · rw [ite_eq_left hq]
    let g₀ : gamma N := ⟨q.label⁻¹,(gamma N).inv_mem hq⟩
    have hg₀ : g₀∈overlap N K L hK hL q.label := by
      apply (mem_overlap N K L hK hL q.label g₀).mpr
      refine ⟨x,?_,hxL⟩
      refine ⟨q.label•x,⟨x,hxK,rfl⟩,?_⟩
      change q.label⁻¹•(q.label•x)=x
      exact inv_smul_smul _ _
    rw [Finset.sum_eq_single g₀]
    · simp [g₀]
    · intro g _ hne
      apply ite_eq_right
      intro he
      apply hne
      apply Subtype.ext
      exact mul_eq_one_iff_eq_inv.mp he
    · exact fun h => (h hg₀).elim
  · rw [ite_eq_right hq]
    apply Finset.sum_eq_zero
    intro g _
    apply ite_eq_right
    intro he
    apply hq
    have hg : q.label=g.val⁻¹ := by
      calc
        q.label = g.val⁻¹*(g.val*q.label) := by group
        _ = g.val⁻¹ := by rw [he,mul_one]
    rw [hg]
    exact (gamma N).inv_mem g.property

/-- Both cutoffs survive the regular main coefficient. No quotient
projection or spectral approximation is substituted in this identity. -/
theorem localExpression_regular_diagonal (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ→ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (B₁ B₂ : ℝ) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (hbound₁ : ∀ x,‖b₁ x‖≤B₁) (hbound₂ : ∀ x,‖b₂ x‖≤B₂)
    (E : Expression) (x : ℍ) (hxK : x∈K) (hxL : x∈L) :
    matrix (regularSum (localExpression N K L hK hL b₁ b₂ hb₁ hb₂
      B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E) x) 1 1 =
      star (b₁ x)*((E.map (fun q => if q.label∈gamma N then q.coefficient x else 0)).sum)*b₂ x := by
  classical
  induction E with
  | nil => simp [localExpression,regularSum,AsymptoticRegularTrace.matrix]
  | cons q E ih =>
    rw [localExpression,List.flatMap_cons,regularSum_append]
    change matrix (regularSum (ofFinset (overlap N K L hK hL q.label)
      (localBranch N b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ q)) x) 1 1+
      matrix (regularSum (localExpression N K L hK hL b₁ b₂ hb₁ hb₂
        B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E) x) 1 1 = _
    rw [localBranch_regular_diagonal N K L hK hL b₁ b₂ hb₁ hb₂ B₁ B₂ hB₁ hB₂
      hbound₁ hbound₂ q x hxK hxL,ih]
    simp only [List.map_cons,List.sum_cons]
    split_ifs <;> ring

#print axioms regularSum_identity_coefficient
#print axioms localBranch_regular_diagonal
#print axioms localExpression_regular_diagonal

end QuantitativeMaass.CrossCompactBranch
