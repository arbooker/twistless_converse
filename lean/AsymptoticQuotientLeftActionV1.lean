module

public import AsymptoticQuotientRightActionV1
public import AsymptoticSectorSignsV1
public import AsymptoticRegularAlgebraV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticNestedQuotients

variable {G : Type*} [Group G]

/-- A normalizer acts by a permutation of the counting cosets. -/
def leftMulEquiv (H : Subgroup G) (a : G)
    (ha : ∀ g∈H,a*g*a⁻¹∈H) (hai : ∀ g∈H,a⁻¹*g*a∈H) : Classes H ≃ Classes H where
  toFun := Quotient.map (fun g => a*g) (by
    intro g h he
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev,mul_assoc] using ha (h*g⁻¹) (QuotientGroup.rightRel_apply.mp he))
  invFun := Quotient.map (fun g => a⁻¹*g) (by
    intro g h he
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev,inv_inv,mul_assoc] using hai (h*g⁻¹) (QuotientGroup.rightRel_apply.mp he))
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      change classOf H (a⁻¹*(a*g))=classOf H g
      rw [inv_mul_cancel_left]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      change classOf H (a*(a⁻¹*g))=classOf H g
      rw [mul_inv_cancel_left]

theorem leftMulEquiv_classOf (H : Subgroup G) (a : G)
    (ha : ∀ g∈H,a*g*a⁻¹∈H) (hai : ∀ g∈H,a⁻¹*g*a∈H) (g : G) :
    leftMulEquiv H a ha hai (classOf H g)=classOf H (a*g) := rfl

#print axioms leftMulEquiv_classOf

end AsymptoticNestedQuotients

namespace AsymptoticPermutationEigenvectors

open InnerProductSpace AsymptoticSectorSigns
open scoped lp InnerProduct ComplexConjugate

/-- Eigenvectors for a counting permutation are orthogonal when their
unit-modulus eigenvalues are distinct. The hypothesis is stated directly
in the conjugate-product form needed by the inner product. -/
theorem inner_eq_zero_of_eigenvalues {ι : Type*} (e : ι ≃ ι)
    (f g : ℓ²(ι,ℂ)) (a b : ℂ) (hab : conj a*b≠1)
    (hf : ∀ i,f (e i)=a*f i) (hg : ∀ i,g (e i)=b*g i) : ⟪f,g⟫_ℂ=0 := by
  have he : ⟪f,g⟫_ℂ=(conj a*b)*⟪f,g⟫_ℂ := by
    calc
      ⟪f,g⟫_ℂ=∑' i,⟪f (e i),g (e i)⟫_ℂ := by
        rw [lp.inner_eq_tsum]
        exact (e.tsum_eq (fun i => ⟪f i,g i⟫_ℂ)).symm
      _=∑' i,(conj a*b)*⟪f i,g i⟫_ℂ := by
        apply tsum_congr
        intro i
        rw [hf,hg]
        simp only [RCLike.inner_apply,map_mul]
        ring
      _=(conj a*b)*⟪f,g⟫_ℂ := by rw [tsum_mul_left,← lp.inner_eq_tsum]
  have hz : (1-conj a*b)*⟪f,g⟫_ℂ=0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab.symm)

theorem inner_eq_zero_of_signs {ι : Type*} (e : ι ≃ ι)
    (f g : ℓ²(ι,ℂ)) (a b : Bool) (hab : a≠b)
    (hf : ∀ i,f (e i)=sign a*f i) (hg : ∀ i,g (e i)=sign b*g i) : ⟪f,g⟫_ℂ=0 := by
  apply inner_eq_zero_of_eigenvalues e f g (sign a) (sign b) _ hf hg
  cases a <;> cases b <;> simp_all [sign]
  all_goals norm_num

theorem inner_eq_zero_of_neg_signs {ι : Type*} (e : ι ≃ ι)
    (f g : ℓ²(ι,ℂ)) (a b : Bool) (hab : a≠b)
    (hf : ∀ i,f (e i)= -sign a*f i) (hg : ∀ i,g (e i)= -sign b*g i) : ⟪f,g⟫_ℂ=0 := by
  apply inner_eq_zero_of_eigenvalues e f g (-sign a) (-sign b) _ hf hg
  cases a <;> cases b <;> simp_all [sign]
  all_goals norm_num

#print axioms inner_eq_zero_of_eigenvalues
#print axioms inner_eq_zero_of_signs
#print axioms inner_eq_zero_of_neg_signs

end AsymptoticPermutationEigenvectors
