module

public import QuantitativeNewGapTreeArithmeticDilationV1
public import AsymptoticQuotientEquivarianceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticQuotientOperators AsymptoticRegularTrace
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticPermutationInvariant
open scoped lp

/-- The root vector is separating for equivariant quotient operators.
Its zero column propagates to every column by the transitive right action. -/
theorem quotient_root_faithful {G : Type*} [Group G] (H : Subgroup G)
    (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) (hB : Equivariant B)
    (hz : B (delta (classOf H 1))=0) : B=0 := by
  apply eq_zero_of_columns
  intro q
  apply norm_eq_zero.mp
  have he := congrArg Complex.re (equivariant_diagonal (B.adjoint.comp B)
    (equivariant_comp _ _ (equivariant_adjoint B hB) hB) q)
  rw [matrix_gram,matrix_gram,hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] at he
  nlinarith [norm_nonneg (B (delta q))]

/-- Every root diagonal of a Gram operator detects the entire equivariant
operator; this supplies faithfulness without a cyclic-vector assumption. -/
theorem quotient_gram_root_faithful {G : Type*} [Group G] (H : Subgroup G)
    (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) (hB : Equivariant B)
    (hz : (matrix (B.adjoint.comp B) (classOf H 1) (classOf H 1)).re=0) : B=0 := by
  apply quotient_root_faithful H B hB
  apply norm_eq_zero.mp
  rw [matrix_gram] at hz
  nlinarith [norm_nonneg (B (delta (classOf H 1)))]

/-- The literal arithmetic Hecke operator has the required right-translation
symmetry on all quotient coordinates, proved from its finite branch formula. -/
theorem regularHecke_equivariant (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) : Equivariant (regularHecke M p) := by
  classical
  intro a q r
  induction q using Quotient.inductionOn with
  | h g =>
    change regularHecke M p (delta (rightMulEquiv (gamma M) a r))
      (classOf (gamma M) (g*a)) = regularHecke M p (delta r) (classOf (gamma M) g)
    rw [regularHecke_apply_prime M p hpM,regularHecke_apply_prime M p hpM]
    have he (x : AsymptoticRationalGroup.Group) :
        delta (rightMulEquiv (gamma M) a r) (classOf (gamma M) (x*a)) =
          delta r (classOf (gamma M) x) := by
      change delta (rightMulEquiv (gamma M) a r)
        (rightMulEquiv (gamma M) a (classOf (gamma M) x)) = _
      simp [delta,Pi.single_apply,(rightMulEquiv (gamma M) a).injective.eq_iff]
    simp_rw [← mul_assoc,he]

#print axioms quotient_root_faithful
#print axioms quotient_gram_root_faithful
#print axioms regularHecke_equivariant

end QuantitativeNewGap
