module

public import SpanningMixedDeterminantsV1
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

namespace SpanningPolynomialDeterminants

open scoped BigOperators
open Polynomial

variable {I K:Type*} [Fintype I] [DecidableEq I] [Field K]
variable {J:I→Type*} [∀i,Fintype (J i)]

noncomputable def polynomialRows (a:∀i,J i→I→K) (w:∀i,J i→ℕ) :
    Matrix I I K[X] :=
  fun i k => ∑j,X^(w i j)*C (a i j k)

theorem determinant_expansion (a:∀i,J i→I→K) (w:∀i,J i→ℕ) :
    (polynomialRows a w).det =
      ∑j:∀i,J i,monomial (∑i,w i (j i)) (Matrix.det (fun i => a i (j i))) := by
  classical
  let F := (Matrix.detRowAlternating : (I→K[X]) [⋀^I]→ₗ[K[X]] K[X]).toMultilinearMap
  have he : polynomialRows a w = (fun i => ∑j,((X:K[X])^(w i j)) • (fun k => C (a i j k))) := by
    ext i k
    simp [polynomialRows,Finset.sum_apply]
  change F (polynomialRows a w)=_
  rw [he,F.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [F.map_smul_univ]
  change (∏i,X^(w i (j i))) * Matrix.det (fun i k => C (a i (j i) k))=_
  have hd := RingHom.map_det (C:K→+*K[X]) (Matrix.of (fun i => a i (j i)))
  change C (Matrix.det (fun i => a i (j i))) = Matrix.det (fun i k => C (a i (j i) k)) at hd
  rw [←hd,Finset.prod_pow_eq_pow_sum,mul_comm,C_mul_X_pow_eq_monomial]

theorem mixed_determinants_zero (a:∀i,J i→I→K) (w:∀i,J i→ℕ)
    (hw:Function.Injective (fun j:∀i,J i => ∑i,w i (j i)))
    (hz:(polynomialRows a w).det=0) :
    ∀j:∀i,J i,Matrix.det (fun i => a i (j i))=0 := by
  classical
  intro j
  have he := congrArg (fun p:K[X] => p.coeff (∑i,w i (j i))) hz
  rw [determinant_expansion,finsetSum_coeff,coeff_zero] at he
  have hs : (∑j':∀i,J i,(monomial (∑i,w i (j' i))
      (Matrix.det (fun i => a i (j' i)))).coeff (∑i,w i (j i)))=
      Matrix.det (fun i => a i (j i)) := by
    rw [Finset.sum_eq_single j]
    · exact coeff_monomial_same _ _
    · intro j' _ hne
      exact coeff_monomial_of_ne _ (fun heq => hne (hw heq).symm)
    · simp
  rw [hs] at he
  exact he

theorem determinant_degree_bound (a:∀i,J i→I→K) (w:∀i,J i→ℕ) (L:ℕ)
    (hL:∀j:∀i,J i,(∑i,w i (j i))≤L) :
    (polynomialRows a w).det.natDegree≤L := by
  rw [determinant_expansion]
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_monomial_le _).trans (hL j)

#print axioms mixed_determinants_zero
#print axioms determinant_degree_bound

end SpanningPolynomialDeterminants
