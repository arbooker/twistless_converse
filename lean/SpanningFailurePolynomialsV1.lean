module

public import SpanningAdditionFailureV1
public import SpanningShiftMatrixV1
public import SpanningFiniteEquationsV1

@[expose] public section

namespace SpanningFailurePolynomials

open scoped BigOperators
open SpanningPolynomialShift SpanningPolynomialDeterminants SpanningTraceAlgebra
  SpanningAdditionFailure SpanningAdditionCoordinates

variable {K:Type*} [Field K]

noncomputable def shiftAt (u:ℕ) (f:ℤ→K) (n:ℤ) : Polynomial K →ₗ[K] K where
  toFun p := shiftPolynomial p u f n
  map_add' p q := by
    change (p+q).sum (fun k a => a*f (n+(u*k:ℕ)))=_
    exact Polynomial.sum_add_index p q _ (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
  map_smul' c p := by
    change (c • p).sum (fun k a => a*f (n+(u*k:ℕ)))=c*_ 
    rw [Polynomial.sum_smul_index]
    · simp [Polynomial.sum,shiftPolynomial,mul_assoc,Finset.mul_sum]
    · intro k
      exact zero_mul _

theorem shiftAt_monomial (u:ℕ) (f:ℤ→K) (n:ℤ) (k:ℕ) (a:K) :
    shiftAt u f n (Polynomial.monomial k a)=a*f (n+(u*k:ℕ)) := by
  change (Polynomial.monomial k a).sum (fun k a => a*f (n+(u*k:ℕ)))=_
  exact Polynomial.sum_monomial_index a _ (zero_mul _)

theorem polynomial_row_action {I J:Type*} [Fintype I] [Fintype J]
    (a:J→I→K) (w:J→ℕ) (f:I→ℤ→K) (u:ℕ) (n:ℤ) :
    (∑i,shiftPolynomial (∑r,Polynomial.X^(w r)*Polynomial.C (a r i)) u (f i) n)=
      ∑r,∑i,a r i*f i (n+(u*w r:ℕ)) := by
  have he : ∀i,shiftPolynomial (∑r,Polynomial.X^(w r)*Polynomial.C (a r i)) u (f i) n=
      ∑r,a r i*f i (n+(u*w r:ℕ)) := by
    intro i
    change shiftAt u (f i) n (∑r,Polynomial.X^(w r)*Polynomial.C (a r i))=_
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_comm,Polynomial.C_mul_X_pow_eq_monomial,shiftAt_monomial]
  simp_rw [he]
  exact Finset.sum_comm

theorem coordinate_evaluation {I:Type*} [Fintype I] [DecidableEq I]
    {V:Submodule K (ℤ→K)} (e:(I→K)≃ₗ[K]V) (v:V) (n:ℤ) :
    (∑i,e.symm v i*(e (Pi.single i 1):ℤ→K) n)=(v:ℤ→K) n := by
  let g : (I→K)→ₗ[K]K := (LinearMap.proj n).comp (V.subtype.comp e.toLinearMap)
  exact (SpanningFiniteEquations.functional_coordinates g (e.symm v)).symm.trans (by
    change ((e (e.symm v)):ℤ→K) n=(v:ℤ→K) n
    rw [e.apply_symm_apply])

theorem relation_in_coordinates {I:Type*} [Fintype I] [DecidableEq I]
    {B:ℕ} {V:Submodule K (ℤ→K)} (e:(I→K)≃ₗ[K]V)
    (c:I→ℕ) (hc:∀i,Nat.Coprime (c i) B) (u:ℕ)
    (hu:NegativeInverse B (∏i,c i) u)
    (hcyc:∀v∈V,Cyclic B v)
    (t:I→ℤ) (ht:∀i,NegativeInverse B (c i) (t i))
    (v:∀i,Fin (c i)→V)
    (hv:∀i (n:ℤ),(∑r,(v i r:ℤ→K) (n+t i*r.val))=0) :
    ∀j,(∑i,shiftPolynomial
      (polynomialRows (fun j r => e.symm (v j r))
        (fun j r => r.val*SpanningCRTExponents.weight c j) j i) u
      (e (Pi.single i 1):ℤ→K))=0 := by
  intro j
  funext n
  simp only [Finset.sum_apply,Pi.zero_apply]
  change (∑i,shiftPolynomial
    (∑r,Polynomial.X^(r.val*SpanningCRTExponents.weight c j)*Polynomial.C (e.symm (v j r) i))
      u (e (Pi.single i 1):ℤ→K) n)=0
  rw [polynomial_row_action]
  simp_rw [coordinate_evaluation]
  convert hv j n using 1
  apply Finset.sum_congr rfl
  intro r _
  apply cyclic_eq_of_dvd (hcyc _ (v j r).property)
  have hd := common_step c hu j (hc j) (ht j)
  obtain ⟨z,hz⟩ := hd
  refine ⟨-z*r.val,?_⟩
  push_cast at hz ⊢
  nlinarith [congrArg (fun x:ℤ => x*r.val) hz]

#print axioms relation_in_coordinates

end SpanningFailurePolynomials
