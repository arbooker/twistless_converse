module

public import AsymptoticAtkinLehnerSquareV1
public import AsymptoticQuotientLeftActionV1
public import AsymptoticSimpleOldAnnihilationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticSectorSigns

theorem sign_reverse (b : Bool) {u v : ℂ} (h : sign b*u=v) : u=sign b*v := by
  calc
    u=(sign b)^2*u := by rw [sign_sq,one_mul]
    _=sign b*v := by rw [pow_two,mul_assoc,h]

#print axioms sign_reverse

end AsymptoticSectorSigns

namespace AsymptoticCosetSectorOrthogonality

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticSectorSigns AsymptoticFreshMatrices AsymptoticOrbitDecode InnerProductSpace
open AsymptoticPermutationEigenvectors
open scoped lp InnerProduct

/-- Different global Fricke signs are orthogonal on counting cosets. -/
theorem fricke_inner_eq_zero (N : ℕ) (hN : 0<N)
    (f g : ℓ²(Classes (gamma N),ℂ)) (a b : Bool) (hab : a≠b)
    (hf : ∀ u,sign a*f (classOf (gamma N) (frickeLabel N hN*u))=f (classOf (gamma N) u))
    (hg : ∀ u,sign b*g (classOf (gamma N) (frickeLabel N hN*u))=g (classOf (gamma N) u)) :
    ⟪f,g⟫_ℂ=0 := by
  have hw : ∀ u∈gamma N,frickeLabel N hN*u*(frickeLabel N hN)⁻¹∈gamma N :=
    fun _ hu => fricke_conj_mem N hN hu
  have hwi : ∀ u∈gamma N,(frickeLabel N hN)⁻¹*u*frickeLabel N hN∈gamma N := by
    intro u hu
    simpa only [frickeLabel_inv] using hw u hu
  apply inner_eq_zero_of_signs (leftMulEquiv (gamma N) (frickeLabel N hN) hw hwi) f g a b hab
  · intro q
    induction q using Quotient.inductionOn with
    | h u => exact sign_reverse a (hf u)
  · intro q
    induction q using Quotient.inductionOn with
    | h u => exact sign_reverse b (hg u)

/-- At a simple prime, the original Fricke and ramified equations imply
orthogonality of different ramified signs via the literal local Atkin
normalizer. No spectral or sector-dimension assertion is assumed. -/
theorem simple_inner_eq_zero (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M)
    (f g : ℓ²(Classes (gamma (p*M)),ℂ)) (wf wg : ℂ) (a b : Bool) (hab : a≠b)
    (hfW : ∀ u,wf*f (classOf (gamma (p*M))
      (frickeLabel (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)*u))=f (classOf (gamma (p*M)) u))
    (hgW : ∀ u,wg*g (classOf (gamma (p*M))
      (frickeLabel (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)*u))=g (classOf (gamma (p*M)) u))
    (hfU : ∀ u,∑ j : Fin p,f (classOf (gamma (p*M)) (ramifiedLabel p (Fact.out : p.Prime).pos j*u))=
      sign a*f (classOf (gamma (p*M)) u))
    (hgU : ∀ u,∑ j : Fin p,g (classOf (gamma (p*M)) (ramifiedLabel p (Fact.out : p.Prime).pos j*u))=
      sign b*g (classOf (gamma (p*M)) u)) : ⟪f,g⟫_ℂ=0 := by
  have hc : p.Coprime M := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have hAB : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    have hh := Nat.gcd_eq_gcd_ab p M
    rw [hc.gcd_eq_one,Nat.cast_one] at hh
    exact hh.symm
  let W := AsymptoticAtkinLehner.localAtkin M p hM (Fact.out : p.Prime).pos
    (Nat.gcdA p M) (Nat.gcdB p M) hAB
  have hw : ∀ u∈gamma (p*M),W*u*W⁻¹∈gamma (p*M) :=
    fun _ hu => AsymptoticAtkinLehner.local_conj_mem M p hM (Fact.out : p.Prime).pos
      (Nat.gcdA p M) (Nat.gcdB p M) hAB hu
  have hwi : ∀ u∈gamma (p*M),W⁻¹*u*W∈gamma (p*M) :=
    fun _ hu => AsymptoticAtkinLehner.local_inv_conj_mem M p hM (Fact.out : p.Prime).pos
      (Nat.gcdA p M) (Nat.gcdB p M) hAB hu
  apply inner_eq_zero_of_neg_signs (leftMulEquiv (gamma (p*M)) W hw hwi) f g a b hab
  · intro q
    induction q using Quotient.inductionOn with
    | h u =>
      exact AsymptoticAtkinLehner.local_eigen M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB
        (fun v => f (classOf (gamma (p*M)) v))
        (fun v u => congrArg f (classOf_mul (gamma (p*M)) v u))
        wf (sign a) (sign_sq a) hfW hfU u
  · intro q
    induction q using Quotient.inductionOn with
    | h u =>
      exact AsymptoticAtkinLehner.local_eigen M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB
        (fun v => g (classOf (gamma (p*M)) v))
        (fun v u => congrArg g (classOf_mul (gamma (p*M)) v u))
        wg (sign b) (sign_sq b) hgW hgU u

#print axioms fricke_inner_eq_zero
#print axioms simple_inner_eq_zero

end AsymptoticCosetSectorOrthogonality
