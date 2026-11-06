module

public import SpanningSpectralCoordinatesV1
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

namespace SpanningPolynomialShift

open SpanningSpectralCoordinates SpanningSpectralUncertainty SpanningTraceAlgebra

variable {K : Type*} [Field K] {Q : ℕ}

def shiftPolynomial (p : Polynomial K) (u : ℕ) (f : ℤ → K) (n : ℤ) : K :=
  ∑k∈p.support,p.coeff k*f (n+(u*k:ℕ))

theorem shift_exponential {z : Fin Q → K} (hz0 : ∀i,z i≠0)
    (a : Fin Q → K) (p : Polynomial K) (u : ℕ) :
    shiftPolynomial p u (exponentialWord z a)=
      exponentialWord z (fun i => a i*p.eval (z i^u)) := by
  funext n
  unfold shiftPolynomial exponentialWord
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_eq_sum,Polynomial.sum]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [zpow_add₀ (hz0 i),zpow_natCast,pow_mul]
  ring

theorem exponentialWord_injective {z : Fin Q → K} (hi : Function.Injective z) :
    Function.Injective (exponentialWord z) := by
  intro a b hab
  apply momentMap_injective hi
  rw [←exponentialWord_coordinates,←exponentialWord_coordinates,hab]

theorem no_small_shift_annihilator {ζ : K} (hQ : 0<Q) (hζ : IsPrimitiveRoot ζ Q)
    (u : ℕ) (hu : Nat.Coprime u Q) {L : ℕ}
    (f : ℤ → K) (hf : Cyclic Q f) (hf0 : f≠0)
    (hzero : ∀j:ℕ,j<L → f j=0) (p : Polynomial K) (hdeg : p.natDegree≤L)
    (hann : shiftPolynomial p u f=0) : p=0 := by
  let z := fun i:Fin Q => ζ^i.val
  have hi : Function.Injective z := fun i j he => Fin.ext (hζ.pow_inj i.isLt j.isLt he)
  have hz0 : ∀i,z i≠0 := fun i => pow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hQ))
  have hzQ : ∀i,z i^Q=1 := by
    intro i
    dsimp [z]
    rw [←pow_mul,mul_comm i.val Q,pow_mul,hζ.pow_eq_one,one_pow]
  obtain ⟨a,ha,_⟩ := exponential_expansion hQ hi hz0 hzQ f hf
  have ha0 : a≠0 := by
    intro he
    apply hf0
    rw [←ha,he]
    funext n
    simp [exponentialWord]
  have hw : Function.Injective (fun i:Fin Q => z i^u) := by
    intro i j he
    apply Fin.ext
    have hp := hζ.pow_of_coprime u hu
    apply hp.pow_inj i.isLt j.isLt
    simpa only [z,←pow_mul,Nat.mul_comm u] using he
  apply no_small_polynomial_annihilator hi hz0 hw 0 ha0 (p:=p) (hdeg:=hdeg)
  · intro j hj
    have he := congrFun ha (j:ℤ)
    simpa only [zero_add,exponentialWord,zpow_natCast] using he.trans (hzero j hj)
  · have he : exponentialWord z (fun i => a i*p.eval (z i^u))=exponentialWord z 0 := by
      rw [←shift_exponential hz0 a p u,ha,hann]
      funext n
      simp [exponentialWord]
    have hc := exponentialWord_injective hi he
    exact fun i => congrFun hc i

#print axioms no_small_shift_annihilator

end SpanningPolynomialShift
