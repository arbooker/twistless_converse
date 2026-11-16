module

public import QuantitativeMaassAdmissibleDivisorEigenV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticSectorSigns AsymptoticFreshMatrices
namespace QuantitativeMaass.CountingMetric

variable (N : ℕ) (hN : 0<N) (K : Subgroup AsymptoticRationalGroup.Group) (hK : gamma N≤K)
include hK

theorem generator_mem_congr (Q : ℕ) (i j : admissibleGeneratorIndex N hN)
    (hi : generatorAtDivisor N hN Q i) (hj : generatorAtDivisor N hN Q j) :
    i.val∈K ↔ j.val∈K := by
  obtain ⟨D,hQ,A,B,hAB,hND,hi⟩ := hi
  obtain ⟨D',hQ',A',B',hAB',hND',hj⟩ := hj
  have hd : D'=D := Nat.eq_of_mul_eq_mul_left hQ (hND'.trans hND.symm)
  subst D'
  obtain ⟨a,ha⟩ := exactAtkin_choice_mod_gamma D Q hQ A' B' A B hAB' hAB
  have haK : a.val∈K := hK (by simpa only [hND] using a.property)
  rw [hi,hj,←ha]
  exact K.mul_mem_cancel_left haK

def divisorMem (Q : ℕ) : Prop :=
  ∀ i : admissibleGeneratorIndex N hN,generatorAtDivisor N hN Q i → i.val∈K

theorem generator_product_mem_iff
    (D P Q : ℕ) (hP : 0<P) (hQ : 0<Q) (hND : (P*Q)*D=N)
    (A B C E U V : ℤ)
    (hAB : (P:ℤ)*A+((Q*D:ℕ):ℤ)*B=1)
    (hCE : (Q:ℤ)*C+((P*D:ℕ):ℤ)*E=1)
    (hUV : ((P*Q:ℕ):ℤ)*U+(D:ℤ)*V=1)
    (i j k : admissibleGeneratorIndex N hN)
    (hi : i.val=exactAtkinLabel (Q*D) P hP A B hAB)
    (hj : j.val=exactAtkinLabel (P*D) Q hQ C E hCE)
    (hk : k.val=exactAtkinLabel D (P*Q) (Nat.mul_pos hP hQ) U V hUV) :
    i.val*j.val∈K ↔ k.val∈K := by
  obtain ⟨a,ha⟩ := exactAtkin_product_mod_gamma D P Q hP hQ A B C E U V hAB hCE hUV
  have haK : a.val∈K := hK (by simpa only [hND] using a.property)
  rw [hi,hj,hk,ha]
  exact K.mul_mem_cancel_left haK


#print axioms generator_mem_congr
#print axioms generator_product_mem_iff
end QuantitativeMaass.CountingMetric
