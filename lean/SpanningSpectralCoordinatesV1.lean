module

public import SpanningSpectralUncertaintyV1
public import SpanningCyclicCoordinatesV1
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace SpanningSpectralCoordinates

open SpanningVandermonde SpanningTraceAlgebra SpanningCyclicCoordinates

variable {K : Type*} [Field K] {Q : ℕ}

def momentMap (z : Fin Q → K) : (Fin Q → K) →ₗ[K] (Fin Q → K) where
  toFun a j := ∑i,a i*z i^j.val
  map_add' a b := by ext j; simp [add_mul,Finset.sum_add_distrib]
  map_smul' c a := by ext j; simp [Finset.mul_sum,mul_assoc]

theorem momentMap_injective {z : Fin Q → K} (hi : Function.Injective z) :
    Function.Injective (momentMap z) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hi (fun j => congrFun ha j)

noncomputable def momentEquiv {z : Fin Q → K} (hi : Function.Injective z) :
    (Fin Q → K) ≃ₗ[K] (Fin Q → K) :=
  LinearEquiv.ofBijective (momentMap z)
    ⟨momentMap_injective hi,LinearMap.injective_iff_surjective.mp (momentMap_injective hi)⟩

def exponentialWord (z a : Fin Q → K) (n : ℤ) : K := ∑i,a i*z i^n

theorem exponentialWord_cyclic {z : Fin Q → K} (hz0 : ∀i,z i≠0)
    (hQ : ∀i,z i^Q=1) (a : Fin Q → K) : Cyclic Q (exponentialWord z a) := by
  intro n
  unfold exponentialWord
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_add₀ (hz0 i),zpow_natCast,hQ,mul_one]

theorem exponentialWord_coordinates (z a : Fin Q → K) :
    coordinates (exponentialWord z a)=momentMap z a := by
  ext j
  simp [coordinates,exponentialWord,momentMap]

theorem exponential_expansion {z : Fin Q → K} (hQ : 0<Q)
    (hi : Function.Injective z) (hz0 : ∀i,z i≠0) (hzQ : ∀i,z i^Q=1)
    (f : ℤ → K) (hf : Cyclic Q f) :
    ∃!a:Fin Q → K,exponentialWord z a=f := by
  let a := (momentEquiv hi).symm (coordinates f)
  have hcoords : coordinates (Q:=Q) (exponentialWord z a)=coordinates f := by
    rw [exponentialWord_coordinates]
    exact (momentEquiv hi).apply_symm_apply (coordinates f)
  have he : exponentialWord z a=f := by
    rw [←extend_coordinates hQ (exponentialWord_cyclic hz0 hzQ a),hcoords,extend_coordinates hQ hf]
  refine ⟨a,he,?_⟩
  intro b hb
  apply momentMap_injective hi
  rw [←exponentialWord_coordinates,←exponentialWord_coordinates,hb,he]

#print axioms exponential_expansion

end SpanningSpectralCoordinates
