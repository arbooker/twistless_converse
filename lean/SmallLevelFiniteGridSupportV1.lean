module
public import SmallLevelFourPrimeRatesV1
public import Mathlib.LinearAlgebra.Matrix.ToLin
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelFiniteGridSupport
open Matrix

/-- Extend a vector on an explicitly enumerated support by zero. -/
def extend {n Q : ℕ} (u : Fin n→Fin Q) (v : Fin n→ℂ) (j : Fin Q) : ℂ :=
  ∑ i : Fin n,if u i=j then v i else 0

theorem extend_at {n Q : ℕ} (u : Fin n→Fin Q) (hu : Function.Injective u)
    (v : Fin n→ℂ) (i : Fin n) : extend u v (u i)=v i := by
  simp [extend,hu.eq_iff]

def extension {n Q : ℕ} (u : Fin n→Fin Q) : (Fin n→ℂ)→ₗ[ℂ](Fin Q→ℂ) where
  toFun := extend u
  map_add' v w := by
    funext j
    simp only [extend,Pi.add_apply,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp_all
  map_smul' c v := by
    funext j
    simp only [extend,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp_all

theorem extension_injective {n Q : ℕ} (u : Fin n→Fin Q) (hu : Function.Injective u) :
    Function.Injective (extension u) := by
  intro v w h
  funext i
  have hh:=congrFun h (u i)
  change extend u v (u i)=extend u w (u i) at hh
  simpa only [extend_at u hu] using hh

/-- A source system that detects every support coordinate remains
injective when written as a rectangular matrix on that finite support. -/
theorem matrix_kernel_of_support {n Q r : ℕ} (u : Fin n→Fin Q)
    (hu : Function.Injective u) (L : (Fin Q→ℂ)→ₗ[ℂ](Fin r→ℂ))
    (hL : ∀ v : Fin Q→ℂ, L v=0 → ∀ i : Fin n,v (u i)=0)
    (v : Fin n→ℂ) (hv : (L.comp (extension u)).toMatrix' *ᵥ v=0) : v=0 := by
  have hh : L (extension u v)=0 := by
    simpa only [LinearMap.toMatrix'_mulVec,LinearMap.comp_apply] using hv
  funext i
  have hi:=hL (extension u v) hh i
  change extend u v (u i)=0 at hi
  simpa only [extend_at u hu,Pi.zero_apply] using hi

#print axioms extend_at
#print axioms matrix_kernel_of_support
end SmallLevelFiniteGridSupport
