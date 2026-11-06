module

/- Finite dimension and stationary quadrants for the actual augmented kernels. -/
public import SpanningLinearKernelsV1
public import SpanningStationaryDimensionsV1
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace SpanningFiniteDimensions

open SpanningLinearKernels SpanningActualKernel SpanningSlicedAddition
open Module
variable {K : Type*} [Field K]

instance kernel_finite (N Q : ℕ) [NeZero Q] : FiniteDimensional K (kernelSubmodule (K:=K) N Q) :=
  FiniteDimensional.of_injective (kernelFiniteEquiv N Q (Nat.pos_of_ne_zero (NeZero.ne Q))).symm.toLinearMap
    (kernelFiniteEquiv N Q (Nat.pos_of_ne_zero (NeZero.ne Q))).symm.injective

instance augmented_finite (N : ℕ) (L : Set ℕ) (Q : ℕ) [NeZero Q] :
    FiniteDimensional K (augmentedSubmodule (K:=K) N L Q) :=
  FiniteDimensional.of_injective (augmentedFiniteEquiv N L Q (Nat.pos_of_ne_zero (NeZero.ne Q))).symm.toLinearMap
    (augmentedFiniteEquiv N L Q (Nat.pos_of_ne_zero (NeZero.ne Q))).symm.injective

noncomputable def dimension (N : ℕ) (L : Set ℕ) (Q : ℕ) : ℕ :=
  finrank K (augmentedSubmodule (K:=K) N L Q)

theorem dimension_trace_le {N q m B : ℕ} {L : Set ℕ}
    (hq : 0<q) (hm : 0<m) (hB : 0<B) (hc : Nat.Coprime N q) (hdiv : ∀ell∈L,ell∣B)
    (hinj : AdditionInjective q B {v : ℤ → K | Augmented N L B v}) :
    dimension (K:=K) N L (q*(m*B))≤dimension (K:=K) N L (m*B) := by
  let : NeZero (m*B) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hB)⟩
  exact LinearMap.finrank_le_finrank_of_injective (traceOnAugmented_injective hq hm hc hdiv hinj)

theorem stationary_dimensions {N c d B : ℕ} {L : Set ℕ}
    (hc : 0<c) (hd : 0<d) (hB : 0<B) (hcN : Nat.Coprime N c) (hdN : Nat.Coprime N d)
    (hdiv : ∀ell∈L,ell∣B)
    (hci : AdditionInjective c B {v : ℤ → K | Augmented N L B v})
    (hdi : AdditionInjective d B {v : ℤ → K | Augmented N L B v}) :
    ∃a b, ∀i j,
      dimension (K:=K) N L (B*c^(a+i)*d^(b+j))=dimension (K:=K) N L (B*c^a*d^b) := by
  apply SpanningStationaryDimensions.stable_quadrant
    (fun a b => dimension (K:=K) N L (B*c^a*d^b))
  · intro a b
    have hh := dimension_trace_le hc (Nat.mul_pos (Nat.pow_pos hc) (Nat.pow_pos hd)) hB hcN hdiv hci
      (m:=c^a*d^b)
    simpa [pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh
  · intro a b
    have hh := dimension_trace_le hd (Nat.mul_pos (Nat.pow_pos hc) (Nat.pow_pos hd)) hB hdN hdiv hdi
      (m:=c^a*d^b)
    simpa [pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh

theorem surjective_of_injective_equal_dimension {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hi : Function.Injective f) (heq : finrank K V=finrank K W) :
    Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  exact Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hi).trans heq)

noncomputable def traceIso {N q m B : ℕ} {L : Set ℕ}
    (hq : 0<q) (hm : 0<m) (hB : 0<B) (hc : Nat.Coprime N q) (hdiv : ∀ell∈L,ell∣B)
    (hinj : AdditionInjective q B {v : ℤ → K | Augmented N L B v})
    (heq : dimension (K:=K) N L (q*(m*B))=dimension (K:=K) N L (m*B)) :
    augmentedSubmodule (K:=K) N L (q*(m*B)) ≃ₗ[K] augmentedSubmodule (K:=K) N L (m*B) := by
  letI : NeZero (m*B) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hB)⟩
  letI : NeZero (q*(m*B)) := ⟨Nat.ne_of_gt (Nat.mul_pos hq (Nat.mul_pos hm hB))⟩
  let T := traceOnAugmented (K:=K) hq hc (fun ell hell => dvd_mul_of_dvd_right (hdiv ell hell) m)
  have hi : Function.Injective T := traceOnAugmented_injective hq hm hc hdiv hinj
  exact LinearEquiv.ofBijective T ⟨hi,surjective_of_injective_equal_dimension T hi heq⟩

instance augmented_finite_set (N : ℕ) (L : Set ℕ) (Q : ℕ) [NeZero Q] [Finite K] :
    Finite (augmentedSubmodule (K:=K) N L Q) :=
  Finite.of_injective (augmentedFiniteEquiv N L Q (Nat.pos_of_ne_zero (NeZero.ne Q))).symm
    (augmentedFiniteEquiv N L Q (Nat.pos_of_ne_zero (NeZero.ne Q))).symm.injective

instance alphabet_finite (N : ℕ) (L : Set ℕ) (Q : ℕ) [NeZero Q] [Finite K] :
    Finite (Module.Dual K (augmentedSubmodule (K:=K) N L Q)) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

#print axioms traceIso

#print axioms stationary_dimensions
#print axioms surjective_of_injective_equal_dimension

end SpanningFiniteDimensions
