module

/- Actual row kernels as submodules and their restriction/trace linear maps. -/
public import SpanningAdditionCoordinatesV1
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section

namespace SpanningLinearKernels

open SpanningTraceAlgebra SpanningActualKernel SpanningWindows SpanningCyclicCoordinates
variable {K : Type*} [Field K]

def primitiveLinear (q B : ℕ) (u : ℤ) : (ℤ → K) →ₗ[K] K where
  toFun v := primitive q B v u
  map_add' v w := by simp [primitive,Finset.sum_add_distrib]
  map_smul' a v := by simp [primitive,Finset.mul_sum]

def traceLinear (q B : ℕ) : (ℤ → K) →ₗ[K] (ℤ → K) where
  toFun := trace q B
  map_add' v w := by funext j; simp [trace,Finset.sum_add_distrib]
  map_smul' a v := by funext j; simp [trace,Finset.mul_sum]

def restrictLinear (m : ℕ) (t : ℤ) : (ℤ → K) →ₗ[K] (ℤ → K) where
  toFun := SpanningTraceAlgebra.restrict m t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extensionLinear {Q : ℕ} (hQ : 0<Q) : (Fin Q → K) →ₗ[K] (ℤ → K) where
  toFun := extend hQ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def kernelSubmodule (N Q : ℕ) : Submodule K (ℤ → K) where
  carrier := {v | Kernel N Q v}
  zero_mem' := by
    constructor
    · intro j; rfl
    · intro q hq u hu; simp [primitive]
  add_mem' {v w} hv hw := by
    constructor
    · intro j; change v (j+Q)+w (j+Q)=v j+w j; rw [hv.1,hw.1]
    · intro q hq u hu
      change primitiveLinear q (Q/q) u (_+_)=0
      rw [map_add]
      change primitive q (Q/q) v u+primitive q (Q/q) w u=0
      rw [hv.2 q hq u hu,hw.2 q hq u hu,add_zero]
  smul_mem' a v hv := by
    constructor
    · intro j; change a • v (j+Q)=a • v j; rw [hv.1]
    · intro q hq u hu
      change primitiveLinear q (Q/q) u (a • _)=0
      rw [map_smul]
      change a • primitive q (Q/q) v u=0
      rw [hv.2 q hq u hu,smul_zero]

def completeSubmodule (N Q : ℕ) : Submodule K (ℤ → K) where
  carrier := {v | CompleteKernel (radius N) Q v}
  zero_mem' := by
    constructor
    · intro j; rfl
    · intro q hq u hu; simp [trace]
  add_mem' {v w} hv hw := by
    constructor
    · intro j; change v (j+Q)+w (j+Q)=v j+w j; rw [hv.1,hw.1]
    · intro q hq u hu
      change (traceLinear q (Q/q) (_+_)) u=0
      rw [map_add]; change trace q (Q/q) v u+trace q (Q/q) w u=0
      rw [hv.2 q hq u hu,hw.2 q hq u hu,add_zero]
  smul_mem' a v hv := by
    constructor
    · intro j; change a • v (j+Q)=a • v j; rw [hv.1]
    · intro q hq u hu
      change (traceLinear q (Q/q) (a • _)) u=0
      rw [map_smul]; change a • trace q (Q/q) v u=0
      rw [hv.2 q hq u hu,smul_zero]

def augmentedSubmodule (N : ℕ) (L : Set ℕ) (Q : ℕ) : Submodule K (ℤ → K) where
  carrier := {v | Augmented N L Q v}
  zero_mem' := by
    refine ⟨(completeSubmodule (K:=K) N Q).zero_mem,?_⟩
    intro ell hell; exact (traceLinear ell (Q/ell)).map_zero
  add_mem' {v w} hv hw := by
    refine ⟨(completeSubmodule (K:=K) N Q).add_mem hv.1 hw.1,?_⟩
    intro ell hell
    change traceLinear ell (Q/ell) (_+_)=0
    rw [map_add]
    change trace ell (Q/ell) v+trace ell (Q/ell) w=0
    rw [hv.2 ell hell,hw.2 ell hell,add_zero]
  smul_mem' a v hv := by
    refine ⟨(completeSubmodule (K:=K) N Q).smul_mem a hv.1,?_⟩
    intro ell hell
    change traceLinear ell (Q/ell) (a • _)=0
    rw [map_smul]
    change a • trace ell (Q/ell) v=0
    rw [hv.2 ell hell,smul_zero]

def traceOnKernel {N p Q : ℕ} (hN : 0<N) (hp : 0<p) (hQ : 0<Q)
    (hc : Nat.Coprime N p) : kernelSubmodule (K:=K) N (p*Q) →ₗ[K] kernelSubmodule (K:=K) N Q where
  toFun v := ⟨trace p Q v.val,kernel_trace hN hp hQ hc v.property⟩
  map_add' v w := Subtype.ext ((traceLinear p Q).map_add v.val w.val)
  map_smul' a v := Subtype.ext ((traceLinear p Q).map_smul a v.val)

def restrictOnKernel {N m Q t : ℕ} (ht : t<m) :
    kernelSubmodule (K:=K) N (m*Q) →ₗ[K] kernelSubmodule (K:=K) N Q where
  toFun v := ⟨SpanningTraceAlgebra.restrict m t v.val,kernel_restrict v.property ht⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteKernel (N Q : ℕ) (hQ : 0<Q) : Submodule K (Fin Q → K) :=
  (kernelSubmodule N Q).comap (extensionLinear hQ)

def kernelFiniteEquiv (N Q : ℕ) (hQ : 0<Q) :
    finiteKernel (K:=K) N Q hQ ≃ₗ[K] kernelSubmodule (K:=K) N Q where
  toFun v := ⟨extend hQ v.val,v.property⟩
  invFun v := ⟨coordinates v.val,by
    change Kernel N Q (extend hQ (coordinates v.val))
    rw [extend_coordinates hQ v.property.1]
    exact v.property⟩
  left_inv v := Subtype.ext (coordinates_extend hQ v.val)
  right_inv v := Subtype.ext (extend_coordinates hQ v.property.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteAugmented (N : ℕ) (L : Set ℕ) (Q : ℕ) (hQ : 0<Q) : Submodule K (Fin Q → K) :=
  (augmentedSubmodule N L Q).comap (extensionLinear hQ)

def augmentedFiniteEquiv (N : ℕ) (L : Set ℕ) (Q : ℕ) (hQ : 0<Q) :
    finiteAugmented (K:=K) N L Q hQ ≃ₗ[K] augmentedSubmodule (K:=K) N L Q where
  toFun v := ⟨extend hQ v.val,v.property⟩
  invFun v := ⟨coordinates v.val,by
    change Augmented N L Q (extend hQ (coordinates v.val))
    rw [extend_coordinates hQ v.property.1.1]
    exact v.property⟩
  left_inv v := Subtype.ext (coordinates_extend hQ v.val)
  right_inv v := Subtype.ext (extend_coordinates hQ v.property.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def traceOnAugmented {N p Q : ℕ} {L : Set ℕ} (hp : 0<p)
    (hc : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣Q) :
    augmentedSubmodule (K:=K) N L (p*Q) →ₗ[K] augmentedSubmodule (K:=K) N L Q where
  toFun v := ⟨trace p Q v.val,augmented_trace hp hc hdiv v.property⟩
  map_add' v w := Subtype.ext ((traceLinear p Q).map_add v.val w.val)
  map_smul' a v := Subtype.ext ((traceLinear p Q).map_smul a v.val)

theorem traceOnAugmented_injective {N q m B : ℕ} {L : Set ℕ}
    (hq : 0<q) (hm : 0<m) (hc : Nat.Coprime N q) (hdiv : ∀ell∈L,ell∣B)
    (hinj : SpanningSlicedAddition.AdditionInjective q B {v : ℤ → K | Augmented N L B v}) :
    Function.Injective (traceOnAugmented (K:=K) hq hc
      (fun ell hell => dvd_mul_of_dvd_right (hdiv ell hell) m)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply Subtype.ext
  apply SpanningSlicedAddition.augmented_zero_of_trace hq hm hdiv hinj v.property
  exact congrArg Subtype.val hv

#print axioms kernelFiniteEquiv
#print axioms augmentedFiniteEquiv
#print axioms traceOnAugmented_injective

#print axioms kernelSubmodule
#print axioms augmentedSubmodule
#print axioms traceOnKernel

end SpanningLinearKernels
