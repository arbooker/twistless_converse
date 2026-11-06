module

public import SpanningTowerTracesV1

@[expose] public section

namespace SpanningCoherentLifts

open SpanningTraceAlgebra SpanningActualKernel SpanningLinearKernels
open SpanningFiniteDimensions SpanningTowerTraces
variable {K : Type*} [Field K]

/-- An actual inverse to cumulative trace, retaining its coordinate identity. -/
structure TraceLift (N : ℕ) (L : Set ℕ) (Q p : ℕ) where
  equiv : augmentedSubmodule (K:=K) N L Q ≃ₗ[K] augmentedSubmodule (K:=K) N L (p*Q)
  trace_eq : ∀v,trace p Q (equiv v).val=v.val

noncomputable def TraceLift.ofStationary {N B p m : ℕ} {L : Set ℕ}
    (hp : 0<p) (hm : 0<m) (hB : 0<B) (hNp : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣B)
    (hi : UniformTraceInjective (K:=K) N L B p)
    (heq : dimension (K:=K) N L (p*(m*B))=dimension (K:=K) N L (m*B)) :
    TraceLift (K:=K) N L (m*B) p where
  equiv := (cumulativeTraceIso hp hm hB hNp hdiv hi heq).symm
  trace_eq v := by
    have hh := congrArg Subtype.val ((cumulativeTraceIso hp hm hB hNp hdiv hi heq).apply_symm_apply v)
    exact hh

theorem TraceLift.unique {N Q p : ℕ} {L : Set ℕ}
    (e : TraceLift (K:=K) N L Q p) (v : augmentedSubmodule (K:=K) N L Q)
    {w : ℤ → K} (hw : Augmented N L (p*Q) w) (ht : trace p Q w=v.val) :
    w=(e.equiv v).val := by
  obtain ⟨u,hu⟩ := e.equiv.surjective ⟨w,hw⟩
  have huval : (e.equiv u).val=w := congrArg Subtype.val hu
  have huv : u=v := by
    apply Subtype.ext
    rw [←e.trace_eq u,huval,ht]
  subst u
  exact huval.symm

theorem TraceLift.coherent {N Q p m : ℕ} {L : Set ℕ}
    (ep : TraceLift (K:=K) N L Q p) (emp : TraceLift (K:=K) N L Q (m*p))
    (hm : 0<m) (hNm : Nat.Coprime N m) (hdiv : ∀ell∈L,ell∣Q)
    (v : augmentedSubmodule (K:=K) N L Q) :
    trace m (p*Q) (emp.equiv v).val=(ep.equiv v).val := by
  apply ep.unique v
  · apply augmented_trace hm hNm (fun ell hell => dvd_mul_of_dvd_right (hdiv ell hell) p)
    have hv : Augmented N L ((m*p)*Q) (emp.equiv v).val := (emp.equiv v).property
    simpa [Nat.mul_assoc] using hv
  · rw [trace_comp]
    exact emp.trace_eq v

def TraceLift.cast {N Q p r : ℕ} {L : Set ℕ} (e : TraceLift (K:=K) N L Q p)
    (h : p=r) : TraceLift (K:=K) N L Q r := h ▸ e

def restrictOnAugmented {N q Q t : ℕ} {L : Set ℕ} (ht : t<q) (hdiv : ∀ell∈L,ell∣Q) :
    augmentedSubmodule (K:=K) N L (q*Q) →ₗ[K] augmentedSubmodule (K:=K) N L Q where
  toFun v := ⟨restrict q t v.val,augmented_restrict hdiv v.property ht⟩
  map_add' v w := Subtype.ext ((restrictLinear q t).map_add v.val w.val)
  map_smul' a v := Subtype.ext ((restrictLinear q t).map_smul a v.val)

def TraceLift.digitMap {N Q q t : ℕ} {L : Set ℕ}
    (eq : TraceLift (K:=K) N L Q q) (ht : t<q) (hdiv : ∀ell∈L,ell∣Q) :
    augmentedSubmodule (K:=K) N L Q →ₗ[K] augmentedSubmodule (K:=K) N L Q :=
  (restrictOnAugmented ht hdiv).comp eq.equiv.toLinearMap

theorem TraceLift.restriction_identification {N Q q m t : ℕ} {L : Set ℕ}
    (eq : TraceLift (K:=K) N L Q q) (em : TraceLift (K:=K) N L Q m)
    (emq : TraceLift (K:=K) N L Q (m*q))
    (hm : 0<m) (hNm : Nat.Coprime N m) (ht : t<q) (hdiv : ∀ell∈L,ell∣Q)
    (v : augmentedSubmodule (K:=K) N L Q) :
    restrict q t (emq.equiv v).val=(em.equiv (eq.digitMap ht hdiv v)).val := by
  apply em.unique
  · apply augmented_restrict (fun ell hell => dvd_mul_of_dvd_right (hdiv ell hell) m) _ ht
    have hv : Augmented N L ((m*q)*Q) (emq.equiv v).val := (emq.equiv v).property
    simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hv
  · rw [trace_restrict,eq.coherent emq hm hNm hdiv v]
    rfl

def evaluation {N Q : ℕ} {L : Set ℕ} (j : ℤ) : augmentedSubmodule (K:=K) N L Q →ₗ[K] K where
  toFun v := v.val j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def TraceLift.word {N Q p : ℕ} {L : Set ℕ} (e : TraceLift (K:=K) N L Q p) (j : ℤ) :
    Module.Dual K (augmentedSubmodule (K:=K) N L Q) :=
  (evaluation j).comp e.equiv.toLinearMap

theorem TraceLift.word_substitution {N Q q m t : ℕ} {L : Set ℕ}
    (eq : TraceLift (K:=K) N L Q q) (em : TraceLift (K:=K) N L Q m)
    (emq : TraceLift (K:=K) N L Q (m*q))
    (hm : 0<m) (hNm : Nat.Coprime N m) (ht : t<q) (hdiv : ∀ell∈L,ell∣Q) (j : ℤ) :
    emq.word (q*j+t)=(em.word j).comp (eq.digitMap ht hdiv) := by
  ext v
  exact congrFun (eq.restriction_identification em emq hm hNm ht hdiv v) j

def TraceLift.wordNat {N Q p : ℕ} {L : Set ℕ} (e : TraceLift (K:=K) N L Q p) :
    ℕ → Module.Dual K (augmentedSubmodule (K:=K) N L Q) := fun j => e.word j

#print axioms TraceLift.ofStationary
#print axioms TraceLift.restriction_identification
#print axioms TraceLift.word_substitution

end SpanningCoherentLifts
