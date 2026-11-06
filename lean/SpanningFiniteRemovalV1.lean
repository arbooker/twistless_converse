module

public import SpanningTraceRemovalV1
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

namespace SpanningFiniteRemoval

open SpanningActualKernel SpanningTraceRemoval SpanningFiniteDimensions

variable {K : Type*} [Field K]

/-- The final finite induction. Its sole research input is the bounded
axis proposition, stated explicitly; this file does not claim that the
input has already been formalized. -/
theorem remove_finite_traces {N : ℕ} (hN : 0<N)
    (step : ∀(B p:ℕ)(L:Finset ℕ),0<B → p.Prime → Nat.Coprime N p →
      (∀ell∈L,ell∣B) →
      (∀a:ℕ,dimension (K:=K) N (L:Set ℕ) (B*p^a)≤dimension (K:=K) N (L:Set ℕ) B) →
      ∃Q:ℕ,0<Q ∧ B∣Q ∧ ∀f:ℤ → K,Augmented N (L:Set ℕ) Q f → f=0)
    (S : Finset ℕ) {B : ℕ} (hB : 0<B)
    (hS : ∀p∈S,p.Prime ∧ Nat.Coprime N p) (hdiv : ∀p∈S,p∣B)
    (hz : ∀f:ℤ → K,Augmented N (S:Set ℕ) B f → f=0) :
    ∃Q:ℕ,0<Q ∧ B∣Q ∧ ∀f:ℤ → K,Kernel N Q f → f=0 := by
  classical
  induction S using Finset.induction_on generalizing B with
  | empty =>
    refine ⟨B,hB,dvd_refl B,?_⟩
    intro f hf
    apply hz f
    refine ⟨(complete_iff_primitive hN hB f).mp hf,?_⟩
    simp
  | @insert p S hpS ih =>
    have hp := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ell∈S,ell.Prime ∧ Nat.Coprime N ell :=
      fun ell hell => hS ell (Finset.mem_insert_of_mem hell)
    have hdiv' : ∀ell∈S,ell∣B := fun ell hell => hdiv ell (Finset.mem_insert_of_mem hell)
    have haxis := bounded_axis_after_insertion (K:=K) hB hp.1.pos hp.2 hdiv' (L:=(S:Set ℕ)) (by
      intro m hm f hf
      apply augmented_zero_at_multiples hm hdiv hz f
      simpa only [Finset.coe_insert] using hf)
    obtain ⟨Q,hQ,hBQ,hzero⟩ := step B p S hB hp.1 hp.2 hdiv' haxis
    obtain ⟨Q',hQ',hQQ',hfinal⟩ := ih hQ hS'
      (fun ell hell => (hdiv' ell hell).trans hBQ) hzero
    exact ⟨Q',hQ',hBQ.trans hQQ',hfinal⟩

#print axioms remove_finite_traces

end SpanningFiniteRemoval
