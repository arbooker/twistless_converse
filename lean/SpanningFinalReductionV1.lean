module

public import SpanningInitialTraceSetV1
public import SpanningFiniteRemovalV1
public import SpanningSmallLevelsV1

@[expose] public section

namespace SpanningFinalReduction

open SpanningActualKernel SpanningIntegerRows SpanningFiniteDimensions

/-- This is the remaining bounded-axis proposition, not an axiom and not
claimed proved here. The final theorem below retains it explicitly. -/
def BoundedAxis (N:ℕ) : Prop :=
  ∀(B p:ℕ)(L:Finset ℕ),0<B → p.Prime → Nat.Coprime N p →
    (∀ell∈L,ell∣B) →
    (∀a:ℕ,dimension (K:=ℚ) N (L:Set ℕ) (B*p^a)≤dimension (K:=ℚ) N (L:Set ℕ) B) →
    ∃Q:ℕ,0<Q ∧ B∣Q ∧ ∀f:ℤ → ℚ,Augmented N (L:Set ℕ) Q f → f=0

theorem spanning_of_bounded_axis {N:ℕ} (hN:0<N) (haxis:BoundedAxis N) :
    ∃Q:ℕ,∃hQ:0<Q,N∣Q ∧
      Submodule.span ℚ (Set.range (fun i j => (primitiveRows N hQ i j:ℚ)))=⊤ := by
  obtain ⟨S,D,hD,hND,hS,hzero⟩ := SpanningInitialTraceSet.exists_initial_trace_set hN
  obtain ⟨Q,hQ,hDQ,hfinal⟩ := SpanningFiniteRemoval.remove_finite_traces hN haxis S hD
    (fun p hp => ⟨(hS p hp).1,(hS p hp).2.1⟩) (fun p hp => (hS p hp).2.2) hzero
  exact ⟨Q,hQ,hND.trans hDQ,(primitive_span_top_iff hQ).mpr hfinal⟩

theorem spanning_small_levels {N:ℕ} (hN:0<N) (hsmall:N≤4) :
    Submodule.span ℚ (Set.range (fun i j => (primitiveRows N (by omega : 0<4) i j:ℚ)))=⊤ := by
  apply (primitive_span_top_iff (by omega : 0<4)).mpr
  exact SpanningSmallLevels.kernel_zero_small hN hsmall

#print axioms spanning_of_bounded_axis
#print axioms spanning_small_levels

end SpanningFinalReduction
