module

public import SpanningCriterionSufficiencyV1
public import SpanningCriterionArithmeticV1

@[expose] public section

namespace SpanningTheorem

open SpanningIntegerRows SpanningActualKernel SpanningTraceAlgebra

/-- The original rational spanning theorem, with no external mathematical
inputs. The rows use the strict window from spanning_proof.tex. -/
theorem spanning (N:ℕ) (hN:0<N) (h16:¬16∣N)
    (hsq:∀p:ℕ,p.Prime→p≠2→¬p^2∣N) :
    ∃Q:ℕ,∃hQ:0<Q,N∣Q ∧
      Submodule.span ℚ (Set.range (fun i j => (primitiveRows N hQ i j:ℚ)))=⊤ :=
  by
  obtain ⟨Q, hQ, hNQ, _, hz⟩ := SpanningCriterion.zero_kernel hN ∅ (by simp)
    (SpanningCriterion.condition_of_admissible ⟨hN, h16, hsq⟩ ∅)
  refine ⟨Q, hQ, hNQ, (primitive_span_top_iff hQ).mpr ?_⟩
  intro f hf
  exact hz f ⟨(complete_iff_primitive hN hQ f).mp hf, by simp⟩

/-- An expanded coordinate formulation, exposing every row equation and
the two strict endpoints rather than hiding them in a kernel predicate. -/
theorem zero_kernel (N:ℕ) (hN:0<N) (h16:¬16∣N)
    (hsq:∀p:ℕ,p.Prime→p≠2→¬p^2∣N) :
    ∃Q:ℕ,0<Q ∧ N∣Q ∧ ∀f:ℤ→ℚ,
      (∀j:ℤ,f (j+(Q:ℤ))=f j) →
      (∀q:ℕ,q∣Q → ∀u:ℤ,
        -(Q:ℝ)/Real.sqrt (Nat.lcm N (q^2)) < (u:ℝ) →
        (u:ℝ)<(Q:ℝ)/Real.sqrt (Nat.lcm N (q^2))-1 →
        (∑a∈(Finset.range q).filter (fun a => Nat.Coprime a q),f (u+(a:ℤ)*(Q/q)))=0) →
      f=0 := by
  obtain ⟨Q,hQ,hNQ,hspan⟩ := spanning N hN h16 hsq
  refine ⟨Q,hQ,hNQ,?_⟩
  intro f hcyc hrows
  apply (primitive_span_top_iff hQ).mp hspan f
  refine ⟨hcyc,?_⟩
  intro q hq u hu
  apply hrows q hq u
  · simpa only [SpanningActualKernel.radius,SpanningLevelArithmetic.level,neg_div] using hu.1
  · have he := hu.2
    change (u:ℝ)+1 < (Q:ℝ)/Real.sqrt (Nat.lcm N (q^2)) at he
    linarith

#print axioms spanning
#print axioms zero_kernel

end SpanningTheorem
