module
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4

@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

/-- Start a staged substitution without asking the elaborator to compare the
full computation with the same computation on `p.drop 0`. -/
theorem substituteCompute_start (inputs : ℕ → Poly) (p : Poly)
    (n : ℕ) (r next : Poly)
    (hnext : substituteCompute inputs (p.drop n) = next)
    (hstep : substituteTail inputs (p.take n) next = r) :
    substituteCompute inputs p = r := by
  simpa only [Nat.zero_add, List.drop_zero] using
    (substituteCompute_stage inputs p 0 n r next
      (by simpa only [Nat.zero_add] using hnext)
      (by simpa only [List.drop_zero] using hstep))

#print axioms substituteCompute_start
end QuantitativeArithmeticSevenLaurentRows
end
