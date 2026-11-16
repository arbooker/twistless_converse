module

public import GridParametersV1

@[expose] public section

namespace GridBufferedDetection

open GridParameters GridSelectedWindows GridSpecialWindows GridPrimeParts GridAdmissibleGap
  GridSupportedDetection GridLabelDetection GridCarrier CompleteRowCosets
  SpanningActualKernel SpanningWindows SpanningTraceAlgebra

def BufferedZero {K : Type*} [AddCommMonoid K] (N Q : ℕ) (b : ℝ) (f : ℤ → K) : Prop :=
  ∀q:ℕ,0<q → q∣Q → ∀u:ℤ,Legal (radius N Q q) u →
    b≤radius N Q q-1-(u:ℝ) → trace q (Q/q) f u=0

theorem coset_zero_of_buffer {K : Type*} [AddCommMonoid K] {N Q q D : ℕ}
    {b : ℝ} {f : ℤ → K} (hq : 0<q) (hD : 0<D) (he : q*D=Q)
    (hcyc : Cyclic Q f) (hz : BufferedZero N Q b f) (u : ℤ)
    (hu : Legal (radius N Q q) u) (hb : b≤radius N Q q-1-(u:ℝ)) : cosetSum Q D u f=0 := by
  have hqd : Q/q=D := by rw [←he,Nat.mul_div_cancel_left _ hq]
  have ht := hz q hq ⟨D,he.symm⟩ u hu hb
  rw [hqd] at ht
  have hcos := trace_coset_sum hq hD u f (by simpa only [he] using hcyc)
  rw [he] at hcos
  exact hcos.symm.trans ht

#print axioms coset_zero_of_buffer

end GridBufferedDetection
