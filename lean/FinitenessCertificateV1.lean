module

public import SpanningTheoremV1
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

namespace FinitenessCertificate

open SpanningIntegerRows

/-- A finite rational certificate, one finitely supported row combination
for each coordinate. This is extracted from the actual spanning theorem. -/
structure Certificate (N Q : ℕ) (hQ : 0 < Q) where
  coeff : Fin Q → RowIndex N Q →₀ ℚ
  reconstruct : ∀ j : Fin Q,
    (coeff j).sum (fun i a => a • (fun t => (primitiveRows N hQ i t : ℚ))) =
      Pi.single j 1

theorem exists_certificate (N : ℕ) (hN : 0 < N) (h16 : ¬16 ∣ N)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p^2 ∣ N) :
    ∃ Q : ℕ, ∃ hQ : 0 < Q, N ∣ Q ∧ Nonempty (Certificate N Q hQ) := by
  classical
  obtain ⟨Q, hQ, hNQ, hspan⟩ := SpanningTheorem.spanning N hN h16 hsq
  have hj (j : Fin Q) : ∃ a : RowIndex N Q →₀ ℚ,
      a.sum (fun i b => b • (fun t => (primitiveRows N hQ i t : ℚ))) =
        Pi.single j 1 := by
    have hm : Pi.single j (1 : ℚ) ∈
        Submodule.span ℚ (Set.range (fun i t => (primitiveRows N hQ i t : ℚ))) := by
      rw [hspan]
      trivial
    obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
    exact ⟨a, ha⟩
  choose a ha using hj
  exact ⟨Q, hQ, hNQ, ⟨⟨a, ha⟩⟩⟩

theorem coordinate_identity {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) (j t : Fin Q) :
    ∑ i ∈ (A.coeff j).support, (A.coeff j i) * (primitiveRows N hQ i t : ℚ) =
      if t = j then 1 else 0 := by
  classical
  have h := congrFun (A.reconstruct j) t
  simpa [Finsupp.sum, Pi.single_apply, eq_comm] using h

#print axioms exists_certificate
#print axioms coordinate_identity

end FinitenessCertificate
