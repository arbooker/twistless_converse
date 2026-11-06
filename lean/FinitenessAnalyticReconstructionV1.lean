module

public import FinitenessReconstructionV1
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace FinitenessAnalyticReconstruction

open FinitenessCertificate SpanningIntegerRows SpanningTraceAlgebra

noncomputable def twist (F : ℂ → ℂ) (q : ℕ) (z : ℂ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F (z + (a : ℂ) / q)

noncomputable def sample (F : ℂ → ℂ) (Q : ℕ) (j : ℤ) (z : ℂ) : ℤ → ℂ :=
  fun t => F (z + ((t : ℂ) - j) / Q)

theorem sample_cyclic (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z)
    {Q : ℕ} (hQ : 0 < Q) (j : ℤ) (z : ℂ) : Cyclic Q (sample F Q j z) := by
  intro t
  unfold sample
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have he : z + (((t + (Q : ℤ) : ℤ) : ℂ) - j) / Q =
      (z + ((t : ℂ) - j) / Q) + 1 := by
    push_cast
    field_simp
    ring
  rw [he, hp]

theorem sample_row (F : ℂ → ℂ) {Q q : ℕ} (hQ : 0 < Q) (hq : q ∣ Q)
    (j u : ℤ) (z : ℂ) :
    primitive q (Q/q) (sample F Q j z) u =
      twist F q (z + ((u : ℂ)-j)/Q) := by
  have hqp : 0 < q := Nat.pos_of_dvd_of_pos hq hQ
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hqp.ne'
  have he : (q : ℂ) * ((Q/q : ℕ) : ℂ) = (Q : ℂ) := by
    exact_mod_cast Nat.mul_div_cancel' hq
  unfold primitive sample twist
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  push_cast
  simp only [← Int.natCast_ediv, Int.cast_natCast]
  field_simp
  linear_combination (a : ℂ) * he

/-- The actual periodic sampling identity, before applying any FE. -/
theorem reconstruct_twists {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z)
    (j : Fin Q) (z : ℂ) :
    F z = ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) *
      twist F i.val.1 (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q) := by
  have h := FinitenessReconstruction.reconstruct_periodic A j
    (sample F Q j z) (sample_cyclic F hp hQ j z)
  have he (i : RowIndex N Q) := sample_row F hQ i.property.1 (j : ℤ) i.val.2 z
  simpa only [he, sample, Int.cast_natCast, sub_self, zero_div, add_zero] using h.symm

/-- Literal holomorphic transformation laws turn the certificate into
positive-height reconstruction. Holomorphy itself is not needed here. -/
theorem reconstruct_FE {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z)
    (k : ℕ) (χ : ℕ → ℂ)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
      twist F q z = χ q / (((Real.sqrt (Nat.lcm N (q^2)) : ℝ) : ℂ) * z)^k *
        twist F q (-1 / ((Nat.lcm N (q^2) : ℕ) * z)))
    (j : Fin Q) (z : ℂ) (hz : 0 < z.im) :
    F z = ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) *
      (χ i.val.1 /
        (((Real.sqrt (Nat.lcm N (i.val.1^2)) : ℝ) : ℂ) *
          (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q))^k *
        twist F i.val.1 (-1 / ((Nat.lcm N (i.val.1^2) : ℕ) *
          (z + ((i.val.2 : ℂ) - (j : ℕ)) / Q)))) := by
  rw [reconstruct_twists A F hp j z]
  apply Finset.sum_congr rfl
  intro i _
  rw [hFE i.val.1 i.property.1]
  simpa using hz

#print axioms reconstruct_twists
#print axioms reconstruct_FE

end FinitenessAnalyticReconstruction
