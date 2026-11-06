module

public import SpanningTwoAdditionSelectionV1
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

namespace SpanningFixedCandidates

theorem prime_set (bound n:ℕ) :
    ∃S:Finset ℕ,S.card=n ∧ ∀p∈S,p.Prime ∧ bound<p := by
  classical
  induction n with
  | zero => exact ⟨∅,rfl,by simp⟩
  | succ n ih =>
    obtain ⟨S,hS,hpr⟩ := ih
    obtain ⟨p,hlarge,hprime⟩ := Nat.exists_infinite_primes (max bound (S.sup id)+1)
    have hnp : p∉S := by
      intro hp
      have hle : p≤S.sup id := Finset.le_sup (f:=id) hp
      have hb := le_max_right bound (S.sup id)
      omega
    refine ⟨insert p S,by simp [hnp,hS],?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl|hq
    · exact ⟨hprime,by have hb:=le_max_left bound (S.sup id); omega⟩
    · exact hpr q hq

theorem prime_coprime_of_large {c B:ℕ} (hc:c.Prime) (hB:0<B) (hlarge:B<c) :
    Nat.Coprime c B := hc.coprime_iff_not_dvd.mpr (fun hd =>
      (not_le.mpr hlarge) (Nat.le_of_dvd hB hd))

#print axioms prime_set

end SpanningFixedCandidates
