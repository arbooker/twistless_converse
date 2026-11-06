module

public import FinitenessSignPatternsV1
public import FinitenessFiniteUnionV1

set_option autoImplicit false

public section

namespace FinitenessOriginalTheorem

open FinitenessOriginalInput FinitenessHolomorphicSpace
  FinitenessOriginalDiskIndependence FinitenessSignPatterns

/-- Finiteness and a uniform linear cardinality bound for the ORIGINAL
solution predicate, at every admissible level and positive even weight.
There are no extra spanning, analytic, Euler inequivalence or modularity inputs. -/
theorem admissible_level (N : ℕ) (hN : 0<N) (h16 : ¬16 ∣ N)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p^2 ∣ N) :
    ∃ C : ℕ, 0<C ∧ ∀ m : ℕ, 0<m →
      (S N (2*m)).Finite ∧ (S N (2*m)).ncard ≤ C*m := by
  classical
  obtain ⟨Q,C,hQ,_hNQ,hC,hbound⟩ :=
    FinitenessHolomorphicSpace.admissible_level N hN h16 hsq
  refine ⟨2^(Q+1)*C,Nat.mul_pos (pow_pos (by decide) _) hC,?_⟩
  intro m hm
  let W : Pattern Q → Submodule ℂ FinitenessDiskJet.space :=
    fun e => space N Q (multiplier Q m e) m
  have hd (e : Pattern Q) : FiniteDimensional ℂ (W e) ∧
      Module.finrank ℂ (W e) ≤ C*m :=
    hbound (multiplier Q m e) m hm (fun q _ => unit_norm Q m e q)
  let inst : ∀ e, FiniteDimensional ℂ (W e) := fun e => (hd e).1
  obtain ⟨hfinite,hcard⟩ := FinitenessFiniteUnion.bound W
    (representative N (2*m)) (independent N (2*m)) (cover hN hQ) (C*m)
    (fun e => (hd e).2)
  refine ⟨Set.finite_coe_iff.mp hfinite,?_⟩
  simpa only [Nat.card_coe_set_eq, FinitenessSignPatterns.card, Nat.mul_assoc] using hcard

/-- Equivalent positive-even-weight formulation, with the O_N(k) bound
stated directly in the original weight variable. -/
theorem even_weight (N : ℕ) (hN : 0<N) (h16 : ¬16 ∣ N)
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p^2 ∣ N) :
    ∃ C : ℕ, 0<C ∧ ∀ k : ℕ, 0<k → Even k →
      (S N k).Finite ∧ (S N k).ncard ≤ C*k := by
  obtain ⟨C,hC,hbound⟩ := admissible_level N hN h16 hsq
  refine ⟨C,hC,?_⟩
  intro k hk heven
  obtain ⟨m,rfl⟩ := heven
  have hm : 0<m := by omega
  obtain ⟨hf,hb⟩ := hbound m hm
  rw [two_mul] at hf hb
  exact ⟨hf,hb.trans (Nat.mul_le_mul_left C (by omega))⟩

#print axioms admissible_level
#print axioms even_weight

end FinitenessOriginalTheorem
