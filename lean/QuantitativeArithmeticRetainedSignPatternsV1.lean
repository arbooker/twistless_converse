module

public import QuantitativeArithmeticRetainedHolomorphicSpaceV1
public import FinitenessSignPatternsV1
public import FinitenessFiniteUnionV1
public import QuantitativeArithmeticRamifiedOriginalBridgeV1

set_option autoImplicit false

@[expose] public section

namespace QuantitativeArithmeticRetainedSignPatterns

open Complex FinitenessOriginalInput FinitenessOriginalDiskIndependence
  QuantitativeArithmeticRetainedHolomorphicSpace

abbrev Pattern (Q : ℕ) := Fin (Q + 1) → Fin 3

/-- The three allowed complete-trace multipliers at each retained prime. -/
noncomputable def multiplier (Q m : ℕ) (e : Pattern Q) (p : ℕ) : ℂ :=
  if h : p ≤ Q then
    if e ⟨p, Nat.lt_succ_of_le h⟩ = 0 then 0
    else if e ⟨p, Nat.lt_succ_of_le h⟩ = 1 then (p : ℂ) ^ m
    else -(p : ℂ) ^ m
  else 0

theorem norm_bound (Q m : ℕ) (e : Pattern Q) (p : ℕ) :
    ‖multiplier Q m e p‖ ≤ (p : ℝ) ^ m := by
  unfold multiplier
  split_ifs <;> simp

noncomputable def encode (Q m : ℕ) (b : ℕ → ℂ) : Pattern Q :=
  fun p => if b p.val = 0 then 0 else if b p.val = (p.val : ℂ) ^ m then 1 else 2

theorem encode_spec {Q m p : ℕ} (b : ℕ → ℂ) (hp : p ≤ Q)
    (hb : b p = 0 ∨ b p = (p : ℂ) ^ m ∨ b p = -(p : ℂ) ^ m) :
    multiplier Q m (encode Q m b) p = b p := by
  classical
  by_cases hzero : b p = 0
  · simp [multiplier, hp, encode, hzero]
  by_cases hplus : b p = (p : ℂ) ^ m
  · have he : encode Q m b ⟨p, Nat.lt_succ_of_le hp⟩ = 1 := by
      dsimp only [encode]
      rw [ite_eq_right hzero, ite_eq_left hplus]
    rw [multiplier, dite_eq_left hp, he]
    simpa using hplus.symm
  have hminus : b p = -(p : ℂ) ^ m := hb.resolve_left hzero |>.resolve_left hplus
  simpa [multiplier, hp, encode, hzero, hplus] using hminus.symm

/-- Restriction on any retained finite set; its primes may divide N. -/
theorem restriction_on {Q m : ℕ} (hQ : 0 < Q) (P : Finset ℕ)
    (hdiv : ∀ p ∈ P, p ∣ Q) (b : ℕ → ℂ)
    (hb : ∀ p ∈ P, b p = 0 ∨ b p = (p : ℂ) ^ m ∨ b p = -(p : ℂ) ^ m) :
    ∃ e : Pattern Q, ∀ p ∈ P, multiplier Q m e p = b p := by
  refine ⟨encode Q m b, ?_⟩
  intro p hp
  exact encode_spec b (Nat.le_of_dvd hQ (hdiv p hp)) (hb p hp)

theorem restriction {Q m : ℕ} (hQ : 0 < Q) (b : ℕ → ℂ)
    (hb : ∀ p, p ∣ Q → b p = 0 ∨ b p = (p : ℂ) ^ m ∨ b p = -(p : ℂ) ^ m) :
    ∃ e : Pattern Q, ∀ p, p ∣ Q → multiplier Q m e p = b p := by
  refine ⟨encode Q m b, ?_⟩
  intro p hp
  exact encode_spec b (Nat.le_of_dvd hQ hp) (hb p hp)

theorem card (Q : ℕ) : Fintype.card (Pattern Q) = 3 ^ (Q + 1) := by
  simp [Pattern]

abbrev CombinedPattern (Q : ℕ) := FinitenessSignPatterns.Pattern Q × Pattern Q

theorem combined_card (Q : ℕ) : Fintype.card (CombinedPattern Q) = 6 ^ (Q + 1) := by
  simp [CombinedPattern, FinitenessSignPatterns.Pattern, Pattern, ← mul_pow]

/-- Finite-pattern cover of the literal original solution set. The only
additional premise is its explicit complete-twist law with the three
ramified multipliers; no finiteness or growth uniformity is assumed. -/
theorem cover_of_complete {N Q m : ℕ} (hN : 0 < N) (hQ : 0 < Q) (hNQ : N ∣ Q)
    (f : S N (2 * m))
    (hcomplete : ∃ b : ℕ → ℂ,
      (∀ p ∈ N.primeFactors, b p = 0 ∨ b p = (p : ℂ) ^ m ∨ b p = -(p : ℂ) ^ m) ∧
      CompleteLaws N.primeFactors b
        (FinitenessHolomorphicSpace.lift (representative N (2 * m) f).val)) :
    ∃ e : CombinedPattern Q, representative N (2 * m) f ∈
      space N Q N.primeFactors (FinitenessSignPatterns.multiplier Q m e.1)
        (multiplier Q m e.2) m := by
  obtain ⟨a, ha⟩ := FinitenessSignPatterns.cover hN hQ f
  obtain ⟨b, hb, hblaw⟩ := hcomplete
  obtain ⟨e, he⟩ := restriction_on hQ N.primeFactors
    (fun _ hp => (Nat.dvd_of_mem_primeFactors hp).trans hNQ) b hb
  refine ⟨(a, e), ha, ?_⟩
  intro p hp z hz
  rw [he p hp]
  exact hblaw p hp z hz

/-- The finite union and independence argument counts original solutions
from the actual mixed sector dimensions, before the complete-law bridge
is discharged. -/
theorem count_of_complete {N Q m d : ℕ} (hN : 0 < N) (hQ : 0 < Q) (hNQ : N ∣ Q)
    (hcomplete : ∀ f : S N (2 * m), ∃ b : ℕ → ℂ,
      (∀ p ∈ N.primeFactors, b p = 0 ∨ b p = (p : ℂ) ^ m ∨ b p = -(p : ℂ) ^ m) ∧
      CompleteLaws N.primeFactors b
        (FinitenessHolomorphicSpace.lift (representative N (2 * m) f).val))
    (hdim : ∀ e : CombinedPattern Q,
      FiniteDimensional ℂ (space N Q N.primeFactors
        (FinitenessSignPatterns.multiplier Q m e.1) (multiplier Q m e.2) m) ∧
      Module.finrank ℂ (space N Q N.primeFactors
        (FinitenessSignPatterns.multiplier Q m e.1) (multiplier Q m e.2) m) ≤ d) :
    (S N (2 * m)).Finite ∧ (S N (2 * m)).ncard ≤ 6 ^ (Q + 1) * d := by
  classical
  let W : CombinedPattern Q → Submodule ℂ FinitenessDiskJet.space :=
    fun e => space N Q N.primeFactors (FinitenessSignPatterns.multiplier Q m e.1)
      (multiplier Q m e.2) m
  let inst : ∀ e, FiniteDimensional ℂ (W e) := fun e => (hdim e).1
  obtain ⟨hfinite, hcard⟩ := FinitenessFiniteUnion.bound W
    (representative N (2 * m)) (independent N (2 * m))
    (fun f => cover_of_complete hN hQ hNQ f (hcomplete f)) d (fun e => (hdim e).2)
  refine ⟨Set.finite_coe_iff.mp hfinite, ?_⟩
  simpa only [Nat.card_coe_set_eq, combined_card] using hcard

/-- Every literal positive-even-weight solution belongs to one of the
finitely many mixed spaces. All complete-twist laws are now derived
from its original Euler factors. -/
theorem cover {N Q m : ℕ} (hN : 0 < N) (hQ : 0 < Q) (hNQ : N ∣ Q)
    (hm : 0 < m) (f : S N (2 * m)) :
    ∃ e : CombinedPattern Q, representative N (2 * m) f ∈
      space N Q N.primeFactors (FinitenessSignPatterns.multiplier Q m e.1)
        (multiplier Q m e.2) m :=
  cover_of_complete hN hQ hNQ f
    (QuantitativeArithmeticRamifiedOriginalBridge.original_sign_cover hm f)

/-- The original solution count follows from the mixed space dimensions,
with no additional full-trace or finite-cover premise. -/
theorem count {N Q m d : ℕ} (hN : 0 < N) (hQ : 0 < Q) (hNQ : N ∣ Q)
    (hm : 0 < m)
    (hdim : ∀ e : CombinedPattern Q,
      FiniteDimensional ℂ (space N Q N.primeFactors
        (FinitenessSignPatterns.multiplier Q m e.1) (multiplier Q m e.2) m) ∧
      Module.finrank ℂ (space N Q N.primeFactors
        (FinitenessSignPatterns.multiplier Q m e.1) (multiplier Q m e.2) m) ≤ d) :
    (S N (2 * m)).Finite ∧ (S N (2 * m)).ncard ≤ 6 ^ (Q + 1) * d :=
  count_of_complete hN hQ hNQ
    (QuantitativeArithmeticRamifiedOriginalBridge.original_sign_cover hm) hdim

#print axioms norm_bound
#print axioms restriction_on
#print axioms restriction
#print axioms cover_of_complete
#print axioms count_of_complete
#print axioms cover
#print axioms count

end QuantitativeArithmeticRetainedSignPatterns
