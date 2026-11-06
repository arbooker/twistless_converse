module

public import FinitenessOriginalTwistedContinuationsV1
public import FinitenessOriginalDiskIndependenceV1
public import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

@[expose] public section

namespace FinitenessSignPatterns

open Complex FinitenessOriginalInput FinitenessHolomorphicSpace
  FinitenessOriginalDiskIndependence

abbrev Pattern (Q : ℕ) := Fin (Q+1) → Bool

noncomputable def multiplier (Q m : ℕ) (e : Pattern Q) (q : ℕ) : ℂ :=
  if h : q ≤ Q then
    if e ⟨q,Nat.lt_succ_of_le h⟩ then I^(2*m) else -I^(2*m)
  else I^(2*m)

theorem unit_norm (Q m : ℕ) (e : Pattern Q) (q : ℕ) :
    ‖multiplier Q m e q‖=1 := by
  unfold multiplier
  split_ifs <;> simp

theorem restriction {Q m : ℕ} (hQ : 0<Q) (χ : ℕ → ℂ)
    (hχ : ∀ q, χ q=I^(2*m) ∨ χ q= -I^(2*m)) :
    ∃ e : Pattern Q, ∀ q, q ∣ Q → multiplier Q m e q=χ q := by
  classical
  let e : Pattern Q := fun q => decide (χ q.val=I^(2*m))
  refine ⟨e,?_⟩
  intro q hq
  have hle : q≤Q := Nat.le_of_dvd hQ hq
  rcases hχ q with h | h
  · simp [multiplier, hle, e, h]
  · by_cases he : χ q=I^(2*m)
    · simp [multiplier, hle, e, he]
    · simpa [multiplier, hle, e, he] using h.symm

theorem cover {N Q m : ℕ} (hN : 0<N) (hQ : 0<Q) (f : S N (2*m)) :
    ∃ e : Pattern Q, representative N (2*m) f ∈ space N Q (multiplier Q m e) m := by
  obtain ⟨χ,hχ,_,hlaw⟩ := FinitenessOriginalTwistedContinuations.solution_laws hN hQ f.property
  obtain ⟨e,he⟩ := restriction hQ χ hχ
  obtain ⟨τ,_,hg⟩ := f.property.growth
  refine ⟨e,?_⟩
  apply FinitenessTwistedAnalyticBridge.disk_mem_space hN hQ f.property.zero hg
  intro q hq z hz
  rw [he q hq]
  exact hlaw q hq z hz

theorem card (Q : ℕ) : Fintype.card (Pattern Q)=2^(Q+1) := by
  simp [Pattern]

#print axioms cover

end FinitenessSignPatterns
