module

public import CobhamTheoremV1
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

@[expose] public section

namespace SpanningPeriodicWords

open AutomaticSequences BKKCommonFactor IndependentBases
open scoped BigOperators

/-- A digit recursion is a finite-state presentation, with leading zeros
already covered by the recursion at n=r=0. -/
theorem automatic_of_digits {A : Type} [Fintype A] {q : ℕ} (hq : 2≤q)
    (step : A → Fin q → A) (u : ℕ → A)
    (hu : ∀ n (r : Fin q), u (q*n+r.val)=step (u n) r) : Automatic q u := by
  apply automatic_of_prefix_equation (s:=0) hq (fun r a => step a r) u
  intro t _
  simpa only [Nat.sub_zero, Nat.div_add_mod] using
    hu (t/q) ⟨t%q, Nat.mod_lt t (by omega)⟩

/-- The common eventual period of all projected words in the revised
spanning proof. This uses ordinary Cobham directly, not common factors. -/
theorem uniform_period {I A : Type} [Fintype I] [Fintype A]
    {q₁ q₂ : ℕ} (h₁ : 2≤q₁) (h₂ : 2≤q₂) (hi : Independent q₁ q₂)
    (u : I → ℕ → A) (step₁ : A → Fin q₁ → A) (step₂ : A → Fin q₂ → A)
    (hu₁ : ∀ α n (r : Fin q₁), u α (q₁*n+r.val)=step₁ (u α n) r)
    (hu₂ : ∀ α n (r : Fin q₂), u α (q₂*n+r.val)=step₂ (u α n) r) :
    ∃ P i₀ : ℕ, 0<P ∧ ∀ α i, i₀ ≤ i → u α (i+P)=u α i := by
  classical
  have hp : ∀ α, ∃ P, 0<P ∧ EventuallyPeriodic P (u α) := fun α =>
    CobhamTheorem.cobham h₁ h₂ hi
      (automatic_of_digits h₁ step₁ (u α) (hu₁ α))
      (automatic_of_digits h₂ step₂ (u α) (hu₂ α))
  choose p hp hperiod using hp
  obtain ⟨P,hP,hdiv⟩ := finite_periods_common_multiple (Finset.univ.image p)
  have hall : ∀ α, EventuallyPeriodic P (u α) := fun α =>
    eventuallyPeriodic_of_dvd (hperiod α)
      (hdiv (p α) (Finset.mem_image.mpr ⟨α,Finset.mem_univ _,rfl⟩) (hp α))
  choose K hK using hall
  refine ⟨P,∑ α, K α,hP,?_⟩
  intro α i hi₀
  have hKi : K α ≤ ∑ β, K β := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ α)
  exact (hK α i (hKi.trans hi₀)).symm

/-- Once a stationary block equals the projected word on [0,n), its
P-step differences vanish on the trimmed interval [i₀,n-P). -/
theorem periodic_zone {I A : Type*} (u : I → ℕ → A) (w : ℕ → A)
    (α : I) (offset n P i₀ i : ℕ)
    (hperiod : ∀ j, i₀≤j → u α (j+P)=u α j)
    (hblock : ∀ j, j<n → w (offset+j)=u α j)
    (hi : i₀ ≤ i) (hend : i+P<n) : w (offset+i+P)=w (offset+i) := by
  rw [Nat.add_assoc, hblock (i+P) hend, hblock i (by omega), hperiod i hi]

#print axioms uniform_period
#print axioms periodic_zone

end SpanningPeriodicWords
