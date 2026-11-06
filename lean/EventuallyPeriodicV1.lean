module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Nat
public import Lean.Elab.Tactic.Omega

@[expose] public section

/- Shared elementary periodicity lemmas. The namespace is retained for
compatibility with the archived automatic-sequence proofs. -/
namespace BKKCommonFactor

variable {A : Type*}

def EventuallyPeriodic (P : ℕ) (z : ℕ → A) : Prop :=
  ∃ K, ∀ j, K ≤ j → z j = z (j+P)

theorem eventuallyPeriodic_mul {p : ℕ} {z : ℕ → A}
    (h : EventuallyPeriodic p z) (m : ℕ) : EventuallyPeriodic (m*p) z := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, ?_⟩
  induction m with
  | zero => intro j _; simp
  | succ m ih =>
    intro j hj
    calc
      z j = z (j+m*p) := ih j hj
      _ = z ((j+m*p)+p) := hK _ (by omega)
      _ = z (j+(m+1)*p) := by rw [Nat.add_mul]; simp [Nat.add_assoc]

theorem eventuallyPeriodic_of_dvd {p P : ℕ} {z : ℕ → A}
    (h : EventuallyPeriodic p z) (hp : p ∣ P) : EventuallyPeriodic P z := by
  obtain ⟨m, rfl⟩ := hp
  simpa only [Nat.mul_comm] using eventuallyPeriodic_mul h m

theorem finite_periods_common_multiple (s : Finset ℕ) :
    ∃ P, 0 < P ∧ ∀ p ∈ s, 0 < p → p ∣ P := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by omega, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨P, hP, hp⟩ := ih
    by_cases ha : a = 0
    · refine ⟨P, hP, ?_⟩
      intro p hpm hpos
      rcases Finset.mem_insert.mp hpm with hpa | hps
      · omega
      · exact hp p hps hpos
    · refine ⟨a*P, Nat.mul_pos (by omega) hP, ?_⟩
      intro p hpm hpos
      rcases Finset.mem_insert.mp hpm with hpa | hps
      · subst p; exact dvd_mul_right a P
      · exact dvd_mul_of_dvd_right (hp p hps hpos) a

/-- Pointwise eventual periodicity is made uniform only when a finite
list of possible periods has been established. -/
theorem common_period_of_finite_periods (X : Set (ℕ → A)) (s : Finset ℕ)
    (hs : ∀ z ∈ X, ∃ p ∈ s, 0 < p ∧ EventuallyPeriodic p z) :
    ∃ P, 0 < P ∧ ∀ z ∈ X, EventuallyPeriodic P z := by
  obtain ⟨P, hP, hp⟩ := finite_periods_common_multiple s
  refine ⟨P, hP, ?_⟩
  intro z hz
  obtain ⟨p, hps, hpos, hperiod⟩ := hs z hz
  exact eventuallyPeriodic_of_dvd hperiod (hp p hps hpos)


end BKKCommonFactor
