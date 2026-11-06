module

public import SpanningCoherentLiftsV1
public import SpanningProjectedWordsV1

set_option autoImplicit false

@[expose] public section

namespace SpanningCoherentLifts

open SpanningTraceAlgebra SpanningActualKernel SpanningLinearKernels
open SpanningProjectedWords

variable {K : Type} [Field K]

/-- Multiplying moduli concatenates their digits. This is the identity
F^(mn)(nj+i) = F^(m)(j) F^(n)(i) from the revised spanning proof. -/
theorem TraceLift.digitMap_product {N Q m n i j : ℕ} {L : Set ℕ}
    (em : TraceLift (K:=K) N L Q m) (en : TraceLift (K:=K) N L Q n)
    (emn : TraceLift (K:=K) N L Q (m*n))
    (hm : 0 < m) (hmN : Nat.Coprime N m)
    (hi : i < n) (hj : j < m) (hdiv : ∀ ell ∈ L, ell ∣ Q)
    (hij : n*j+i < m*n) :
    emn.digitMap hij hdiv = (em.digitMap hj hdiv).comp (en.digitMap hi hdiv) := by
  ext v z
  have he := en.restriction_identification em emn hm hmN hi hdiv v
  have hr := congrArg (restrict m (j:ℤ)) he
  rw [restrict_comp] at hr
  rw [Nat.mul_comm n m] at hr
  have hc : (n:ℤ)*j+i=((n*j+i:ℕ):ℤ) := by push_cast; rfl
  rw [hc] at hr
  exact congrFun hr z

/-- Construct the digit action directly from the stationary trace inverses;
out-of-range indices have an arbitrary totalization, never used by the laws. -/
noncomputable def traceDigitAction {N Q q₁ q₂ : ℕ} {L : Set ℕ}
    (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (h₁N : Nat.Coprime N q₁) (h₂N : Nat.Coprime N q₂)
    (hdiv : ∀ ell ∈ L, ell ∣ Q)
    (E : ∀ n, Tower q₁ q₂ n → TraceLift (K:=K) N L Q n) :
    DigitAction (Module.Dual K (augmentedSubmodule (K:=K) N L Q)) q₁ q₂ := by
  classical
  let digit := fun n i (α : Module.Dual K (augmentedSubmodule (K:=K) N L Q)) =>
    if hn : Tower q₁ q₂ n then
      if hi : i < n then α.comp ((E n hn).digitMap hi hdiv) else α
    else α
  refine ⟨digit, ?_⟩
  intro m n hm hn j i hj hi α
  have hmpos : 0 < m := by
    obtain ⟨a,b,rfl⟩ := hm
    positivity
  have hmN : Nat.Coprime N m := by
    obtain ⟨a,b,rfl⟩ := hm
    exact (h₁N.pow_right a).mul_right (h₂N.pow_right b)
  have hij : n*j+i < m*n := by nlinarith
  simp only [digit, dite_eq_left hm, dite_eq_left hn, dite_eq_left (tower_mul hm hn),
    dite_eq_left hi, dite_eq_left hj, dite_eq_left hij]
  rw [TraceLift.digitMap_product (E m hm) (E n hn) (E (m*n) (tower_mul hm hn))
    hmpos hmN hi hj hdiv hij, LinearMap.comp_assoc]

#print axioms TraceLift.digitMap_product
#print axioms traceDigitAction

noncomputable def towerWord {N Q q₁ q₂ : ℕ} {L : Set ℕ}
    (E : ∀ n, Tower q₁ q₂ n → TraceLift (K:=K) N L Q n)
    (n : ℕ) (j : ℤ) : Module.Dual K (augmentedSubmodule (K:=K) N L Q) := by
  classical
  exact if hn : Tower q₁ q₂ n then (E n hn).word j else 0

theorem towerWord_product {N Q q₁ q₂ m n i : ℕ} {L : Set ℕ}
    (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (h₁N : Nat.Coprime N q₁) (h₂N : Nat.Coprime N q₂)
    (hdiv : ∀ ell ∈ L, ell ∣ Q)
    (E : ∀ n, Tower q₁ q₂ n → TraceLift (K:=K) N L Q n)
    (hm : Tower q₁ q₂ m) (hn : Tower q₁ q₂ n) (hi : i < n) (j : ℤ) :
    towerWord E (m*n) ((n:ℤ)*j+i) =
      (traceDigitAction h₁ h₂ h₁N h₂N hdiv E).digit n i (towerWord E m j) := by
  have hmN : Nat.Coprime N m := by
    obtain ⟨a,b,rfl⟩ := hm
    exact (h₁N.pow_right a).mul_right (h₂N.pow_right b)
  simpa only [towerWord, traceDigitAction, dite_eq_left (tower_mul hm hn),
    dite_eq_left hm, dite_eq_left hn, dite_eq_left hi] using
    (E n hn).word_substitution (E m hm) (E (m*n) (tower_mul hm hn))
      (tower_pos h₁ h₂ hm) hmN hi hdiv j

/-- The periodic-zone conclusion for the actual stationary trace words,
uniform in every outer block and every vector in the augmented kernel.
The finite alphabet, digit law, projection and Cobham step are all derived. -/
theorem periodic_trace_words [Finite K] {N Q q₁ q₂ : ℕ} {L : Set ℕ}
    (hQ : 0 < Q) (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : IndependentBases.Independent q₁ q₂)
    (h₁N : Nat.Coprime N q₁) (h₂N : Nat.Coprime N q₂)
    (hdiv : ∀ ell ∈ L, ell ∣ Q)
    (E : ∀ n, Tower q₁ q₂ n → TraceLift (K:=K) N L Q n) :
    ∃ s t P i₀ : ℕ, 0 < s ∧ 0 < t ∧ 0 < P ∧
      ∀ m n, Tower (q₁^s) (q₂^t) m → Tower (q₁^s) (q₂^t) n →
      ∀ (j : ℤ) (i : ℕ), i₀ ≤ i → i+P < n →
      towerWord E (m*((q₁^s*q₂^t)*n)) (((q₁^s*q₂^t)*n:ℕ)*j+(i+P:ℕ)) =
      towerWord E (m*((q₁^s*q₂^t)*n)) (((q₁^s*q₂^t)*n:ℕ)*j+i) := by
  classical
  let : NeZero Q := ⟨hQ.ne'⟩
  let : Fintype (Module.Dual K (augmentedSubmodule (K:=K) N L Q)) := Fintype.ofFinite _
  let F := traceDigitAction (by omega : 0 < q₁) (by omega : 0 < q₂) h₁N h₂N hdiv E
  obtain ⟨s,t,P,i₀,hs,ht,hP,hperiod⟩ := powered_block_periodic F h₁ h₂ hi
  refine ⟨s,t,P,i₀,hs,ht,hP,?_⟩
  intro m n hm hn j i hi₀ hin
  have hmn : Tower q₁ q₂ ((q₁^s*q₂^t)*n) :=
    tower_mul ⟨s,t,rfl⟩ (tower_powers hn)
  have hp : 0 < q₁^s*q₂^t := by positivity
  have hlarge : n ≤ (q₁^s*q₂^t)*n := by nlinarith
  rw [towerWord_product (by omega) (by omega) h₁N h₂N hdiv E (tower_powers hm) hmn
      (hin.trans_le hlarge),
    towerWord_product (by omega) (by omega) h₁N h₂N hdiv E (tower_powers hm) hmn
      (by omega)]
  exact hperiod n hn _ i hi₀ hin

#print axioms periodic_trace_words

end SpanningCoherentLifts
