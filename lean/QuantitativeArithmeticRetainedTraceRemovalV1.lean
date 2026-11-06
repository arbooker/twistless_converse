module

public import SpanningFiniteRemovalV1
public import SpanningInitialTraceSetV1

set_option autoImplicit false

@[expose] public section

namespace QuantitativeArithmeticRetainedTraceRemoval

open SpanningActualKernel SpanningTraceRemoval SpanningFiniteDimensions

variable {K : Type*} [Field K]

/-- Extra complete-trace conditions can only shrink the augmented kernel. -/
theorem augmented_mono {N Q : ℕ} {L L' : Set ℕ} (h : L ⊆ L')
    {f : ℤ → K} (hf : Augmented N L' Q f) : Augmented N L Q f :=
  ⟨hf.1, fun ell hell => hf.2 ell (h hell)⟩

/-- Remove a finite auxiliary set while retaining every trace in `P`.
The bounded-axis input is required only for finite sets containing `P`.
No primality or coprimality hypothesis is imposed on the retained set. -/
theorem remove_auxiliary_traces {N : ℕ} (P : Finset ℕ)
    (step : ∀ (B p : ℕ) (L : Finset ℕ), P ⊆ L →
      0 < B → p.Prime → Nat.Coprime N p →
      (∀ ell ∈ L, ell ∣ B) →
      (∀ a : ℕ, dimension (K := K) N (L : Set ℕ) (B * p ^ a) ≤
        dimension (K := K) N (L : Set ℕ) B) →
      ∃ Q : ℕ, 0 < Q ∧ B ∣ Q ∧
        ∀ f : ℤ → K, Augmented N (L : Set ℕ) Q f → f = 0)
    (S : Finset ℕ) {B : ℕ} (hB : 0 < B)
    (hS : ∀ p ∈ S, p.Prime ∧ Nat.Coprime N p)
    (hdiv : ∀ ell ∈ P ∪ S, ell ∣ B)
    (hz : ∀ f : ℤ → K, Augmented N ((P ∪ S : Finset ℕ) : Set ℕ) B f → f = 0) :
    ∃ Q : ℕ, 0 < Q ∧ B ∣ Q ∧
      ∀ f : ℤ → K, Augmented N (P : Set ℕ) Q f → f = 0 := by
  classical
  induction S using Finset.induction_on generalizing B with
  | empty =>
    exact ⟨B, hB, dvd_refl B, by simpa using hz⟩
  | @insert p S hpS ih =>
    have hp := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ ell ∈ S, ell.Prime ∧ Nat.Coprime N ell :=
      fun ell hell => hS ell (Finset.mem_insert_of_mem hell)
    have hsub : P ∪ S ⊆ P ∪ insert p S := by
      intro ell hell
      rcases Finset.mem_union.mp hell with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)
    have hdiv' : ∀ ell ∈ P ∪ S, ell ∣ B := fun ell hell => hdiv ell (hsub hell)
    have he : ((P ∪ insert p S : Finset ℕ) : Set ℕ) =
        insert p ((P ∪ S : Finset ℕ) : Set ℕ) := by
      ext ell
      simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_insert, Set.mem_insert_iff]
      tauto
    have haxis := bounded_axis_after_insertion (K := K) hB hp.1.pos hp.2
      (L := ((P ∪ S : Finset ℕ) : Set ℕ)) hdiv' (by
        intro m hm f hf
        apply augmented_zero_at_multiples hm hdiv hz f
        rw [he]
        exact hf)
    obtain ⟨Q, hQ, hBQ, hzero⟩ := step B p (P ∪ S)
      Finset.subset_union_left hB hp.1 hp.2 hdiv' haxis
    obtain ⟨Q', hQ', hQQ', hfinal⟩ := ih hQ hS'
      (fun ell hell => (hdiv' ell hell).trans hBQ) hzero
    exact ⟨Q', hQ', hBQ.trans hQQ', hfinal⟩

/-- The existing initial trace set may be enlarged by arbitrary fixed
positive retained moduli; the base length includes all retained divisors. -/
theorem exists_initial_with_retained {N : ℕ} (hN : 0 < N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    ∃ (S : Finset ℕ) (B : ℕ), 0 < B ∧ N ∣ B ∧
      (∀ p ∈ S, p.Prime ∧ Nat.Coprime N p) ∧
      (∀ ell ∈ P ∪ S, ell ∣ B) ∧
      ∀ f : ℤ → ℚ, Augmented N ((P ∪ S : Finset ℕ) : Set ℕ) B f → f = 0 := by
  classical
  obtain ⟨S, D, hD, hND, hS, hz⟩ :=
    SpanningInitialTraceSet.exists_initial_trace_set hN
  let M := ∏ p ∈ P, p
  have hM : 0 < M := Finset.prod_pos hP
  refine ⟨S, M * D, Nat.mul_pos hM hD, hND.trans (dvd_mul_left D M),
    fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩, ?_, ?_⟩
  · intro ell hell
    rcases Finset.mem_union.mp hell with h | h
    · exact (Finset.dvd_prod_of_mem (fun p : ℕ => p) h).trans (dvd_mul_right M D)
    · exact ((hS ell h).2.2).trans (dvd_mul_left D M)
  · intro f hf
    apply augmented_zero_at_multiples hM (fun p hp => (hS p hp).2.2) hz f
    exact augmented_mono (by
      intro p hp
      exact Finset.mem_union_right P hp) hf

/-- A retained bounded-axis theorem supplies vanishing with just the
retained traces. This is a reduction, with its analytic/combinatorial
bounded-axis premise explicitly retained. -/
theorem retained_zero_of_bounded_axis {N : ℕ} (hN : 0 < N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (step : ∀ (B p : ℕ) (L : Finset ℕ), P ⊆ L →
      0 < B → p.Prime → Nat.Coprime N p →
      (∀ ell ∈ L, ell ∣ B) →
      (∀ a : ℕ, dimension (K := ℚ) N (L : Set ℕ) (B * p ^ a) ≤
        dimension (K := ℚ) N (L : Set ℕ) B) →
      ∃ Q : ℕ, 0 < Q ∧ B ∣ Q ∧
        ∀ f : ℤ → ℚ, Augmented N (L : Set ℕ) Q f → f = 0) :
    ∃ Q : ℕ, 0 < Q ∧ N ∣ Q ∧ (∀ p ∈ P, p ∣ Q) ∧
      ∀ f : ℤ → ℚ, Augmented N (P : Set ℕ) Q f → f = 0 := by
  obtain ⟨S, B, hB, hNB, hS, hdiv, hz⟩ := exists_initial_with_retained hN P hP
  obtain ⟨Q, hQ, hBQ, hzero⟩ := remove_auxiliary_traces P step S hB hS hdiv hz
  exact ⟨Q, hQ, hNB.trans hBQ,
    fun p hp => (hdiv p (Finset.mem_union_left S hp)).trans hBQ, hzero⟩

#print axioms remove_auxiliary_traces
#print axioms exists_initial_with_retained
#print axioms retained_zero_of_bounded_axis

end QuantitativeArithmeticRetainedTraceRemoval
