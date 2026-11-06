module

public import SpanningIntegerRowsV1
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

@[expose] public section

namespace QuantitativeArithmeticRetainedCertificate

open Matrix SpanningIntegerRows SpanningFiniteEquations SpanningCyclicCoordinates
  SpanningActualKernel SpanningTraceAlgebra

/-- Legal primitive (Ramanujan) rows together with unrestricted complete
rows at the retained moduli. The original augmented-row index is reused. -/
def rows (N : ℕ) (P : Finset ℕ) {Q : ℕ} (hQ : 0 < Q) :
    AugIndex N (P : Set ℕ) Q → Fin Q → ℤ
  | Sum.inl x => primitiveRows N hQ x
  | Sum.inr x => traceRow hQ x.1.val (Q / x.1.val) x.2

/-- Primitive legal rows and complete legal rows give the same kernel;
the unrestricted retained complete equations are unchanged. -/
theorem augmented_iff_equations {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (P : Finset ℕ) {K : Type*} [CommRing K] (v : Fin Q → K) :
    Augmented N (P : Set ℕ) Q (extend hQ v) ↔
      Equations (fun i j => (rows N P hQ i j : K)) v := by
  constructor
  · intro hv i
    cases i with
    | inl x =>
      exact ((primitive_iff_equations hQ v).mp
        ((complete_iff_primitive hN hQ _).mpr hv.1)) x
    | inr x =>
      change dotProduct (fun j => (traceRow hQ x.1.val (Q / x.1.val) x.2 j : K)) v = 0
      rw [traceRow_eval]
      exact congrFun (hv.2 x.1.val x.1.property) x.2
  · intro hv
    have hk : Kernel N Q (extend hQ v) :=
      (primitive_iff_equations hQ v).mpr (fun i => hv (Sum.inl i))
    refine ⟨(complete_iff_primitive hN hQ _).mp hk, ?_⟩
    intro ell hell
    funext u
    exact (traceRow_eval hQ ell (Q / ell) u v).symm.trans
      (hv (Sum.inr (⟨ell, hell⟩, u)))

/-- Coordinate equations detect vanishing of the full periodic augmented
kernel, with no extra divisibility assumption on the retained moduli. -/
theorem augmented_zero_iff {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (P : Finset ℕ) {K : Type*} [CommRing K] :
    (∀ f : ℤ → K, Augmented N (P : Set ℕ) Q f → f = 0) ↔
      (∀ v : Fin Q → K, Equations (fun i j => (rows N P hQ i j : K)) v → v = 0) := by
  constructor
  · intro hz v hv
    have he := hz (extend hQ v) ((augmented_iff_equations hN hQ P v).mpr hv)
    have hc := congrArg (coordinates (Q := Q)) he
    rw [coordinates_extend] at hc
    exact hc
  · intro hz f hf
    have he := extend_coordinates hQ hf.1.1
    have hv := hz (coordinates f)
      ((augmented_iff_equations hN hQ P _).mp (by rw [he]; exact hf))
    rw [← he, hv]
    rfl

/-- The actual legal primitive and retained complete rows span precisely
when the augmented kernel vanishes. -/
theorem span_top_iff {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (P : Finset ℕ) {K : Type*} [Field K] :
    Submodule.span K (Set.range (fun i j => (rows N P hQ i j : K))) = ⊤ ↔
      (∀ f : ℤ → K, Augmented N (P : Set ℕ) Q f → f = 0) := by
  rw [SpanningFiniteEquations.span_top_iff, augmented_zero_iff hN hQ P]

/-- A finite rational reconstruction with legal primitive rows and
unrestricted complete retained rows. No existence is assumed here. -/
structure Certificate (N : ℕ) (P : Finset ℕ) (Q : ℕ) (hQ : 0 < Q) where
  coeff : Fin Q → AugIndex N (P : Set ℕ) Q →₀ ℚ
  reconstruct : ∀ j : Fin Q,
    (coeff j).sum (fun i a => a • (fun t => (rows N P hQ i t : ℚ))) =
      Pi.single j 1

/-- Extract an actual finitely supported rational certificate from the
vanishing kernel at a specified grid length. -/
theorem exists_certificate_of_zero {N Q : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (P : Finset ℕ)
    (hz : ∀ f : ℤ → ℚ, Augmented N (P : Set ℕ) Q f → f = 0) :
    Nonempty (Certificate N P Q hQ) := by
  classical
  have hspan := (span_top_iff hN hQ P).mpr hz
  have hj (j : Fin Q) : ∃ a : AugIndex N (P : Set ℕ) Q →₀ ℚ,
      a.sum (fun i b => b • (fun t => (rows N P hQ i t : ℚ))) = Pi.single j 1 := by
    have hm : Pi.single j (1 : ℚ) ∈
        Submodule.span ℚ (Set.range (fun i t => (rows N P hQ i t : ℚ))) := by
      rw [hspan]
      trivial
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  choose a ha using hj
  exact ⟨⟨a, ha⟩⟩

/-- Each finite certificate is a literal coordinate identity. -/
theorem coordinate_identity {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) (j t : Fin Q) :
    ∑ i ∈ (A.coeff j).support, (A.coeff j i) * (rows N P hQ i t : ℚ) =
      if t = j then 1 else 0 := by
  classical
  have h := congrFun (A.reconstruct j) t
  simpa [Finsupp.sum, Pi.single_apply, eq_comm] using h

#print axioms augmented_iff_equations
#print axioms augmented_zero_iff
#print axioms span_top_iff
#print axioms exists_certificate_of_zero
#print axioms coordinate_identity

end QuantitativeArithmeticRetainedCertificate
