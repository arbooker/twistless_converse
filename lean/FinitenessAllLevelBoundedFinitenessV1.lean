module

public import FinitenessAllLevelSectorFinitenessV1
public import FinitenessAllLevelAuxiliaryV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelBoundedFiniteness

open Complex Set FinitenessOriginalInput FinitenessAllLevelGlobalHeight
  FinitenessAllLevelConstraintLocus FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelDiskCoordinates
  FinitenessAllLevelAuxiliary QuantitativeArithmeticRetainedCertificate

/-- Choose a second, distinct good prime at every positive level. -/
theorem second_large_good_prime (N p : ℕ) (hN : 0 < N) :
    ∃ r : ℕ, r.Prime ∧ ¬ r ∣ N ∧ N < r ^ 2 ∧ p ≠ r := by
  obtain ⟨r, hrsize, hr⟩ := Nat.exists_infinite_primes (N + p + 1)
  have hNr : N < r := by omega
  have hpr : p < r := by omega
  refine ⟨r, hr, ?_, by nlinarith [hr.two_le], Nat.ne_of_lt hpr⟩
  intro hd
  exact (not_le_of_gt hNr) (Nat.le_of_dvd hN hd)

/-- The paper's bounded-eigenvalue finiteness proposition, for literal
original Euler-product solutions at EVERY positive level. -/
theorem bounded_original {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m) (B : ℝ) :
    {f : ℕ → ℂ | IsSolution N (2 * m) f ∧ ‖f p‖ ≤ B}.Finite := by
  obtain ⟨r, hr, hrgood, hrlarge, hne⟩ := second_large_good_prime N p hN
  obtain ⟨Q, hQ, _, hpQ, ⟨A⟩⟩ := certificate_at_prime hN hp hlarge
  obtain ⟨P⟩ := parameters_exist hN hQ A (L := 0) le_rfl
  obtain ⟨a, b, hb, hba, hae, hheight⟩ := chart_heights_exist A P
  let c := coordinates N (2 * m) p (radius_pos a) (radius_lt_one (hb.trans hba))
  have hc : Function.Injective c := coordinates_injective N (2 * m) p _ _
  have hu : (⋃ s : Fin (Q + 1) → Bool,
      {t : ℂ × space (radius a) | t ∈ sectorLocus hN A P hb hba m s ∧ ‖t.1‖ ≤ B}).Finite :=
    Set.finite_iUnion (fun s => sector_bounded_finite hN hp hgood hlarge hr hrgood hrlarge hne
      hpQ A P hb hba hae hm s B)
  have hsub : {f : S N (2 * m) | ‖f.val p‖ ≤ B}.Finite := by
    apply (hu.preimage hc.injOn).subset
    intro f hf
    obtain ⟨s, hs⟩ := (global_finite_locus_iff_original hN hp hgood hpQ A P hb hba hae hheight hm (c f)).mpr
      ⟨f, rfl, rfl⟩
    exact mem_iUnion.mpr ⟨s, hs, hf⟩
  apply (hsub.image Subtype.val).subset
  intro f hf
  exact ⟨⟨f, hf.1⟩, hf.2, rfl⟩

/-- Same proposition for an arbitrary positive even weight. -/
theorem bounded_original_even {N p k : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) (hk : 0 < k) (heven : Even k) (B : ℝ) :
    {f : ℕ → ℂ | IsSolution N k f ∧ ‖f p‖ ≤ B}.Finite := by
  obtain ⟨m, hm⟩ := heven
  have hk' : k = 2 * m := by omega
  rw [hk'] at hk ⊢
  exact bounded_original (m := m) hN hp hgood hlarge (by omega) B

#print axioms second_large_good_prime
#print axioms bounded_original
#print axioms bounded_original_even

end FinitenessAllLevelBoundedFiniteness
