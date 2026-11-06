module

public import FinitenessAllLevelGlobalSectorProperV1
public import FinitenessAllLevelEigenvalueFibersV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelFormalContinuation
  FinitenessAllLevelCertificatePencil FinitenessOriginalInput
  QuantitativeArithmeticRetainedCertificate

/-- The fibers of the exact sector locus are finite, by its proved injection
into the actual original Euler-solution fiber. This does not assert discreteness
of the whole locus or finiteness of its union over eigenvalues. -/
theorem global_sector_fiber_finite {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool) (lam : ℂ) :
    {t : ℂ × space (radius a) | t ∈ sectorLocus hN A P hb hba m s ∧ t.1 = lam}.Finite := by
  classical
  obtain ⟨_, _, hfib⟩ := FinitenessAllLevelEigenvalueFibers.uniform_fiber_bound
    hN hp hgood hlarge (norm_nonneg lam)
  have hf := (hfib m hm lam le_rfl).1
  let := hf.fintype
  let c : FinitenessAllLevelEigenvalueFibers.fiber N (2 * m) p lam → ℂ × space (radius a) :=
    fun f => FinitenessAllLevelDiskCoordinates.coordinates N (2 * m) p
      (radius_pos a) (radius_lt_one (hb.trans hba)) (FinitenessAllLevelEigenvalueFibers.toSolution f)
  apply (Set.finite_range c).subset
  intro t ht
  obtain ⟨f, he, hF⟩ := constraints_recover_global hN hp hpQ hm A P (hb.trans hba) hae
    (sector Q m s) t.1 t.2 (fun q _ => sector_norm Q m s q)
    (sector_signs Q m s 1) ht.1.2
  refine ⟨⟨f.val, f.property, he.trans ht.2⟩, ?_⟩
  exact Prod.ext he hF

#print axioms global_sector_fiber_finite

end FinitenessAllLevelConstraintLocus
