module

public import AsymptoticClassicalEulerBadPrimesV1
public import AsymptoticClassicalEigenFrickeSlashV1
public import AsymptoticClassicalLSeriesOrderV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane AsymptoticClassicalCusp

/-- The classical Fricke eigenrelation gives every analytic condition
in the literal continuation predicate, including finite order. -/
theorem coefficients_continuation (N k : ℕ) [NeZero N] (hk : 0 < k) (heven : Even k)
    (f : CuspForm (level N) (k : ℤ)) (η : ℂ) (hη : η = 1 ∨ η = -1)
    (hfr : normalizedFricke N (Nat.pos_of_ne_zero (NeZero.ne N)) (k : ℤ) f =
      η • (f : ℍ → ℂ)) :
    FinitenessOriginalInput.Continuation N k (coefficients f) := by
  refine ⟨entireCompletion N k hk f, entireCompletion_differentiable N k hk f,
    entireCompletion_finiteOrder N k hk f, ⟨2, ?_⟩,
    Complex.I^(k : ℤ) * η, fricke_root_sign k heven hη, ?_⟩
  · intro s hs
    exact entireCompletion_eq_completed N k hk f s hs
  · intro s
    exact entireCompletion_fricke_eigen N k (Nat.pos_of_ne_zero (NeZero.ne N)) hk f η hfr s

/-- A classical cusp form with the raw newform Fourier relations and a
Fricke sign yields an actual element of the paper's complex solution set.
The operator-theoretic proofs of these arithmetic and spectral inputs
remain separate from this analytic bridge. -/
theorem coefficients_isSolution (N k : ℕ) [NeZero N] (hk : 0 < k) (heven : Even k)
    (f : CuspForm (level N) (k : ℤ))
    (hone : (qExpansion 1 f).coeff 1 = 1)
    (hmul : ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n)
    (hrec : ∀ p, p.Prime → ∀ j, (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        FinitenessEulerIdentification.xi N p * (p : ℂ)^((k : ℤ)-1) *
          (qExpansion 1 f).coeff (p^j))
    (hbad : ∀ p, p.Prime → p ∣ N →
      (qExpansion 1 f).coeff p ^ 2 = if p^2 ∣ N then 0 else (p : ℂ)^((k : ℤ)-2))
    (η : ℂ) (hη : η = 1 ∨ η = -1)
    (hfr : normalizedFricke N (Nat.pos_of_ne_zero (NeZero.ne N)) (k : ℤ) f =
      η • (f : ℍ → ℂ)) :
    FinitenessOriginalInput.IsSolution N k (coefficients f) where
  toEulerData := coefficients_eulerData f hone hmul hrec hbad
  continuation := coefficients_continuation N k hk heven f η hη hfr

#print axioms coefficients_continuation
#print axioms coefficients_isSolution

end AsymptoticClassicalLSeries
