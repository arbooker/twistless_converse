module

public import QuantitativeArithmeticShiftedDensityCertificatesV1
public import QuantitativeArithmeticShiftedDensityFinalV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic
open QuantitativeHolomorphic

/-- The literal simultaneous positive-divisor class assertion, proved from
the completed finite-sieve density theorem rather than assumed as input. -/
theorem relativePrimeDensityOne_shiftedDivisorClasses (Q M : ℕ)
    (hQ : 0 < Q) (hM : 0 < M) :
    RelativePrimeDensityOne (ShiftedDivisorClasses Q M) :=
  shiftedDivisorClasses_density_of_prime_classes Q M
    (relativePrimeDensityOne_prime_shifted_class Q M hQ hM)

/-- All fixed shifts and all unit classes hold simultaneously after any
fixed finite exclusions and any fixed lower cutoff. -/
theorem density_one_simultaneous_shifted_classes {ι : Type*} [Fintype ι]
    (Q M : ι → ℕ) (hQ : ∀ i, 0 < Q i) (hM : ∀ i, 0 < M i)
    (S : Finset ℕ) (bound : ℕ) :
    RelativePrimeDensityOne (fun q =>
      (∀ i, ShiftedDivisorClasses (Q i) (M i) q) ∧ q ∉ S ∧ bound < q) :=
  simultaneous_shifted_classes_with_exclusions Q M
    (fun i => relativePrimeDensityOne_shiftedDivisorClasses (Q i) (M i) (hQ i) (hM i)) S bound

/-- Unconditional density-one supply of uniformly bounded literal
certificates for any finite prepared integral matrix family. -/
theorem density_one_polynomial_certificates {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (Q c : ι → ℕ) (B D : ι → ℤ)
    (hQ : ∀ i, 0 < Q i) (hcop : ∀ i, (c i).Coprime (N*Q i))
    (hdet : ∀ i, (Q i : ℤ)*D i-(N : ℤ)*(c i : ℤ)*B i=1)
    (S : Finset ℕ) (bound : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Good : ℕ → Prop, RelativePrimeDensityOne Good ∧
      ∀ q : ℕ, Good q → q ∉ S ∧ bound < q ∧
        ∀ i, (N : ℤ) ∣ (q : ℤ)-(Q i : ℤ) →
          ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate (Q i) (B i) N (c i) (D i) d q K) := by
  apply finite_density_polynomial_certificates N hN Q c B D hQ hcop hdet
    (fun i => fixedMatrixHeight (certificateMatrix (Q i) (B i) N (c i) (D i)))
    (fun i => fixedMatrixHeight_nonneg _) (fun i => fixedMatrixHeight_bounds _)
  · intro i
    exact relativePrimeDensityOne_shiftedDivisorClasses (Q i) (N*Q i) (hQ i) (Nat.mul_pos hN (hQ i))

/-- The complete finite arithmetic input in the manuscript: all unit
residue branches and all fixed matrices are served by one density-one set
and one polynomial-height constant, with actual q-residue selection. -/
theorem density_one_unit_indexed_polynomial_certificates {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (Q : UnitResidue N → ℕ)
    (c : UnitResidue N → ι → ℕ) (B D : UnitResidue N → ι → ℤ)
    (hQ : ∀ a, 0 < Q a) (hQres : ∀ a, Nat.ModEq N (Q a) a.val.val)
    (hcop : ∀ a i, (c a i).Coprime (N*Q a))
    (hdet : ∀ a i, (Q a : ℤ)*D a i-(N : ℤ)*(c a i : ℤ)*B a i=1)
    (S : Finset ℕ) (bound : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Good : ℕ → Prop, RelativePrimeDensityOne Good ∧
      ∀ q : ℕ, q.Prime → Good q → q ∉ S ∧ ¬ q ∣ N ∧ bound < q ∧
        ∃ a : UnitResidue N, Nat.ModEq N q a.val.val ∧
          ∀ i, ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate (Q a) (B a i) N (c a i) (D a i) d q K) := by
  apply unit_indexed_density_polynomial_certificates N hN Q c B D hQ hQres hcop hdet
    (fun a i => fixedMatrixHeight (certificateMatrix (Q a) (B a i) N (c a i) (D a i)))
    (fun a i => fixedMatrixHeight_nonneg _) (fun a i => fixedMatrixHeight_bounds _)
  · intro a
    exact relativePrimeDensityOne_shiftedDivisorClasses (Q a) (N*Q a) (hQ a) (Nat.mul_pos hN (hQ a))

#print axioms relativePrimeDensityOne_shiftedDivisorClasses
#print axioms density_one_simultaneous_shifted_classes
#print axioms density_one_polynomial_certificates
#print axioms density_one_unit_indexed_polynomial_certificates
end QuantitativeArithmetic
