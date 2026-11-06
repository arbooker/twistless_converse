module

public import QuantitativeArithmeticShiftedDensityCertificatesCompleteV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic
open QuantitativeHolomorphic

/-- Starting with the original fixed determinant-one matrices in each unit
residue branch, prepare them by literal integral shears and supply bounded
certificates for every matrix on one density-one set of fresh primes.
The common shifts, all preparation data, and the height constant are chosen
before the fresh prime. No density or auxiliary matrix-bound premise remains. -/
theorem density_one_prepared_matrix_certificates {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N)
    (A B C D : UnitResidue N → ι → ℤ)
    (hA : ∀ a i, A a i ≠ 0)
    (hdet : ∀ a i, A a i*D a i-(N : ℤ)*C a i*B a i=1)
    (hres : ∀ a i, (N : ℤ) ∣ A a i-(a.val.val : ℤ))
    (S : Finset ℕ) (bound : ℕ) :
    ∃ (Q : UnitResidue N → ℕ) (c : UnitResidue N → ι → ℕ)
      (n t Bhat Dhat : UnitResidue N → ι → ℤ),
      (∀ a, 0 < Q a ∧ Nat.ModEq N (Q a) a.val.val ∧ Function.Injective (c a) ∧
        ∀ i, (c a i).Prime ∧ (c a i).Coprime (N*Q a) ∧
          (Q a : ℤ)*Dhat a i-(N : ℤ)*(c a i : ℤ)*Bhat a i=1 ∧
          upperUnipotent (t a i) * lowerUnipotent N (n a i) *
            certificateMatrix (A a i) (B a i) N (C a i) (D a i) =
              certificateMatrix (Q a) (Bhat a i) N (c a i) (Dhat a i)) ∧
      ∃ K : ℝ, 0 < K ∧ ∃ Good : ℕ → Prop, RelativePrimeDensityOne Good ∧
        ∀ q : ℕ, q.Prime → Good q → q ∉ S ∧ ¬ q ∣ N ∧ bound < q ∧
          ∃ a : UnitResidue N, Nat.ModEq N q a.val.val ∧
            ∀ i, ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate
              (Q a) (Bhat a i) N (c a i) (Dhat a i) d q K) := by
  classical
  have hprep (a : UnitResidue N) := exists_prepared_natural_matrix_family
    N a.val.val hN (A a) (B a) (C a) (D a) (hA a) (hdet a) (hres a)
  choose Q c n t Bhat Dhat hQ hQres hinj hdata using hprep
  refine ⟨Q,c,n,t,Bhat,Dhat,fun a => ⟨hQ a,hQres a,hinj a,hdata a⟩,?_⟩
  exact density_one_unit_indexed_polynomial_certificates N hN Q c Bhat Dhat hQ hQres
    (fun a i => (hdata a i).2.1) (fun a i => (hdata a i).2.2.1) S bound

#print axioms density_one_prepared_matrix_certificates
end QuantitativeArithmetic
