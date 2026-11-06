module

public import QuantitativeEulerDensityGeneratorsV1
public import QuantitativeArithmeticDensityTransferV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open QuantitativeArithmetic QuantitativeHolomorphic

/-- A concrete preparation of the actual Γ₁ generator family. Its matrix
identities, density and polynomial heights are proved when it is constructed;
they are not hypotheses required of the Euler solutions. -/
structure Prepared (N : ℕ) [NeZero N] (excluded : Finset ℕ) (threshold : ℕ) where
  Q : UnitResidue N → ℕ
  c : UnitResidue N → Option (Generator N) → ℕ
  n : UnitResidue N → Option (Generator N) → ℤ
  t : UnitResidue N → Option (Generator N) → ℤ
  B : UnitResidue N → Option (Generator N) → ℤ
  D : UnitResidue N → Option (Generator N) → ℤ
  Q_pos : ∀ a, 0<Q a
  Q_residue : ∀ a, Nat.ModEq N (Q a) a.val.val
  c_injective : ∀ a, Function.Injective (c a)
  c_prime : ∀ a i, (c a i).Prime
  c_coprime : ∀ a i, (c a i).Coprime (N*Q a)
  determinant : ∀ a i, (Q a : ℤ)*D a i-(N : ℤ)*(c a i : ℤ)*B a i=1
  shear : ∀ a i, upperUnipotent (t a i)*lowerUnipotent N (n a i)*(family N a i).val =
    certificateMatrix (Q a) (B a i) N (c a i) (D a i)
  K : ℝ
  K_pos : 0<K
  Good : ℕ → Prop
  density : RelativePrimeDensityOne Good
  prime_data : ∀ q : ℕ, q.Prime → Good q → q∉excluded ∧ ¬q∣N ∧ threshold<q ∧
    ∃ a : UnitResidue N, Nat.ModEq N q a.val.val ∧
      ∀ i, ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate
        (Q a) (B a i) N (c a i) (D a i) d q K)

/-- Unconditional density-one polynomial certificates for every actual
fixed Γ₁(N) generator, simultaneously in all possible fresh-prime residues.
The level-one elementary-unipotent case is separate. -/
theorem exists_prepared (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) : Nonempty (Prepared N excluded threshold) := by
  classical
  obtain ⟨Q,c,n,t,B,D,hprep,K,hK,Good,hGood,hcert⟩ :=
    density_one_prepared_matrix_certificates N (by omega)
      (fun a i => family N a i 0 0) (fun a i => family N a i 0 1)
      (lowerEntry N) (fun a i => family N a i 1 1)
      (family_leading_nonzero N hN) (family_det N) (family_residue_dvd N)
      excluded threshold
  refine ⟨{
    Q := Q
    c := c
    n := n
    t := t
    B := B
    D := D
    Q_pos := fun a => (hprep a).1,
    Q_residue := fun a => (hprep a).2.1,
    c_injective := fun a => (hprep a).2.2.1,
    c_prime := fun a i => ((hprep a).2.2.2 i).1,
    c_coprime := fun a i => ((hprep a).2.2.2 i).2.1,
    determinant := fun a i => ((hprep a).2.2.2 i).2.2.1,
    shear := ?_, K := K, K_pos := hK, Good := Good,
    density := hGood, prime_data := hcert }⟩
  intro a i
  simpa only [family_matrix] using ((hprep a).2.2.2 i).2.2.2

def prepared (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ) :
    Prepared N excluded threshold := (exists_prepared N hN excluded threshold).some

/-- No density hypothesis remains in the prime contraction product for
the actual prepared generator family. Every exponent below the one-prime
contraction coefficient is available without a progression-density loss. -/
theorem prepared_product (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) {σ b : ℝ}
    (hσ : 0<σ) (hσ1 : σ≤1) (hb : 0≤b) (hbσ : b<σ) :
    let P := prepared N hN excluded threshold
    letI : DecidablePred P.Good := Classical.decPred _
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n →
      (∏ p ∈ (n+1).primesBelow.filter P.Good, (1-σ/((p : ℝ)-1))) ≤
        Real.exp C * (Real.log (n+1 : ℝ))^(-b) := by
  classical
  exact good_prime_product_of_relative_density_one _
    (prepared N hN excluded threshold).density hσ hσ1 hb hbσ

#print axioms exists_prepared
#print axioms prepared_product
end QuantitativeEulerDensityGenerators
