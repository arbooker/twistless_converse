module

public import QuantitativeEulerEndpointGoodSetsV1
public import QuantitativeEulerDensityPreparedV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Finset QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerEndpointAP
attribute [local instance] Classical.propDecidable

/-- Rebuild the good set of an actual preparation using the proved
shifted-divisor conditions. All fixed matrix data are retained, while a
new uniform height constant is supplied by the finite algebraic theorem. -/
theorem exists_summable_preparation (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) :
    ∃ P : Prepared N excluded threshold, Summable (badPrimeLoss P.Good) := by
  obtain ⟨P⟩ := exists_prepared N hN excluded threshold
  let Q : UnitResidue N × Option (Generator N) → ℕ := fun j => P.Q j.1
  let c : UnitResidue N × Option (Generator N) → ℕ := fun j => P.c j.1 j.2
  let B : UnitResidue N × Option (Generator N) → ℤ := fun j => P.B j.1 j.2
  let D : UnitResidue N × Option (Generator N) → ℤ := fun j => P.D j.1 j.2
  obtain ⟨K,hK,hcert⟩ := finite_uniform_polynomial_certificates N (by omega) Q c B D
    (fun j => P.Q_pos j.1) (fun j => P.c_coprime j.1 j.2)
    (fun j => P.determinant j.1 j.2)
    (fun j => fixedMatrixHeight (certificateMatrix (Q j) (B j) N (c j) (D j)))
    (fun _ => fixedMatrixHeight_nonneg _) (fun _ => fixedMatrixHeight_bounds _)
  let L : ℕ := max threshold (max 1 (univ.sup P.Q))
  let S : Finset ℕ := excluded ∪ N.primeFactors
  let Good : ℕ → Prop := fun p =>
    (∀ a, ShiftedDivisorClasses (P.Q a) (N*P.Q a) p) ∧ p∉S ∧ L<p
  have hdensity : RelativePrimeDensityOne Good :=
    density_one_simultaneous_shifted_classes P.Q (fun a => N*P.Q a)
      P.Q_pos (fun a => Nat.mul_pos (by omega) (P.Q_pos a)) S L
  have hsum : Summable (badPrimeLoss Good) :=
    simultaneous_shifted_classes_exception_summable P.Q (fun a => N*P.Q a)
      P.Q_pos (fun a => Nat.mul_pos (by omega) (P.Q_pos a)) S L
  have hdata : ∀ q : ℕ, q.Prime → Good q → q∉excluded ∧ ¬q∣N ∧ threshold<q ∧
      ∃ a : UnitResidue N, Nat.ModEq N q a.val.val ∧
        ∀ i, ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate
          (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q K) := by
    intro q hq hG
    have hL : threshold≤L ∧ 1≤L ∧ univ.sup P.Q≤L := by dsimp [L]; omega
    have hqN : ¬q∣N := by
      intro hd
      exact hG.2.1 (mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hq,hd,NeZero.ne N⟩))
    have hcopq : q.Coprime N := hq.coprime_iff_not_dvd.mpr hqN
    have hcopmod : (q%N).Coprime N := by
      change Nat.gcd (q%N) N=1
      rw [← Nat.gcd_rec]
      exact hcopq.symm
    let a : UnitResidue N := ⟨⟨q%N,Nat.mod_lt q (by omega)⟩,hcopmod⟩
    have hqa : Nat.ModEq N q a.val.val := by simp [a,Nat.ModEq]
    have hqQ : Nat.ModEq N q (P.Q a) := hqa.trans (P.Q_residue a).symm
    have hres : (N : ℤ)∣(q : ℤ)-(P.Q a : ℤ) :=
      (Int.natCast_modEq_iff.mpr hqQ).symm.dvd
    refine ⟨fun hs => hG.2.1 (mem_union_left _ hs),hqN,lt_of_le_of_lt hL.1 hG.2.2,a,hqa,?_⟩
    intro i
    apply hcert q (fun j => ?_) (lt_of_le_of_lt hL.2.1 hG.2.2)
      (fun j => hG.1 j.1) (a,i) hres
    exact lt_of_le_of_lt ((le_sup (f := P.Q) (mem_univ j.1)).trans hL.2.2) hG.2.2
  exact ⟨{ P with K := K, K_pos := hK, Good := Good, density := hdensity, prime_data := hdata },hsum⟩

/-- An actual preparation chosen from the unconditional construction. -/
def prepared (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) : Prepared N excluded threshold :=
  (exists_summable_preparation N hN excluded threshold).choose

theorem prepared_exception_summable (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) :
    Summable (badPrimeLoss (prepared N hN excluded threshold).Good) :=
  (exists_summable_preparation N hN excluded threshold).choose_spec

/-- Endpoint contraction product for the SAME actual good-prime family
that supplies every prepared Γ₁ generator certificate. No density or
summability premise is left to the Euler solutions. -/
theorem prepared_endpoint_product (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) :
    let P := prepared N hN excluded threshold
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 0<n →
      (∏ p∈(n+1).primesBelow.filter P.Good,
        (1-(1-1/(p : ℝ))/((p : ℝ)-1)))≤C/Real.log (n+1 : ℝ) :=
  QuantitativeEulerEndpointProduct.endpoint_product_of_summable_exceptions _
    (prepared_exception_summable N hN excluded threshold)

#print axioms exists_summable_preparation
#print axioms prepared_exception_summable
#print axioms prepared_endpoint_product
end QuantitativeEulerEndpointPrepared
