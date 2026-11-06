module

public import QuantitativeArithmeticShiftedCertificateBoundsV1
public import QuantitativeArithmeticCertificatePreparationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmetic
open Finset Filter QuantitativeHolomorphic

/-- Increasing the fixed height constant preserves the entire literal
certificate, including all its determinant and matrix identities. -/
def PolynomialPrimeCertificate.enlarge {Q B N c D d q : ℤ} {K L : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K)
    (hKL : K ≤ L) (hq : 0 ≤ q) : PolynomialPrimeCertificate Q B N c D d q L :=
  { cert with
    r_bound := cert.r_bound.trans (mul_le_mul_of_nonneg_right hKL (by exact_mod_cast hq))
    s_bound := cert.s_bound.trans (mul_le_mul_of_nonneg_right hKL (by exact_mod_cast hq))
    l_bound := cert.l_bound.trans (mul_le_mul_of_nonneg_right hKL (by exact_mod_cast hq))
    shear_height := fun i j => (cert.shear_height i j).trans
      (mul_le_mul_of_nonneg_right hKL (pow_nonneg (by exact_mod_cast hq) 3))
    canonical_height := fun i j => (cert.canonical_height i j).trans
      (mul_le_mul_of_nonneg_right hKL (pow_nonneg (by exact_mod_cast hq) 3)) }

/-- Finite simultaneous matrix construction with one constant chosen before
q. This finite algebraic theorem has no density premise. -/
theorem finite_uniform_polynomial_certificates {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (Q c : ι → ℕ) (B D : ι → ℤ)
    (hQ : ∀ i, 0 < Q i) (hcop : ∀ i, (c i).Coprime (N*Q i))
    (hdet : ∀ i, (Q i : ℤ)*D i-(N : ℤ)*(c i : ℤ)*B i=1)
    (H : ι → ℝ) (hH : ∀ i, 0 ≤ H i)
    (hM : ∀ i, MatrixEntryBound (certificateMatrix (Q i) (B i) N (c i) (D i)) (H i)) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, (∀ i, Q i < q) → 1 < q →
      (∀ i, ShiftedDivisorClasses (Q i) (N*Q i) q) →
      ∀ i, (N : ℤ) ∣ (q : ℤ)-(Q i : ℤ) →
        ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate (Q i) (B i) N (c i) (D i) d q K) := by
  classical
  have hi (i : ι) := shiftedDivisorClasses_polynomial_certificates
    (Q i) N (c i) (B i) (D i) (hQ i) hN (hcop i) (hdet i) (hH i) (hM i)
  choose K hK hcert using hi
  let L : ℝ := 1+∑ i, K i
  have hs : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => (hK i).le)
  refine ⟨L,by dsimp [L]; linarith,?_⟩
  intro q hQq hq hclasses i hres
  obtain ⟨d,⟨cert⟩⟩ := hcert i q (hQq i) hq hres (hclasses i)
  have hiK : K i ≤ L := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => (hK j).le)
      (Finset.mem_univ i)
    dsimp [L]
    linarith
  exact ⟨d,⟨cert.enlarge hiK (by exact_mod_cast (show 0 ≤ q by omega))⟩⟩

/-- Assembly lemma: all density inputs are explicit here. The unconditional
application is supplied separately from the proved shifted-density theorem. -/
theorem simultaneous_shifted_classes_with_exclusions {ι : Type*} [Fintype ι]
    (Q M : ι → ℕ) (hdensity : ∀ i, RelativePrimeDensityOne (ShiftedDivisorClasses (Q i) (M i)))
    (S : Finset ℕ) (bound : ℕ) :
    RelativePrimeDensityOne (fun q =>
      (∀ i, ShiftedDivisorClasses (Q i) (M i) q) ∧ q ∉ S ∧ bound < q) := by
  classical
  have hall := relativePrimeDensityOne_finset Finset.univ
    (fun i => ShiftedDivisorClasses (Q i) (M i)) (fun i _ => hdensity i)
  have hex := relativePrimeDensityOne_remove_finset hall (S ∪ Finset.range (bound+1))
  apply relativePrimeDensityOne_mono hex
  intro q hq
  simp only [Finset.mem_univ, forall_const] at hq
  exact ⟨hq.1,fun hs => hq.2 (Finset.mem_union_left _ hs),by
    have hh : q ∉ Finset.range (bound+1) := fun hh => hq.2 (Finset.mem_union_right _ hh)
    simpa only [Finset.mem_range, not_lt, Nat.add_one_le_iff] using hh⟩

/-- A concrete height for any fixed integral matrix; no matrix-bound
hypothesis is required when constructing the final certificate family. -/
def fixedMatrixHeight (M : IntegerMatrix2) : ℝ := ∑ i : Fin 2, ∑ j : Fin 2, |(M i j : ℝ)|

theorem fixedMatrixHeight_nonneg (M : IntegerMatrix2) : 0 ≤ fixedMatrixHeight M := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))

theorem fixedMatrixHeight_bounds (M : IntegerMatrix2) : MatrixEntryBound M (fixedMatrixHeight M) := by
  intro i j
  have hj : |(M i j : ℝ)| ≤ ∑ j : Fin 2, |(M i j : ℝ)| :=
    Finset.single_le_sum (f := fun j : Fin 2 => |(M i j : ℝ)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hi : (∑ j : Fin 2, |(M i j : ℝ)|) ≤ fixedMatrixHeight M :=
    Finset.single_le_sum (f := fun i : Fin 2 => ∑ j : Fin 2, |(M i j : ℝ)|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
  exact hj.trans hi

/-- The existing signed-integer Dirichlet/CRT preparation supplies actual
positive natural shifts and prime lower entries for a fixed matrix family.
The returned matrices are the literal integral shears of the originals. -/
theorem exists_prepared_natural_matrix_family {ι : Type*} [Fintype ι]
    (N a : ℕ) (hN : 0 < N) (A B C D : ι → ℤ)
    (hA : ∀ i, A i ≠ 0)
    (hdet : ∀ i, A i*D i-(N : ℤ)*C i*B i=1)
    (hres : ∀ i, (N : ℤ) ∣ A i-(a : ℤ)) :
    ∃ (Q : ℕ) (c : ι → ℕ) (n t Bhat Dhat : ι → ℤ),
      0 < Q ∧ Nat.ModEq N Q a ∧ Function.Injective c ∧
      ∀ i, (c i).Prime ∧ (c i).Coprime (N*Q) ∧
        (Q : ℤ)*Dhat i-(N : ℤ)*(c i : ℤ)*Bhat i=1 ∧
        upperUnipotent (t i) * lowerUnipotent N (n i) * certificateMatrix (A i) (B i) N (C i) (D i) =
          certificateMatrix Q (Bhat i) N (c i) (Dhat i) := by
  have hAC (i : ι) : IsCoprime (A i) (C i) :=
    ⟨D i,-(N : ℤ)*B i,by nlinarith [hdet i]⟩
  obtain ⟨c,n,t,Qz,hQz,hcinj,hQres,hprep⟩ :=
    exists_fixed_certificate_preparation N hN a A C hA (fun i => (hAC i).symm) hres
  let Q : ℕ := Qz.toNat
  have hQcast : (Q : ℤ)=Qz := Int.toNat_of_nonneg hQz.le
  have hQpos : 0 < Q := by exact_mod_cast (show (0 : ℤ)<Q by rw [hQcast]; exact hQz)
  have hQres' : Nat.ModEq N Q a := by
    apply Int.natCast_modEq_iff.mp
    apply Int.modEq_iff_dvd.mpr
    rw [hQcast]
    simpa only [neg_sub] using dvd_neg.mpr hQres
  let Bhat : ι → ℤ := fun i => B i+t i*((N : ℤ)*n i*B i+D i)
  let Dhat : ι → ℤ := fun i => (N : ℤ)*n i*B i+D i
  refine ⟨Q,c,n,t,Bhat,Dhat,hQpos,hQres',hcinj,?_⟩
  intro i
  have hcprime := (hprep i).1
  have hcnodvd : ¬c i ∣ N*Q := by
    intro hd
    apply (hprep i).2.2.2.2
    have hz : (c i : ℤ) ∣ (N : ℤ)*(Q : ℤ) := by exact_mod_cast hd
    simpa only [hQcast] using hz
  have hs : (Q : ℤ)=A i+(N : ℤ)*t i*(c i : ℤ) := by
    rw [hQcast]
    convert (hprep i).2.2.2.1 using 1
    ring
  have hr := (hprep i).2.2.1
  have hshear := certificate_shear_of_witnesses (A i) (B i) N (C i) (D i) (n i) (t i) (c i) Q hr hs
  refine ⟨hcprime,hcprime.coprime_iff_not_dvd.mpr hcnodvd,?_,hshear⟩
  have hd := certificate_shear_det (A i) (B i) N (C i) (D i) (n i) (t i)
  rw [← hr, ← hs, certificate_det, certificate_det] at hd
  exact hd.trans (hdet i)

/-- Canonical representatives of all unit classes, including the sole class
at modulus one. This indexing does not exclude the residue zero when M=1. -/
abbrev UnitResidue (M : ℕ) := {a : Fin M // Nat.Coprime a.val M}

/-- Finite intersection of the prime-divisor class results gives exactly the
positive-divisor predicate already consumed by the certificate construction. -/
theorem shiftedDivisorClasses_density_of_prime_classes (Q M : ℕ)
    (hprime : ∀ a : ZMod M, IsUnit a → RelativePrimeDensityOne
      (fun p => ∃ l : ℕ, l.Prime ∧ (l : ZMod M)=a ∧ (l : ℤ) ∣ (p : ℤ)-(Q : ℤ))) :
    RelativePrimeDensityOne (ShiftedDivisorClasses Q M) := by
  classical
  let P : UnitResidue M → ℕ → Prop := fun a p =>
    ∃ l : ℕ, l.Prime ∧ (l : ZMod M)=(a.val.val : ZMod M) ∧ (l : ℤ) ∣ (p : ℤ)-(Q : ℤ)
  have hall := relativePrimeDensityOne_finset Finset.univ P (fun a _ =>
    hprime (a.val.val : ZMod M) ((ZMod.isUnit_iff_coprime a.val.val M).mpr a.property))
  apply relativePrimeDensityOne_mono hall
  intro p hp a ha hacop
  let i : UnitResidue M := ⟨⟨a,ha⟩,hacop⟩
  obtain ⟨l,hl,hlclass,hldiv⟩ := hp i (Finset.mem_univ i)
  exact ⟨l,hl.pos,hldiv,(ZMod.natCast_eq_natCast_iff l a M).mp hlclass⟩

/-- Explicit finite assembly from the density inputs to uniformly bounded
literal certificates. The set and height constant are fixed before q. -/
theorem finite_density_polynomial_certificates {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (Q c : ι → ℕ) (B D : ι → ℤ)
    (hQ : ∀ i, 0 < Q i) (hcop : ∀ i, (c i).Coprime (N*Q i))
    (hdet : ∀ i, (Q i : ℤ)*D i-(N : ℤ)*(c i : ℤ)*B i=1)
    (H : ι → ℝ) (hH : ∀ i, 0 ≤ H i)
    (hM : ∀ i, MatrixEntryBound (certificateMatrix (Q i) (B i) N (c i) (D i)) (H i))
    (hdensity : ∀ i, RelativePrimeDensityOne (ShiftedDivisorClasses (Q i) (N*Q i)))
    (S : Finset ℕ) (bound : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Good : ℕ → Prop, RelativePrimeDensityOne Good ∧
      ∀ q : ℕ, Good q → q ∉ S ∧ bound < q ∧
        ∀ i, (N : ℤ) ∣ (q : ℤ)-(Q i : ℤ) →
          ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate (Q i) (B i) N (c i) (D i) d q K) := by
  classical
  obtain ⟨K,hK,hcert⟩ := finite_uniform_polynomial_certificates N hN Q c B D hQ hcop hdet H hH hM
  let L : ℕ := max bound (max 1 (Finset.univ.sup Q))
  let Good : ℕ → Prop := fun q => (∀ i, ShiftedDivisorClasses (Q i) (N*Q i) q) ∧ q ∉ S ∧ L < q
  refine ⟨K,hK,Good,simultaneous_shifted_classes_with_exclusions Q (fun i => N*Q i) hdensity S L,?_⟩
  intro q hq
  have hL : bound ≤ L ∧ 1 ≤ L ∧ Finset.univ.sup Q ≤ L := by dsimp [L]; omega
  refine ⟨hq.2.1,by omega,?_⟩
  apply hcert q
  · intro i
    have hi := Finset.le_sup (f := Q) (Finset.mem_univ i)
    omega
  · omega
  · exact hq.1

/-- A fresh prime selects its actual unit residue class, and every fixed
matrix in that class receives a bounded certificate. Initial excluded primes
and divisors of the level are removed by a proved finite-exclusion step. -/
theorem unit_indexed_density_polynomial_certificates {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (Q : UnitResidue N → ℕ)
    (c : UnitResidue N → ι → ℕ) (B D : UnitResidue N → ι → ℤ)
    (hQ : ∀ a, 0 < Q a) (hQres : ∀ a, Nat.ModEq N (Q a) a.val.val)
    (hcop : ∀ a i, (c a i).Coprime (N*Q a))
    (hdet : ∀ a i, (Q a : ℤ)*D a i-(N : ℤ)*(c a i : ℤ)*B a i=1)
    (H : UnitResidue N → ι → ℝ) (hH : ∀ a i, 0 ≤ H a i)
    (hM : ∀ a i, MatrixEntryBound (certificateMatrix (Q a) (B a i) N (c a i) (D a i)) (H a i))
    (hdensity : ∀ a, RelativePrimeDensityOne (ShiftedDivisorClasses (Q a) (N*Q a)))
    (S : Finset ℕ) (bound : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Good : ℕ → Prop, RelativePrimeDensityOne Good ∧
      ∀ q : ℕ, q.Prime → Good q → q ∉ S ∧ ¬ q ∣ N ∧ bound < q ∧
        ∃ a : UnitResidue N, Nat.ModEq N q a.val.val ∧
          ∀ i, ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate (Q a) (B a i) N (c a i) (D a i) d q K) := by
  classical
  obtain ⟨K,hK,Good,hGood,hcert⟩ := finite_density_polynomial_certificates
    N hN (fun j : UnitResidue N × ι => Q j.1) (fun j => c j.1 j.2)
    (fun j => B j.1 j.2) (fun j => D j.1 j.2) (fun j => hQ j.1)
    (fun j => hcop j.1 j.2) (fun j => hdet j.1 j.2)
    (fun j => H j.1 j.2) (fun j => hH j.1 j.2) (fun j => hM j.1 j.2)
    (fun j => hdensity j.1) (S ∪ N.primeFactors) bound
  refine ⟨K,hK,Good,hGood,?_⟩
  intro q hq hG
  obtain ⟨hex,hbound,hcertq⟩ := hcert q hG
  have hqN : ¬q ∣ N := by
    intro hd
    exact hex (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hq,hd,hN.ne'⟩))
  have hcopq : q.Coprime N := hq.coprime_iff_not_dvd.mpr hqN
  have hcopmod : (q%N).Coprime N := by
    change Nat.gcd (q%N) N=1
    rw [← Nat.gcd_rec]
    exact hcopq.symm
  let a : UnitResidue N := ⟨⟨q%N,Nat.mod_lt q hN⟩,hcopmod⟩
  have hqa : Nat.ModEq N q a.val.val := by simp [a,Nat.ModEq]
  have hqQ : Nat.ModEq N q (Q a) := hqa.trans (hQres a).symm
  have hres : (N : ℤ) ∣ (q : ℤ)-(Q a : ℤ) :=
    (Int.natCast_modEq_iff.mpr hqQ).symm.dvd
  refine ⟨fun hs => hex (Finset.mem_union_left _ hs),hqN,hbound,a,hqa,?_⟩
  intro i
  exact hcertq (a,i) hres

#print axioms unit_indexed_density_polynomial_certificates
#print axioms shiftedDivisorClasses_density_of_prime_classes
#print axioms finite_density_polynomial_certificates
#print axioms finite_uniform_polynomial_certificates
#print axioms simultaneous_shifted_classes_with_exclusions
#print axioms exists_prepared_natural_matrix_family
end QuantitativeArithmetic
