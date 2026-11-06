module

public import QuantitativeArithmeticCertificateChoiceV1
public import QuantitativeArithmeticDensityV1

set_option autoImplicit false
@[expose] public noncomputable section

/-!
Polynomial-height completion of the literal shifted-divisor certificate.
The divisor-class assertion is an input for one integer q, not an asserted
analytic density theorem. All matrices below are the actual integral matrices;
in particular their inverses are proved equal to integral adjugates.
-/

namespace QuantitativeArithmetic

open QuantitativeHolomorphic

def inverseMatrix2 (M : IntegerMatrix2) : IntegerMatrix2 :=
  !![M 1 1, -M 0 1; -M 1 0, M 0 0]

theorem inverseMatrix2_mul (M : IntegerMatrix2) (hM : M.det = 1) :
    inverseMatrix2 M * M = 1 ∧ M * inverseMatrix2 M = 1 := by
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hM
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [inverseMatrix2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals nlinarith [hd]

theorem inverseMatrix2_entry_bound {M : IntegerMatrix2} {H : ℝ}
    (hM : MatrixEntryBound M H) : MatrixEntryBound (inverseMatrix2 M) H := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simpa [inverseMatrix2] using hM _ _

theorem canonical_translation_real_bound (q B l : ℤ) {A : ℝ}
    (hq : 1 ≤ q) (hB : |(B : ℝ)| ≤ A*(q : ℝ)^2)
    (hl : q*|l| ≤ |B|+q) : |(l : ℝ)| ≤ (A+1)*(q : ℝ) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlr : (q : ℝ)*|(l : ℝ)| ≤ |(B : ℝ)|+(q : ℝ) := by exact_mod_cast hl
  have hqq : (q : ℝ) ≤ (q : ℝ)^2 := by nlinarith
  have hb : (q : ℝ)*|(l : ℝ)| ≤ (A+1)*(q : ℝ)^2 := by nlinarith
  nlinarith

theorem certificate_canonical_entry_bound (M : IntegerMatrix2) (N l : ℤ)
    {A q : ℝ} (hA : 0 ≤ A) (hq : 1 ≤ q)
    (hM : MatrixEntryBound M (A*q^2)) (hl : |(l : ℝ)| ≤ (A+1)*q) :
    MatrixEntryBound (lowerUnipotent N (-1) * M * upperUnipotent l)
      (4*(1+|(N : ℝ)|)*A*(A+2)*q^3) := by
  have hV : MatrixEntryBound (lowerUnipotent N (-1)) (1+|(N : ℝ)|) := by
    simpa using lowerUnipotent_entry_bound N (-1)
  have hU := upperUnipotent_entry_bound l
  have hVM := matrix_entry_bound_mul (by positivity) hV hM
  have hVMU := matrix_entry_bound_mul (by positivity) hVM hU
  have hlast : 1+|(l : ℝ)| ≤ (A+2)*q := by nlinarith
  intro i j
  calc
    _ ≤ 2*(2*(1+|(N : ℝ)|)*(A*q^2))*(1+|(l : ℝ)|) := hVMU i j
    _ ≤ 2*(2*(1+|(N : ℝ)|)*(A*q^2))*((A+2)*q) := by gcongr
    _ = _ := by ring

/-- All varying quantities in a canonical certificate, with no assumed
modularity, density, or existence of an unbounded word factorization. -/
structure PolynomialPrimeCertificate (Q B N c D d q : ℤ) (K : ℝ) where
  r : ℤ
  s : ℤ
  β : ℤ
  l : ℤ
  B' : ℤ
  D' : ℤ
  divisor_eq : d = c+r*Q
  prime_entry_eq : q = Q+N*s*d
  alpha_range : 1 ≤ q-d ∧ q-d < q
  beta_range : 1 ≤ β ∧ β < q
  residue_eq : B'+q*l = -β
  shear_eq : upperUnipotent s * lowerUnipotent N r * certificateMatrix Q B N c D =
    certificateMatrix q B' N d D'
  canonical_eq : lowerUnipotent N (-1) * certificateMatrix q B' N d D' *
    upperUnipotent l = !![q, -β; -N*(q-d), D'+N*d*l+N*β]
  canonical_bottom_eq : q*(D'+N*d*l+N*β) = 1+N*(q-d)*β
  shear_det : (certificateMatrix q B' N d D').det = 1
  canonical_det : (lowerUnipotent N (-1) * certificateMatrix q B' N d D' *
    upperUnipotent l).det = 1
  r_bound : |(r : ℝ)| ≤ K*(q : ℝ)
  s_nonneg : 0 ≤ s
  s_bound : |(s : ℝ)| ≤ K*(q : ℝ)
  l_bound : |(l : ℝ)| ≤ K*(q : ℝ)
  shear_height : MatrixEntryBound (certificateMatrix q B' N d D') (K*(q : ℝ)^3)
  canonical_height : MatrixEntryBound
    (lowerUnipotent N (-1) * certificateMatrix q B' N d D' * upperUnipotent l)
    (K*(q : ℝ)^3)

/-- The integer adjugates really are inverses, with the same entry bounds.
This records both inverse identities rather than merely bounding a formal
matrix called an inverse. -/
theorem PolynomialPrimeCertificate.inverse_bounds {Q B N c D d q : ℤ} {K : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K) :
    let M := certificateMatrix q cert.B' N d cert.D'
    let C := lowerUnipotent N (-1) * M * upperUnipotent cert.l
    (inverseMatrix2 M * M = 1 ∧ M * inverseMatrix2 M = 1) ∧
    (inverseMatrix2 C * C = 1 ∧ C * inverseMatrix2 C = 1) ∧
    MatrixEntryBound (inverseMatrix2 M) (K*(q : ℝ)^3) ∧
    MatrixEntryBound (inverseMatrix2 C) (K*(q : ℝ)^3) := by
  exact ⟨inverseMatrix2_mul _ cert.shear_det, inverseMatrix2_mul _ cert.canonical_det,
    inverseMatrix2_entry_bound cert.shear_height,
    inverseMatrix2_entry_bound cert.canonical_height⟩

/-- The constant depends only on the fixed matrix and level. For every
admissible divisor the theorem constructs the literal certificate with all
variable exponents O(q), heights O(q^3), and determinant exactly one.
Primality is not needed for this finite arithmetic construction. -/
theorem exists_uniform_polynomial_certificates (Q B N c D x y : ℤ)
    (hQ : 0 < Q) (hN : 0 < N) (hdet : Q*D-N*c*B = 1)
    (hcop : x*N+y*c = 1) {H : ℝ} (hH : 0 ≤ H)
    (hM : MatrixEntryBound (certificateMatrix Q B N c D) H) :
    ∃ K : ℝ, 0 < K ∧ ∀ d q : ℤ, 0 < d → d < q → Q ≤ q → 1 < q →
      N*Q ∣ d-c → N ∣ q-Q → d ∣ q-Q →
      Nonempty (PolynomialPrimeCertificate Q B N c D d q K) := by
  let C : ℝ := 1+|(c : ℝ)|
  let A : ℝ := 4*(1+C)*(1+|(N : ℝ)| * C)*H
  let L : ℝ := 4*(1+|(N : ℝ)|)*A*(A+2)
  let K : ℝ := 1+C+(A+1)+L+A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hCK : C ≤ K := by dsimp [K]; linarith
  have hAK : A ≤ K := by dsimp [K]; linarith
  have hLK : L ≤ K := by dsimp [K]; linarith
  have hAlK : A+1 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro d q hd hdq hQq hq hcong hNdiv hddiv
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqnonneg : (0 : ℝ) ≤ q := by linarith
  obtain ⟨r, s, hr, hs, hrbound, hsnonneg, hsbound⟩ :=
    exists_bounded_shear_witnesses Q N c d q x y hQ hN hd (by omega) hQq
      hcop hcong hNdiv hddiv
  let B' := B+s*(N*r*B+D)
  let D' := N*r*B+D
  have hshear := certificate_shear_of_witnesses Q B N c D r s d q hr hs
  have hdet' : q*D'-N*d*B' = 1 := by
    have he := certificate_shear_det Q B N c D r s
    rw [← hr, ← hs, certificate_det, certificate_det] at he
    exact he.trans hdet
  have hdetM : (certificateMatrix q B' N d D').det = 1 := by
    rw [certificate_det]; exact hdet'
  obtain ⟨β, l, hβpos, hβlt, hβeq, hlbound⟩ :=
    exists_canonical_residue q B' N d D' hq hdet'
  have hrr : |(r : ℝ)| ≤ C*(q : ℝ) := by
    have hh : |(r : ℝ)| ≤ (q : ℝ)+|(c : ℝ)| := by exact_mod_cast hrbound
    dsimp [C]
    nlinarith [abs_nonneg (c : ℝ)]
  have hsr : |(s : ℝ)| ≤ C*(q : ℝ) := by
    have hs0 : (0 : ℝ) ≤ s := by exact_mod_cast hsnonneg
    have hsq : (s : ℝ) ≤ q := by exact_mod_cast hsbound
    rw [abs_of_nonneg hs0]
    dsimp [C]
    nlinarith [abs_nonneg (c : ℝ)]
  have hMbound : MatrixEntryBound (certificateMatrix q B' N d D') (A*(q : ℝ)^2) := by
    rw [← hshear]
    exact certificate_shear_polynomial_entry_bound _ N r s hH hC hqr hM hrr hsr
  have hBbound : |(B' : ℝ)| ≤ A*(q : ℝ)^2 := by
    simpa [certificateMatrix] using hMbound 0 1
  have hlr : |(l : ℝ)| ≤ (A+1)*(q : ℝ) :=
    canonical_translation_real_bound q B' l (by omega) hBbound hlbound
  have hCbound := certificate_canonical_entry_bound
    (certificateMatrix q B' N d D') N l hA hqr hMbound hlr
  have hq23 : (q : ℝ)^2 ≤ (q : ℝ)^3 := by
    nlinarith [sq_nonneg (q : ℝ), mul_nonneg (sq_nonneg (q : ℝ))
      (show 0 ≤ (q : ℝ)-1 by linarith)]
  refine ⟨{
    r := r, s := s, β := β, l := l, B' := B', D' := D'
    divisor_eq := hr
    prime_entry_eq := hs
    alpha_range := ⟨by omega, by omega⟩
    beta_range := ⟨hβpos, hβlt⟩
    residue_eq := hβeq
    shear_eq := hshear
    canonical_eq := canonical_conversion q B' N d D' l β hβeq
    canonical_bottom_eq := canonical_bottom_right q B' N d D' l β hdet' hβeq
    shear_det := hdetM
    canonical_det := ?_
    r_bound := hrr.trans (mul_le_mul_of_nonneg_right hCK hqnonneg)
    s_nonneg := hsnonneg
    s_bound := hsr.trans (mul_le_mul_of_nonneg_right hCK hqnonneg)
    l_bound := hlr.trans (mul_le_mul_of_nonneg_right hAlK hqnonneg)
    shear_height := ?_
    canonical_height := ?_ }⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hdetM]
    simp [lowerUnipotent, upperUnipotent, Matrix.det_fin_two]
  · intro i j
    exact (hMbound i j).trans (mul_le_mul hAK hq23 (sq_nonneg _) (le_of_lt hK))
  · intro i j
    exact (hCbound i j).trans (mul_le_mul_of_nonneg_right hLK (by positivity))

/-- A literal unit-class divisor input supplies all of the divisor
hypotheses needed by the matrix construction, including its strict size
bound. No distribution theorem is involved in this implication. -/
theorem shiftedDivisorClasses_certificate_divisor (Q N c q : ℕ)
    (hQ : 0 < Q) (hN : 0 < N) (hQq : Q < q)
    (hcop : c.Coprime (N*Q)) (hclasses : ShiftedDivisorClasses Q (N*Q) q) :
    ∃ d : ℤ, 0 < d ∧ d < (q : ℤ) ∧ d ∣ (q : ℤ)-(Q : ℤ) ∧
      (N : ℤ)*(Q : ℤ) ∣ d-(c : ℤ) := by
  have hM : 0 < N*Q := Nat.mul_pos hN hQ
  have hcmod : (c%(N*Q)).Coprime (N*Q) := by
    change Nat.gcd (c%(N*Q)) (N*Q) = 1
    rw [← Nat.gcd_rec]
    exact hcop.symm
  obtain ⟨d, hdpos, hddiv, hdmod⟩ :=
    hclasses (c%(N*Q)) (Nat.mod_lt _ hM) hcmod
  have hcmod' : Nat.ModEq (N*Q) (c%(N*Q)) c := by simp [Nat.ModEq]
  have hdmod' : (d : ℤ) ≡ (c : ℤ) [ZMOD (N*Q : ℕ)] :=
    Int.natCast_modEq_iff.mpr (hdmod.trans hcmod')
  have hdiff : (0 : ℤ) < (q : ℤ)-(Q : ℤ) := by omega
  have hdle : (d : ℤ) ≤ (q : ℤ)-(Q : ℤ) := Int.le_of_dvd hdiff hddiv
  refine ⟨d, by exact_mod_cast hdpos, by omega, hddiv, ?_⟩
  simpa using hdmod'.symm.dvd

/-- End-to-end finite arithmetic interface for the density argument.
The positive constant is chosen before q. The only q-dependent arithmetic
input is the explicit shifted-divisor predicate and its residue class mod N.
Both determinant-one matrix identities and all height bounds are supplied
by the returned structure; `inverse_bounds` supplies actual inverse heights. -/
theorem shiftedDivisorClasses_polynomial_certificates (Q N c : ℕ) (B D : ℤ)
    (hQ : 0 < Q) (hN : 0 < N) (hcop : c.Coprime (N*Q))
    (hdet : (Q : ℤ)*D-(N : ℤ)*(c : ℤ)*B = 1)
    {H : ℝ} (hH : 0 ≤ H)
    (hM : MatrixEntryBound (certificateMatrix Q B N c D) H) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, Q < q → 1 < q →
      (N : ℤ) ∣ (q : ℤ)-(Q : ℤ) → ShiftedDivisorClasses Q (N*Q) q →
      ∃ d : ℤ, Nonempty (PolynomialPrimeCertificate Q B N c D d q K) := by
  have hcN : N.Coprime c :=
    (hcop.coprime_dvd_right (dvd_mul_right N Q)).symm
  obtain ⟨x, y, hxy⟩ := hcN.isCoprime
  obtain ⟨K, hK, hcert⟩ := exists_uniform_polynomial_certificates
    Q B N c D x y (by exact_mod_cast hQ) (by exact_mod_cast hN) hdet hxy hH hM
  refine ⟨K, hK, ?_⟩
  intro q hQq hq hNdiv hclasses
  obtain ⟨d, hdpos, hdq, hddiv, hdcong⟩ :=
    shiftedDivisorClasses_certificate_divisor Q N c q hQ hN hQq hcop hclasses
  exact ⟨d, hcert d q hdpos hdq (by exact_mod_cast Nat.le_of_lt hQq)
    (by exact_mod_cast hq) hdcong hNdiv hddiv⟩

#print axioms inverseMatrix2_mul
#print axioms inverseMatrix2_entry_bound
#print axioms canonical_translation_real_bound
#print axioms certificate_canonical_entry_bound
#print axioms PolynomialPrimeCertificate.inverse_bounds
#print axioms exists_uniform_polynomial_certificates
#print axioms shiftedDivisorClasses_certificate_divisor
#print axioms shiftedDivisorClasses_polynomial_certificates

end QuantitativeArithmetic
