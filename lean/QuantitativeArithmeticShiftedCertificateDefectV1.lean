module

public import QuantitativeArithmeticShiftedCertificateBoundsV1
public import Mathlib.Algebra.MonoidAlgebra.Basic

set_option autoImplicit false
@[expose] public noncomputable section

/-!
Exact signed defect telescoping in the integral monoid algebra of the actual
integer matrices. Identities in this algebra apply to every linear right
action; they do not assume modularity or Fricke invariance.
-/

namespace QuantitativeArithmetic

open QuantitativeHolomorphic

abbrev MatrixAlgebra := MonoidAlgebra ℤ IntegerMatrix2

def matrixSymbol (M : IntegerMatrix2) : MatrixAlgebra := MonoidAlgebra.single M 1

@[simp] theorem matrixSymbol_mul (M A : IntegerMatrix2) :
    matrixSymbol (M*A) = matrixSymbol M * matrixSymbol A := by
  simp [matrixSymbol]

@[simp] theorem matrixSymbol_one : matrixSymbol 1 = 1 := rfl

@[simp] theorem lowerUnipotent_zero (N : ℤ) : lowerUnipotent N 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

@[simp] theorem upperUnipotent_zero : upperUnipotent 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent]

theorem lower_symbol_mul (N r s : ℤ) :
    matrixSymbol (lowerUnipotent N r) * matrixSymbol (lowerUnipotent N s) =
      matrixSymbol (lowerUnipotent N (r+s)) := by
  rw [← matrixSymbol_mul, ← lowerUnipotent_add]

/-- Exactly n translates, all with coefficient +1. -/
theorem lower_defect_positive_sum (N : ℤ) (n : ℕ) :
    matrixSymbol (lowerUnipotent N (n : ℤ))-1 =
      ∑ j ∈ Finset.range n, (matrixSymbol (lowerUnipotent N 1)-1) *
        matrixSymbol (lowerUnipotent N (j : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have he := lower_symbol_mul N 1 (n : ℤ)
    have hn : (1 : ℤ)+(n : ℤ) = (n+1 : ℕ) := by omega
    rw [hn] at he
    rw [← he]
    noncomm_ring

/-- Exactly n translates, all with coefficient -1; the exponents run
from -1 down to -n, so their absolute sizes never exceed n. -/
theorem lower_defect_negative_sum (N : ℤ) (n : ℕ) :
    matrixSymbol (lowerUnipotent N (-(n : ℤ)))-1 =
      -(∑ j ∈ Finset.range n, (matrixSymbol (lowerUnipotent N 1)-1) *
        matrixSymbol (lowerUnipotent N (-(j : ℤ)-1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, neg_add, ← ih]
    have he := lower_symbol_mul N 1 (-(n : ℤ)-1)
    have hn : (1 : ℤ)+(-(n : ℤ)-1) = -(n : ℤ) := by ring
    have hn' : -(n : ℤ)-1 = -((n+1 : ℕ) : ℤ) := by push_cast; ring
    rw [hn, hn'] at he
    rw [hn', ← he]
    noncomm_ring

/-- Every partial product in either signed telescope has linear height.
This is the reason the O(q)-term defect expansion does not introduce an
exponential matrix-height bound. -/
theorem lower_defect_partial_heights (N : ℤ) (n j : ℕ) (hj : j < n) :
    MatrixEntryBound (lowerUnipotent N (j : ℤ)) (1+|(N : ℝ)| * (n : ℝ)) ∧
    MatrixEntryBound (lowerUnipotent N (-(j : ℤ)-1)) (1+|(N : ℝ)| * (n : ℝ)) := by
  have hjr : (j : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast hj
  constructor
  · intro i k
    have hb := lowerUnipotent_entry_bound N (j : ℤ) i k
    simp only [Int.cast_natCast, Nat.abs_cast] at hb
    exact hb.trans (by gcongr)
  · intro i k
    have hb := lowerUnipotent_entry_bound N (-(j : ℤ)-1) i k
    have he : |((-(j : ℤ)-1 : ℤ) : ℝ)| = (j : ℝ)+1 := by
      push_cast
      rw [abs_of_nonpos (by have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)]
      ring
    rw [he] at hb
    exact hb.trans (by gcongr)

/-- A single signed expansion covering every integer exponent. It has
exactly |r| terms, coefficients of absolute value one, and no intermediate
exponent larger than |r|. -/
theorem lower_defect_signed_sum (N r : ℤ) :
    ∃ (n : ℕ) (ε : ℤ) (e : ℕ → ℤ), n = r.natAbs ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ j < n, |e j| ≤ |r|) ∧
      matrixSymbol (lowerUnipotent N r)-1 =
        ε • (∑ j ∈ Finset.range n, (matrixSymbol (lowerUnipotent N 1)-1)*
          matrixSymbol (lowerUnipotent N (e j))) := by
  obtain ⟨n, rfl | rfl⟩ := r.eq_nat_or_neg
  · refine ⟨n, 1, fun j => (j : ℤ), by simp, Or.inl rfl, ?_, ?_⟩
    · intro j hj
      simpa using (show (j : ℤ) ≤ (n : ℤ) by omega)
    · simpa using lower_defect_positive_sum N n
  · refine ⟨n, -1, fun j => -(j : ℤ)-1, by simp, Or.inr rfl, ?_, ?_⟩
    · intro j hj
      have hn : |(-(n : ℤ))| = (n : ℤ) := by simp
      rw [hn, abs_of_nonpos (by omega : -(j : ℤ)-1 ≤ 0)]
      omega
    · simpa using lower_defect_negative_sum N n

theorem upperUnipotent_inverse (l : ℤ) :
    upperUnipotent l * upperUnipotent (-l) = 1 := by
  rw [← upperUnipotent_add]
  simp

/-- Recover the fixed matrix from the canonical certificate without any
matrix inverse notation or projective ambiguity. -/
theorem PolynomialPrimeCertificate.matrix_recovery {Q B N c D d q : ℤ} {K : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K) :
    let H := certificateMatrix Q B N c D
    let C := lowerUnipotent N (-1) * certificateMatrix q cert.B' N d cert.D' *
      upperUnipotent cert.l
    upperUnipotent cert.s * lowerUnipotent N cert.r * H =
      lowerUnipotent N 1 * C * upperUnipotent (-cert.l) := by
  dsimp
  rw [cert.shear_eq]
  simp only [mul_assoc]
  rw [upperUnipotent_inverse, mul_one]
  rw [← mul_assoc (lowerUnipotent N 1), lowerUnipotent_inverse, one_mul]

theorem formal_certificate_algebra {R : Type*} [Ring R] (T V P H C U : R)
    (he : T*P*H = V*C*U) :
    H-1 = (V-1)*C*U+(C-1)*U-(P-1)*H+(U-1)-(T-1)*P*H := by
  calc
    H-1 = H-1+(V*C*U-T*P*H) := by rw [he, sub_self, add_zero]
    _ = _ := by noncomm_ring

/-- The exact certificate identity including the two periodicity terms.
After evaluation on a T-periodic section those two terms vanish; the only
remaining variable-length part is `lower_defect_positive_sum` or its
negative counterpart above. -/
theorem PolynomialPrimeCertificate.formal_defect_recovery
    {Q B N c D d q : ℤ} {K : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K) :
    let H := certificateMatrix Q B N c D
    let C := lowerUnipotent N (-1) * certificateMatrix q cert.B' N d cert.D' *
      upperUnipotent cert.l
    matrixSymbol H-1 =
      (matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol C*
        matrixSymbol (upperUnipotent (-cert.l)) +
      (matrixSymbol C-1)*matrixSymbol (upperUnipotent (-cert.l)) -
      (matrixSymbol (lowerUnipotent N cert.r)-1)*matrixSymbol H +
      (matrixSymbol (upperUnipotent (-cert.l))-1) -
      (matrixSymbol (upperUnipotent cert.s)-1)*
        matrixSymbol (lowerUnipotent N cert.r)*matrixSymbol H := by
  dsimp
  have he := congrArg matrixSymbol cert.matrix_recovery
  simp only [matrixSymbol_mul] at he
  apply formal_certificate_algebra
  simpa only [matrixSymbol_mul] using he

/-- Evaluation on any periodic linear section removes exactly the two
translation terms from the formal identity. The hypothesis says only
T-periodicity, not invariance under V or any congruence generator. -/
theorem PolynomialPrimeCertificate.periodic_defect_recovery
    {Q B N c D d q : ℤ} {K : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K)
    {A : Type*} [AddCommGroup A] (F : MatrixAlgebra →+ A)
    (hperiod : ∀ (j : ℤ) (M : IntegerMatrix2),
      F (matrixSymbol (upperUnipotent j)*matrixSymbol M) = F (matrixSymbol M)) :
    let H := certificateMatrix Q B N c D
    let C := lowerUnipotent N (-1) * certificateMatrix q cert.B' N d cert.D' *
      upperUnipotent cert.l
    F (matrixSymbol H)-F 1 =
      F ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol C*
        matrixSymbol (upperUnipotent (-cert.l))) +
      F ((matrixSymbol C-1)*matrixSymbol (upperUnipotent (-cert.l))) -
      F ((matrixSymbol (lowerUnipotent N cert.r)-1)*matrixSymbol H) := by
  let H := certificateMatrix Q B N c D
  have hpU : F (matrixSymbol (upperUnipotent (-cert.l))-1) = 0 := by
    rw [map_sub, sub_eq_zero]
    simpa using hperiod (-cert.l) 1
  have hpT : F ((matrixSymbol (upperUnipotent cert.s)-1)*
      matrixSymbol (lowerUnipotent N cert.r)*matrixSymbol H) = 0 := by
    rw [sub_mul, sub_mul, one_mul, map_sub, sub_eq_zero]
    simpa only [matrixSymbol_mul, mul_assoc] using
      hperiod cert.s (lowerUnipotent N cert.r*H)
  have he := congrArg F cert.formal_defect_recovery
  dsimp [H] at hpT
  simpa only [map_sub, map_add, hpU, hpT, sub_zero, add_zero] using he

/-- Evaluation of the signed finite telescope, with its literal
translating matrices. The number of terms remains |r| after evaluation. -/
theorem lower_defect_evaluated_sum (N r : ℤ) (H : IntegerMatrix2)
    {A : Type*} [AddCommGroup A] (F : MatrixAlgebra →+ A) :
    ∃ (n : ℕ) (ε : ℤ) (e : ℕ → ℤ), n = r.natAbs ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ j < n, |e j| ≤ |r|) ∧
      F ((matrixSymbol (lowerUnipotent N r)-1)*matrixSymbol H) =
        ε • (∑ j ∈ Finset.range n, F ((matrixSymbol (lowerUnipotent N 1)-1)*
          matrixSymbol (lowerUnipotent N (e j)*H))) := by
  obtain ⟨n, ε, e, hn, hε, he, hid⟩ := lower_defect_signed_sum N r
  refine ⟨n, ε, e, hn, hε, he, ?_⟩
  rw [hid]
  simp only [smul_mul_assoc, Finset.sum_mul, map_zsmul, map_sum,
    matrixSymbol_mul, mul_assoc]

/-- Polynomial height for the actual translations in the long telescope.
The bound is linear in q although the number of summands can also be linear
in q. -/
theorem telescope_translation_height (N e : ℤ) (M : IntegerMatrix2)
    {K q H : ℝ} (hK : 0 ≤ K) (hq : 1 ≤ q)
    (hM : MatrixEntryBound M H) (he : |(e : ℝ)| ≤ K*q) :
    MatrixEntryBound (lowerUnipotent N e*M)
      (2*(1+|(N : ℝ)| * K)*H*q) := by
  have hlower : MatrixEntryBound (lowerUnipotent N e) ((1+|(N : ℝ)| * K)*q) := by
    intro i j
    have hh := lowerUnipotent_entry_bound N e i j
    apply hh.trans
    nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (N : ℝ))]
  have hh := matrix_entry_bound_mul (by positivity) hlower hM
  convert hh using 1
  ring

/-- Evaluated fixed-matrix defect with an explicit signed O(q)-term
expansion and a linear bound for every matrix in its variable-length part.
The two remaining terms use the canonical matrix and fixed V-defect.
Its canonical and inverse heights are supplied by the certificate itself. -/
theorem PolynomialPrimeCertificate.periodic_polynomial_expansion
    {Q B N c D d q : ℤ} {K H₀ : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K)
    (hK : 0 ≤ K) (hq : 1 ≤ q)
    (hH : MatrixEntryBound (certificateMatrix Q B N c D) H₀)
    {A : Type*} [AddCommGroup A] (F : MatrixAlgebra →+ A)
    (hperiod : ∀ (j : ℤ) (M : IntegerMatrix2),
      F (matrixSymbol (upperUnipotent j)*matrixSymbol M) = F (matrixSymbol M)) :
    let H := certificateMatrix Q B N c D
    let C := lowerUnipotent N (-1) * certificateMatrix q cert.B' N d cert.D' *
      upperUnipotent cert.l
    ∃ (n : ℕ) (ε : ℤ) (e : ℕ → ℤ), (n : ℝ) ≤ K*(q : ℝ) ∧
      (ε = 1 ∨ ε = -1) ∧
      (∀ j < n, MatrixEntryBound (lowerUnipotent N (e j)*H)
        (2*(1+|(N : ℝ)| * K)*H₀*(q : ℝ))) ∧
      F (matrixSymbol H)-F 1 =
        F ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol C*
          matrixSymbol (upperUnipotent (-cert.l))) +
        F ((matrixSymbol C-1)*matrixSymbol (upperUnipotent (-cert.l))) -
        ε • (∑ j ∈ Finset.range n, F ((matrixSymbol (lowerUnipotent N 1)-1)*
          matrixSymbol (lowerUnipotent N (e j)*H))) := by
  obtain ⟨n, ε, e, hn, hε, he, hid⟩ :=
    lower_defect_evaluated_sum N cert.r (certificateMatrix Q B N c D) F
  refine ⟨n, ε, e, ?_, hε, ?_, ?_⟩
  · rw [hn]
    simpa using cert.r_bound
  · intro j hj
    have hej : |(e j : ℝ)| ≤ |(cert.r : ℝ)| := by exact_mod_cast he j hj
    exact telescope_translation_height N (e j) _ hK
      (by exact_mod_cast hq) hH (hej.trans cert.r_bound)
  · rw [← hid]
    exact cert.periodic_defect_recovery F hperiod

def integralFrickeMatrix (N : ℤ) : IntegerMatrix2 := !![0, -1; N, 0]

theorem fricke_translation_fricke (N : ℤ) :
    integralFrickeMatrix N * upperUnipotent (-1) * integralFrickeMatrix N =
      (-N) • lowerUnipotent N 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralFrickeMatrix, upperUnipotent, lowerUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The Fricke residual evaluated after a literal matrix translation. -/
def frickeResidual {A : Type*} [AddCommGroup A] (F : MatrixAlgebra →+ A)
    (N w : ℤ) (M : IntegerMatrix2) : A :=
  F (matrixSymbol (integralFrickeMatrix N)*matrixSymbol M)-w • F (matrixSymbol M)

/-- The elementary lower-unipotent residual is exactly two translates of
the Fricke residual. Periodicity and the usual even-weight projective scalar
law are the only hypotheses; no Fricke equation is assumed. -/
theorem lower_defect_of_fricke {A : Type*} [AddCommGroup A]
    (F : MatrixAlgebra →+ A) (N w : ℤ) (hw : w = 1 ∨ w = -1)
    (hperiod : ∀ (j : ℤ) (M : IntegerMatrix2),
      F (matrixSymbol (upperUnipotent j)*matrixSymbol M) = F (matrixSymbol M))
    (hscale : ∀ M : IntegerMatrix2, F (matrixSymbol ((-N) • M)) = F (matrixSymbol M))
    (M : IntegerMatrix2) :
    F ((matrixSymbol (lowerUnipotent N 1)-1)*matrixSymbol M) =
      frickeResidual F N w (upperUnipotent (-1)*integralFrickeMatrix N*M) +
      w • frickeResidual F N w M := by
  have hmat : integralFrickeMatrix N *
      (upperUnipotent (-1)*integralFrickeMatrix N*M) =
      (-N) • (lowerUnipotent N 1*M) := by
    rw [← mul_assoc, ← mul_assoc, fricke_translation_fricke, smul_mul_assoc]
  have hfirst : F (matrixSymbol (integralFrickeMatrix N)*
      matrixSymbol (upperUnipotent (-1)*integralFrickeMatrix N*M)) =
      F (matrixSymbol (lowerUnipotent N 1)*matrixSymbol M) := by
    rw [← matrixSymbol_mul, hmat, hscale, matrixSymbol_mul]
  have hsecond : F (matrixSymbol (upperUnipotent (-1)*integralFrickeMatrix N*M)) =
      F (matrixSymbol (integralFrickeMatrix N)*matrixSymbol M) := by
    simpa only [matrixSymbol_mul, mul_assoc] using
      hperiod (-1) (integralFrickeMatrix N*M)
  simp only [frickeResidual, hfirst, hsecond, sub_mul, one_mul, map_sub]
  rcases hw with rfl | rfl <;> simp
  abel

/-- The extra Fricke translate has a fixed-height prefix, hence preserves
polynomial height for every term in the signed telescope. -/
theorem fricke_translate_height (N : ℤ) (M : IntegerMatrix2) {H : ℝ}
    (hM : MatrixEntryBound M H) :
    MatrixEntryBound (upperUnipotent (-1)*integralFrickeMatrix N*M)
      (2*(1+|(N : ℝ)|)*H) := by
  have hprefix : MatrixEntryBound (upperUnipotent (-1)*integralFrickeMatrix N)
      (1+|(N : ℝ)|) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent, integralFrickeMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals positivity
  exact matrix_entry_bound_mul (by positivity) hprefix hM

#print axioms lower_defect_positive_sum
#print axioms lower_defect_negative_sum
#print axioms lower_defect_partial_heights
#print axioms lower_defect_signed_sum
#print axioms PolynomialPrimeCertificate.matrix_recovery
#print axioms PolynomialPrimeCertificate.formal_defect_recovery
#print axioms PolynomialPrimeCertificate.periodic_defect_recovery
#print axioms lower_defect_evaluated_sum
#print axioms telescope_translation_height
#print axioms PolynomialPrimeCertificate.periodic_polynomial_expansion
#print axioms fricke_translation_fricke
#print axioms lower_defect_of_fricke
#print axioms fricke_translate_height

end QuantitativeArithmetic
