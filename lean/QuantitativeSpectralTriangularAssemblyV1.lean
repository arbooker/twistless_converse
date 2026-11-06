module

public import QuantitativeSpectralBlockTriangularV1
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralTriangularAssembly

variable {A : Type*} [CStarAlgebra A] {n : ℕ}
  (Q : Fin n → A) (hid : ∀ i, Q i*Q i = Q i)
  (horth : ∀ i j, i ≠ j → Q i*Q j = 0)

/-- The actual block diagonal operator with prescribed scalar weights. -/
def diagonal (d : Fin n → ℝ) : A := ∑ i, d i • Q i

include hid horth in
theorem mul_diagonal (d : Fin n → ℝ) (i : Fin n) :
    Q i * diagonal Q d = d i • Q i := by
  classical
  unfold diagonal
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [mul_smul_comm, hid]
  · intro j _ hji
    rw [mul_smul_comm, horth i j hji.symm, smul_zero]
  · simp

include hid horth in
theorem diagonal_mul (d : Fin n → ℝ) (i : Fin n) :
    diagonal Q d * Q i = d i • Q i := by
  classical
  unfold diagonal
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, hid]
  · intro j _ hji
    rw [smul_mul_assoc, horth j i hji, smul_zero]
  · simp

include hid horth in
theorem diagonal_product (d e : Fin n → ℝ) :
    diagonal Q d * diagonal Q e = diagonal Q (fun i => d i*e i) := by
  change (∑ i, d i • Q i) * diagonal Q e = _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_assoc, mul_diagonal Q hid horth, smul_smul]

include hid horth in
theorem diagonal_inverse (hQ : ∑ i, Q i = 1) (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    diagonal Q (fun i => (d i)⁻¹) * diagonal Q d = 1 ∧
      diagonal Q d * diagonal Q (fun i => (d i)⁻¹) = 1 := by
  constructor
  · rw [diagonal_product Q hid horth]
    simpa [diagonal, hd] using hQ
  · rw [diagonal_product Q hid horth]
    simpa [diagonal, hd] using hQ

include hid horth in
theorem diagonal_isUnit (hQ : ∑ i, Q i = 1) (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    IsUnit (diagonal Q d) := by
  have he := diagonal_inverse Q hid horth hQ d hd
  exact isUnit_iff_exists.mpr ⟨diagonal Q (fun i => (d i)⁻¹),he.2,he.1⟩

variable (C : Fin n → A) (hleft : ∀ i, Q i*C i = C i)

include horth hleft in
theorem row_block (i : Fin n) : Q i*(∑ j, C j) = C i := by
  classical
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact hleft i
  · intro j _ hji
    calc
      Q i*C j = Q i*(Q j*C j) := by rw [hleft]
      _ = 0 := by rw [← mul_assoc, horth i j hji.symm, zero_mul]
  · simp

/-- The normalized strict triangular part is constructed from the rows,
rather than assumed to exist. -/
def normalizedStrict (d : Fin n → ℝ) : A :=
  diagonal Q (fun i => (d i)⁻¹) * (∑ i, C i) - 1

include hid horth hleft in
theorem normalizedStrict_below (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (hdiag : ∀ i, C i*Q i = d i • Q i)
    (hupper : ∀ i j, i < j → C i*Q j = 0) :
    QuantitativeSpectralBlockTriangular.Below Q (normalizedStrict Q C d) 1 := by
  intro i j hij
  have hij' : i ≤ j := by simpa using Nat.le_of_lt_succ hij
  unfold normalizedStrict
  rw [mul_sub, sub_mul, mul_one]
  rw [← mul_assoc (Q i) (diagonal Q (fun i => (d i)⁻¹)) (∑ i, C i),
    mul_diagonal Q hid horth, smul_mul_assoc, row_block Q horth C hleft,
    smul_mul_assoc]
  by_cases he : i = j
  · subst j
    rw [hdiag, smul_smul, inv_mul_cancel₀ (hd i), one_smul, hid, sub_self]
  · rw [hupper i j (lt_of_le_of_ne hij' he), smul_zero, horth i j he, sub_self]

include hid horth in
theorem diagonal_factor (hQ : ∑ i, Q i = 1) (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    diagonal Q d * (1+normalizedStrict Q C d) = ∑ i, C i := by
  unfold normalizedStrict
  rw [← add_sub_assoc, add_sub_cancel_left, ← mul_assoc, (diagonal_inverse Q hid horth hQ d hd).2, one_mul]

include horth hleft in
theorem cross_gram_zero (hself : ∀ i, IsSelfAdjoint (Q i)) (i j : Fin n) (hij : i ≠ j) :
    star (C i)*C j = 0 := by
  have hl : star (C i)*Q i = star (C i) := by
    simpa only [star_mul, (hself i).star_eq] using congrArg star (hleft i)
  calc
    star (C i)*C j = (star (C i)*Q i)*(Q j*C j) := by rw [hl, hleft]
    _ = 0 := by rw [mul_assoc, ← mul_assoc (Q i), horth i j hij]; simp

include horth hleft in
/-- Mutually orthogonal output blocks eliminate every cross term in the
Gram operator of the assembled residual rows. -/
theorem row_sum_gram (hself : ∀ i, IsSelfAdjoint (Q i)) :
    star (∑ i, C i)*(∑ i, C i) = ∑ i, star (C i)*C i := by
  classical
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · intro j _ hji
    exact cross_gram_zero Q horth C hleft hself i j hji.symm
  · simp

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- Left multiplication by a contraction decreases the actual Gram
operator. This is the domination used by the normalized cut rows. -/
theorem contraction_gram (W B : A) (hW : ‖W‖ ≤ 1) :
    star (W*B)*(W*B) ≤ star B*B := by
  have hg : star W*W ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg W)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg W]
  simpa only [star_mul, mul_assoc, one_mul] using star_left_conjugate_le_conjugate hg B

include horth hleft in
theorem row_sum_gram_le (hself : ∀ i, IsSelfAdjoint (Q i)) (B : Fin n → A)
    (hgram : ∀ i, star (C i)*C i ≤ star (B i)*B i) :
    star (∑ i, C i)*(∑ i, C i) ≤ ∑ i, star (B i)*B i := by
  rw [row_sum_gram Q horth C hleft hself]
  exact Finset.sum_le_sum (fun i _ => hgram i)

end Ordered

#print axioms diagonal_isUnit
#print axioms normalizedStrict_below
#print axioms diagonal_factor
#print axioms row_sum_gram
#print axioms contraction_gram
#print axioms row_sum_gram_le

end QuantitativeSpectralTriangularAssembly
