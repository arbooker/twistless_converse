module

public import QuantitativeSpectralTriangularLogV1
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

open Finset

namespace QuantitativeSpectralBlockTriangular

variable {R : Type*} [Ring R] {n : ℕ} (P : Fin n → R)

/-- A finite block operator has no entries less than `k` blocks below its
diagonal. This definition uses actual products of the block idempotents. -/
def Below (A : R) (k : ℕ) : Prop :=
  ∀ i j : Fin n, i.val < j.val+k → P i*A*P j = 0

/-- Multiplication adds strict triangular depth. -/
theorem below_mul (hP : ∑ i, P i = 1) {A B : R} {k l : ℕ}
    (hA : Below P A k) (hB : Below P B l) : Below P (A*B) (k+l) := by
  intro i j hij
  have he : P i*(A*B)*P j = ∑ m, P i*A*P m*B*P j := by
    calc
      P i*(A*B)*P j = P i*A*(∑ m, P m)*B*P j := by rw [hP]; simp [mul_assoc]
      _ = ∑ m, P i*A*P m*B*P j := by simp only [mul_sum, sum_mul]
  rw [he]
  apply sum_eq_zero
  intro m _
  by_cases hm : i.val < m.val+k
  · rw [hA i m hm, zero_mul, zero_mul]
  · have hm' : m.val < j.val+l := by omega
    rw [mul_assoc (P i*A) (P m) B, mul_assoc (P i*A) (P m*B) (P j), hB m j hm', mul_zero]

/-- Powers of a strict triangular operator move farther below the diagonal. -/
theorem below_pow (hP : ∑ i, P i = 1) {V : R} (hV : Below P V 1)
    (k : ℕ) : Below P (V^(k+1)) (k+1) := by
  induction k with
  | zero => simpa using hV
  | succ k ih =>
    simpa only [pow_succ, Nat.add_assoc] using below_mul P hP ih hV

/-- A zero block matrix is the zero operator. -/
theorem eq_zero_of_blocks (hP : ∑ i, P i = 1) {V : R}
    (hV : ∀ i j, P i*V*P j = 0) : V = 0 := by
  calc
    V = (∑ i, P i)*V*(∑ j, P j) := by rw [hP]; simp
    _ = ∑ i, ∑ j, P i*V*P j := by
      simp only [sum_mul, mul_sum]
      rw [sum_comm]
    _ = 0 := by simp [hV]

/-- Every strictly triangular finite block operator is nilpotent. -/
theorem pow_eq_zero (hP : ∑ i, P i = 1) {V : R} (hV : Below P V 1) :
    V^(n+1) = 0 := by
  apply eq_zero_of_blocks P hP
  intro i j
  exact below_pow P hP hV n i j (by omega)

/-- Cyclic trace is the sum of its diagonal block traces. In particular,
an operator with vanishing diagonal blocks has zero trace. -/
theorem trace_eq_zero (hP : ∑ i, P i = 1) (hid : ∀ i, P i*P i = P i)
    {V : R} (hV : ∀ i, P i*V*P i = 0)
    (τ : R →+ ℝ) (hcyc : ∀ A B, τ (A*B) = τ (B*A)) : τ V = 0 := by
  have hd (i : Fin n) : τ (P i*V) = 0 := by
    calc
      τ (P i*V) = τ (P i*P i*V) := by rw [hid i]
      _ = τ (P i*(P i*V)) := by rw [mul_assoc]
      _ = τ (P i*V*P i) := hcyc _ _
      _ = 0 := by rw [hV i, map_zero]
  calc
    τ V = τ ((∑ i, P i)*V) := by rw [hP, one_mul]
    _ = ∑ i, τ (P i*V) := by rw [sum_mul, map_sum]
    _ = 0 := by simp [hd]

/-- Every positive power of a strictly triangular block operator has zero
cyclic trace. -/
theorem trace_pow_zero (hP : ∑ i, P i = 1) (hid : ∀ i, P i*P i = P i)
    {V : R} (hV : Below P V 1) (τ : R →+ ℝ)
    (hcyc : ∀ A B, τ (A*B) = τ (B*A)) {k : ℕ} (hk : 0 < k) : τ (V^k) = 0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  apply trace_eq_zero P hP hid ?_ τ hcyc
  intro i
  exact below_pow P hP hV j i i (by omega)

section CStar

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

/-- Exact finite-block triangular trace-log identity. Both nilpotence and
vanishing power traces are derived from the actual block products. -/
theorem trace_log_block_unipotent (Q : Fin n → 𝔄) (hQ : ∑ i, Q i = 1)
    (hid : ∀ i, Q i*Q i = Q i) {V : 𝔄} (hV : Below Q V 1)
    (τ : 𝔄 →L[ℝ] ℝ) (hcyc : ∀ A B, τ (A*B) = τ (B*A))
    (hstar : ∀ A, τ (star A) = τ A) (t : ℝ) :
    τ (CFC.log (star (1+t • V)*(1+t • V))) = 0 := by
  apply QuantitativeSpectralTriangularLog.trace_log_unipotent_gram V
    (pow_eq_zero Q hQ hV) τ hcyc hstar ?_ t
  intro k hk
  exact trace_pow_zero Q hQ hid hV τ.toLinearMap.toAddMonoidHom hcyc hk

/-- Exact diagonal-factor version of the finite triangular trace-log
identity. This is the congruence identity used by collective deflation. -/
theorem trace_log_block_congruence (Q : Fin n → 𝔄) (hQ : ∑ i, Q i = 1)
    (hid : ∀ i, Q i*Q i = Q i) {V : 𝔄} (hV : Below Q V 1)
    (B : 𝔄) (hB : IsUnit B) (τ : 𝔄 →L[ℝ] ℝ)
    (hcyc : ∀ A B, τ (A*B) = τ (B*A)) (hstar : ∀ A, τ (star A) = τ A) (t : ℝ) :
    τ (CFC.log (star (B*(1+t • V))*(B*(1+t • V)))) =
      τ (CFC.log (star B*B)) := by
  apply QuantitativeSpectralTriangularLog.trace_log_unipotent_congruence B V hB
    (pow_eq_zero Q hQ hV) τ hcyc hstar ?_ t
  intro k hk
  exact trace_pow_zero Q hQ hid hV τ.toLinearMap.toAddMonoidHom hcyc hk

end CStar

#print axioms below_mul
#print axioms trace_eq_zero
#print axioms trace_pow_zero
#print axioms trace_log_block_unipotent
#print axioms trace_log_block_congruence
#print axioms below_pow
#print axioms eq_zero_of_blocks
#print axioms pow_eq_zero

end QuantitativeSpectralBlockTriangular
