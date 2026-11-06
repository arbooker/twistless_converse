module

public import QuantitativeEulerEndpointInverseRegionV1
public import QuantitativeEulerEndpointAveragedV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDiamondPolynomial
open AsymptoticIntegralSubgroup AsymptoticFreshAveraging
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- The correction polynomial is an explicit positive triangular sum. -/
theorem prime_correction_expansion (q : ℕ) :
    Polynomial.aeval (primeX q) (correctionPolynomial q)=
      ((q : ℂ)-1)⁻¹ • (∑ j∈Finset.range q, ∑ i∈Finset.range j, (primeX q)^i) := by
  simp only [correctionPolynomial,map_mul,Polynomial.aeval_C,triangular,geometric,
    map_sum,map_pow,Polynomial.aeval_X,Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc,one_mul]
  rw [←Rat.cast_smul_eq_qsmul ℂ]
  simp only [Rat.cast_inv,Rat.cast_sub,Rat.cast_natCast,Rat.cast_one]

private theorem sum_natCast_range (q : ℕ) :
    (∑ j∈Finset.range q, (j : ℝ))=(q : ℝ)*((q : ℝ)-1)/2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

theorem correction_scalar_mass (q : ℕ) (hq : 2≤q) :
    ‖((q : ℂ)-1)⁻¹‖*(∑ j∈Finset.range q, (j : ℝ))=(q : ℝ)/2 := by
  have hq' : (2 : ℝ)≤q := by exact_mod_cast hq
  have hd : 0<(q : ℝ)-1 := by linarith
  have hn : ‖(q : ℂ)-1‖=(q : ℝ)-1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  rw [norm_inv,hn,sum_natCast_range]
  field_simp

theorem compact_prime_power_union_bound (q i : ℕ) (hi : i<q) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*(primeX q)^i) v‖≤
      ‖compactAction (inverseRegion_compact q hs) hε t x A v‖ := by
  have he := congrArg (fun B : Ring => ‖compactAction hs hε t x (A*B) v‖)
    (prime_power_translation q i)
  apply he.trans_le
  apply (compact_right_translation_norm ((i : ℚ)/q) A hs hε t x v).trans
  apply compactAction_restrict_norm A _ (inverseRegion_compact q hs) _ hε t x v
  exact Set.Subset.trans (Set.subset_iUnion_of_subset ⟨i,hi⟩ (Set.Subset.refl _))
    Set.subset_union_right

theorem triangular_vector_bound (q : ℕ) (c : ℂ) (u : ℕ → Space)
    {D : ℝ} (hu : ∀ i<q, ‖u i‖≤D) :
    ‖c • (∑ j∈Finset.range q, ∑ i∈Finset.range j, u i)‖≤
      (‖c‖*(∑ j∈Finset.range q, (j : ℝ)))*D := by
  have hs : ‖∑ j∈Finset.range q, ∑ i∈Finset.range j, u i‖≤
      (∑ j∈Finset.range q, (j : ℝ))*D := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i∈Finset.range j, D := Finset.sum_le_sum (fun i hi =>
        hu i (lt_trans (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)))
      _ = _ := by simp
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left hs (norm_nonneg c)).trans_eq (mul_assoc _ _ _).symm

/-- The actual period-correction multiplier costs q/2, on the same compact
union as the inverse. The bound is uniform in epsilon and the cap exponent. -/
theorem compact_prime_correction_bound (q : ℕ) (hq : 2≤q) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x
      (A*Polynomial.aeval (primeX q) (correctionPolynomial q)) v‖≤
      ((q : ℝ)/2)*‖compactAction (inverseRegion_compact q hs) hε t x A v‖ := by
  have he : compactAction hs hε t x
      (A*Polynomial.aeval (primeX q) (correctionPolynomial q)) v=
      ((q : ℂ)-1)⁻¹ • (∑ j∈Finset.range q, ∑ i∈Finset.range j,
        compactAction hs hε t x (A*(primeX q)^i) v) := by
    rw [prime_correction_expansion]
    simp only [mul_smul_comm,Finset.mul_sum,map_smul,map_sum,_root_.smul_apply,_root_.sum_apply]
  have h := triangular_vector_bound q ((q : ℂ)-1)⁻¹
    (fun i => compactAction hs hε t x (A*(primeX q)^i) v)
    (fun i hi => compact_prime_power_union_bound q i hi A hs hε t x v)
  rw [correction_scalar_mass q hq] at h
  exact (congrArg norm he).trans_le h

theorem difference_multiplier_inverse_bound (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j i : Fin (q-1)) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*differenceMultiplier N q hN hq j i) v‖≤
      3*‖compactAction (inverseRegion_compact q hs) hε t x
        ((A*symbol (defectLabel N q hN hq j))*symbol (primeLabels q i)) v‖ := by
  have he : A*differenceMultiplier N q hN hq j i=
      ((A*symbol (defectLabel N q hN hq j))*symbol (primeLabels q i))*primeInverse q := by
    simp only [differenceMultiplier,mul_assoc]
  exact (congrArg (fun B : Ring => ‖compactAction hs hε t x B v‖) he).trans_le
    (compact_prime_inverse_bound q (Fact.out : q.Prime).two_le _ hs hε t x v)

theorem period_multiplier_correction_bound (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*periodMultiplier N q hN hq j) v‖≤
      ((q : ℝ)/2)*‖compactAction (inverseRegion_compact q hs) hε t x
        (A*symbol (defectLabel N q hN hq j)) v‖ := by
  have he : A*periodMultiplier N q hN hq j=
      (A*symbol (defectLabel N q hN hq j))*Polynomial.aeval (primeX q) (correctionPolynomial q) := by
    simp only [periodMultiplier,mul_assoc]
  exact (congrArg (fun B : Ring => ‖compactAction hs hε t x B v‖) he).trans_le
    (compact_prime_correction_bound q (Fact.out : q.Prime).two_le _ hs hε t x v)

#print axioms prime_correction_expansion
#print axioms correction_scalar_mass
#print axioms triangular_vector_bound
#print axioms compact_prime_correction_bound
#print axioms difference_multiplier_inverse_bound
#print axioms period_multiplier_correction_bound
end QuantitativeEulerEndpointPrepared
