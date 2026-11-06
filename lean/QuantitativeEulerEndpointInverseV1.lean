module

public import QuantitativeEulerEndpointTranslationV1

set_option autoImplicit false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDiamondPolynomial
open AsymptoticIntegralSubgroup Polynomial
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

theorem inverse_polynomial_geometric (q : ℕ) (hq : 2≤q) :
    inversePolynomial q=Polynomial.C ((q : ℚ)-1)⁻¹*geometric q-1 := by
  have hd : (q : ℚ)-1≠0 := by
    have h : (2 : ℚ)≤q := by exact_mod_cast hq
    linarith
  have hc : Polynomial.C ((q : ℚ)-1)⁻¹*Polynomial.C ((q : ℚ)-1)=(1 : ℚ[X]) := by
    rw [←map_mul,inv_mul_cancel₀ hd,map_one]
  have he : kernel q-Polynomial.C ((q : ℚ)-2)=geometric q-Polynomial.C ((q : ℚ)-1) := by
    simp only [kernel,map_sub,map_ofNat,map_one]
    ring
  rw [inversePolynomial,he,mul_sub,hc]

theorem prime_inverse_expansion (q : ℕ) (hq : 2≤q) :
    primeInverse q=((q : ℂ)-1)⁻¹ • (∑ j∈Finset.range q, (primeX q)^j)-1 := by
  rw [primeInverse,inverse_polynomial_geometric q hq]
  simp only [map_sub,map_mul,map_one,Polynomial.aeval_C,geometric,map_sum,map_pow,
    Polynomial.aeval_X,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
  rw [←Rat.cast_smul_eq_qsmul ℂ]
  simp only [Rat.cast_inv,Rat.cast_sub,Rat.cast_natCast,Rat.cast_one]

theorem prime_power_translation (q j : ℕ) :
    (primeX q)^j=symbol (translationLabel ((j : ℚ)/q)) := by
  rw [primeX,←map_pow,translationLabel_pow]
  congr 2

/-- One explicit compact observation set for the whole finite inverse. -/
def inverseRegion (q : ℕ) (s : Set ℍ) : Set ℍ :=
  s ∪ ⋃ j : Fin q, branchImage (symbolBranch (translationLabel ((j.val : ℚ)/q))) s

theorem inverseRegion_compact (q : ℕ) {s : Set ℍ} (hs : IsCompact s) :
    IsCompact (inverseRegion q s) :=
  hs.union (isCompact_iUnion (fun j => branchImage_compact
    (symbolBranch (translationLabel ((j.val : ℚ)/q))) hs))

theorem inverse_scalar_cost (q : ℕ) (hq : 2≤q) :
    ‖((q : ℂ)-1)⁻¹‖*(q : ℝ)≤2 := by
  have hq' : (2 : ℝ)≤q := by exact_mod_cast hq
  have hd : 0<(q : ℝ)-1 := by linarith
  have hn : ‖(q : ℂ)-1‖=(q : ℝ)-1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  rw [norm_inv,hn,inv_mul_eq_div]
  exact (div_le_iff₀ hd).2 (by linarith)

private theorem finite_inverse_vector_bound (q : ℕ) (c : ℂ) (u : ℕ → Space)
    (v : Space) {D : ℝ} (hD : 0≤D) (hv : ‖v‖≤D)
    (hu : ∀ j∈Finset.range q, ‖u j‖≤D) (hc : ‖c‖*(q : ℝ)≤2) :
    ‖c • (∑ j∈Finset.range q, u j)-v‖≤3*D := by
  have hs : ‖∑ j∈Finset.range q, u j‖≤(q : ℝ)*D := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j∈Finset.range q, D := Finset.sum_le_sum hu
      _ = _ := by simp
  calc
    _ ≤ ‖c • (∑ j∈Finset.range q, u j)‖+‖v‖ := norm_sub_le _ _
    _ = ‖c‖*‖∑ j∈Finset.range q, u j‖+‖v‖ := by rw [norm_smul]
    _ ≤ ‖c‖*((q : ℝ)*D)+D := add_le_add (mul_le_mul_of_nonneg_left hs (norm_nonneg c)) hv
    _ = (‖c‖*(q : ℝ))*D+D := by ring
    _ ≤ 2*D+D := add_le_add (mul_le_mul_of_nonneg_right hc hD) le_rfl
    _ = 3*D := by ring

/-- The actual finite diamond inverse costs at most three, uniformly in q,
epsilon, the exponent and the original compact region. The right-hand
operator is observed on the explicitly displayed union of translated sets. -/
theorem compact_prime_inverse_bound (q : ℕ) (hq : 2≤q) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*primeInverse q) v‖≤
      3*‖compactAction (inverseRegion_compact q hs) hε t x A v‖ := by
  have hv := compactAction_restrict_norm A hs (inverseRegion_compact q hs)
    Set.subset_union_left hε t x v
  have hu (j : ℕ) (hj : j∈Finset.range q) :
      ‖compactAction hs hε t x (A*(primeX q)^j) v‖≤
        ‖compactAction (inverseRegion_compact q hs) hε t x A v‖ := by
    have he := congrArg (fun B : Ring => ‖compactAction hs hε t x (A*B) v‖)
      (prime_power_translation q j)
    apply he.trans_le
    apply (compact_right_translation_norm ((j : ℚ)/q) A hs hε t x v).trans
    apply compactAction_restrict_norm A _ (inverseRegion_compact q hs) _ hε t x v
    exact Set.Subset.trans (Set.subset_iUnion_of_subset ⟨j,Finset.mem_range.mp hj⟩
      (Set.Subset.refl _)) Set.subset_union_right
  have he : compactAction hs hε t x (A*primeInverse q) v=
      ((q : ℂ)-1)⁻¹ • (∑ j∈Finset.range q, compactAction hs hε t x (A*(primeX q)^j) v)-
        compactAction hs hε t x A v := by
    rw [prime_inverse_expansion q hq]
    simp only [mul_sub,mul_smul_comm,mul_one,Finset.mul_sum,map_sub,map_smul,map_sum,
      _root_.sub_apply,_root_.smul_apply,_root_.sum_apply]
  exact (congrArg norm he).trans_le (finite_inverse_vector_bound q _ _ _
    (norm_nonneg _) hv hu (inverse_scalar_cost q hq))

#print axioms inverse_polynomial_geometric
#print axioms prime_inverse_expansion
#print axioms prime_power_translation
#print axioms inverseRegion_compact
#print axioms inverse_scalar_cost
#print axioms compact_prime_inverse_bound
end QuantitativeEulerEndpointPrepared
