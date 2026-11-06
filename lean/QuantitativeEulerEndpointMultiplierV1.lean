module

public import QuantitativeEulerEndpointCorrectionV1
public import QuantitativeEulerEndpointBranchHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeHolomorphic QuantitativeArithmetic
open QuantitativeEulerDiamondDecode QuantitativeEulerDiamondPolynomial
open AsymptoticIntegralSubgroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- Every branch is composed before transporting from the original set. -/
def translatedMultiplierRegion (g : G) (q : ℕ) (s : Set ℍ) : Set ℍ :=
  ⋃ j : Fin q, branchImage (symbolBranch (g*translationLabel ((j.val : ℚ)/q))) s

theorem translatedMultiplierRegion_compact (g : G) (q : ℕ) {s : Set ℍ}
    (hs : IsCompact s) : IsCompact (translatedMultiplierRegion g q s) :=
  isCompact_iUnion (fun j => branchImage_compact
    (symbolBranch (g*translationLabel ((j.val : ℚ)/q))) hs)

theorem transported_prime_power_bound (g : G) (q i : ℕ) (hq : 0<q) (hi : i<q)
    {M : IntegerMatrix2} {B H ε : ℝ} (hM : IntegerAction g M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x ((A*symbol g)*(primeX q)^i) v‖≤
      (integerCompactDistortion (2*B*(q : ℝ)) H)^t*
        ‖compactAction (translatedMultiplierRegion_compact g q hs) hε t x A v‖ := by
  let b := symbolBranch (g*translationLabel ((i : ℚ)/q))
  have hMi : IntegerAction (ofMatrix b.matrix b.positive) (M*translationIntegerMatrix q i) := by
    rw [symbolBranch_label]
    exact hM.mul (translation_label_integer_action q i hq)
  have hbi := matrix_entry_bound_mul hB hb (translation_integer_bound q i hi.le)
  have ht := compactAction_mul_symbol_integer_norm b hs hMi (by positivity) hbi
    hε hre him t x A v
  have halg : (A*symbol g)*(primeX q)^i=A*symbol (g*translationLabel ((i : ℚ)/q)) := by
    rw [prime_power_translation,map_mul,mul_assoc]
  have hlabel := congrArg (fun z : G => ‖compactAction hs hε t x (A*symbol z) v‖)
    (symbolBranch_label (g*translationLabel ((i : ℚ)/q)))
  have hnorm := (congrArg (fun Z : Ring => ‖compactAction hs hε t x Z v‖) halg).trans hlabel.symm
  have hr := compactAction_restrict_norm A (branchImage_compact b hs)
    (translatedMultiplierRegion_compact g q hs)
    (Set.subset_iUnion_of_subset ⟨i,hi⟩ (Set.Subset.refl _)) hε t x v
  exact hnorm.trans_le (ht.trans (mul_le_mul_of_nonneg_left hr
    (by unfold integerCompactDistortion; positivity)))

private theorem inverse_vector_bound (q : ℕ) (c : ℂ) (u : ℕ → Space)
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

/-- A uniform explicit height cost for the inverse after an arbitrary
integral-representable multiplier. No unit-strip hypothesis is imposed on
an intermediate image region. -/
theorem transported_prime_inverse_bound (g : G) (q : ℕ) (hq : 2≤q)
    {M : IntegerMatrix2} {B H ε : ℝ} (hM : IntegerAction g M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x ((A*symbol g)*primeInverse q) v‖≤
      3*((integerCompactDistortion (2*B*(q : ℝ)) H)^t*
        ‖compactAction (translatedMultiplierRegion_compact g q hs) hε t x A v‖) := by
  have hu (i : ℕ) (hi : i<q) := transported_prime_power_bound g q i (by omega) hi
    hM hB hb A hs hε hre him t x v
  have hzero := hu 0 (by omega)
  simp only [pow_zero,mul_one] at hzero
  have he : compactAction hs hε t x ((A*symbol g)*primeInverse q) v=
      ((q : ℂ)-1)⁻¹ • (∑ j∈Finset.range q,
        compactAction hs hε t x ((A*symbol g)*(primeX q)^j) v)-
          compactAction hs hε t x (A*symbol g) v := by
    rw [prime_inverse_expansion q hq]
    simp only [mul_sub,mul_smul_comm,mul_one,Finset.mul_sum,map_sub,map_smul,map_sum,
      _root_.sub_apply,_root_.smul_apply,_root_.sum_apply]
  exact (congrArg norm he).trans_le (inverse_vector_bound q _ _ _
    (by unfold integerCompactDistortion; positivity) hzero
    (fun i hi => hu i (Finset.mem_range.mp hi)) (inverse_scalar_cost q hq))

/-- The same composed images and explicit height bound control the period
correction, with its exact scalar mass q/2. -/
theorem transported_prime_correction_bound (g : G) (q : ℕ) (hq : 2≤q)
    {M : IntegerMatrix2} {B H ε : ℝ} (hM : IntegerAction g M)
    (hB : 0≤B) (hb : MatrixEntryBound M B) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x
      ((A*symbol g)*Polynomial.aeval (primeX q) (correctionPolynomial q)) v‖≤
      ((q : ℝ)/2)*((integerCompactDistortion (2*B*(q : ℝ)) H)^t*
        ‖compactAction (translatedMultiplierRegion_compact g q hs) hε t x A v‖) := by
  have hu (i : ℕ) (hi : i<q) := transported_prime_power_bound g q i (by omega) hi
    hM hB hb A hs hε hre him t x v
  have he : compactAction hs hε t x
      ((A*symbol g)*Polynomial.aeval (primeX q) (correctionPolynomial q)) v=
      ((q : ℂ)-1)⁻¹ • (∑ j∈Finset.range q, ∑ i∈Finset.range j,
        compactAction hs hε t x ((A*symbol g)*(primeX q)^i) v) := by
    rw [prime_correction_expansion]
    simp only [mul_smul_comm,Finset.mul_sum,map_smul,map_sum,_root_.smul_apply,_root_.sum_apply]
  have h := triangular_vector_bound q ((q : ℂ)-1)⁻¹
    (fun i => compactAction hs hε t x ((A*symbol g)*(primeX q)^i) v) hu
  rw [correction_scalar_mass q hq] at h
  exact (congrArg norm he).trans_le h

#print axioms transported_prime_power_bound
#print axioms transported_prime_inverse_bound
#print axioms transported_prime_correction_bound
end QuantitativeEulerEndpointPrepared
