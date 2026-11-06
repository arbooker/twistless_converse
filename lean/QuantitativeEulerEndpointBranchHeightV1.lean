module

public import QuantitativeEulerEndpointCanonicalNormV1
public import QuantitativeHolomorphicObservationMatricesV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeHolomorphic QuantitativeArithmetic
open QuantitativeEulerDiamondDecode QuantitativeArithmeticDiamondLabels
open QuantitativeEulerDensityGenerators
open AsymptoticFreshMatrices AsymptoticFreshResidues AsymptoticFreshAveraging
open AsymptoticCongruenceLabels AsymptoticIntegralSubgroup
open scoped MatrixGroups Classical

/-- A deliberately loose uniform bound for every canonical residue matrix.
It is independent of the prime's residue index and needs no chosen constant. -/
theorem canonical_entry_bound (N q : ℕ) (hq : 1≤q) (a b c : ℤ)
    (ha : 0≤a ∧ a≤q) (hb : 0≤b ∧ b≤q)
    (hdet : (q : ℤ)*c=(N : ℤ)*a*b+1) :
    MatrixEntryBound (canonical N q a b c hdet).val ((1+(N : ℝ))*(q : ℝ)^2) := by
  have hq' : (1 : ℝ)≤q := by exact_mod_cast hq
  have ha0 : (0 : ℝ)≤a := by exact_mod_cast ha.1
  have hb0 : (0 : ℝ)≤b := by exact_mod_cast hb.1
  have haq : (a : ℝ)≤q := by exact_mod_cast ha.2
  have hbq : (b : ℝ)≤q := by exact_mod_cast hb.2
  have hd : (q : ℝ)*c=(N : ℝ)*a*b+1 := by exact_mod_cast hdet
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hab := mul_le_mul haq hbq hb0 (Nat.cast_nonneg q : (0 : ℝ)≤q)
  have hNab := mul_le_mul_of_nonneg_left hab hN0
  have hprod : 0≤(N : ℝ)*a*b := mul_nonneg (mul_nonneg hN0 ha0) hb0
  have hc0 : (0 : ℝ)≤c := by nlinarith
  have hcq : (c : ℝ)≤(1+(N : ℝ))*(q : ℝ)^2 := by nlinarith
  have hqq : (q : ℝ)≤(1+(N : ℝ))*(q : ℝ)^2 := by
    nlinarith [mul_nonneg hN0 (sq_nonneg (q : ℝ))]
  have hNa : (N : ℝ)*a≤(1+(N : ℝ))*(q : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left haq hN0
    have h' : (N : ℝ)*q≤(N : ℝ)*(q : ℝ)^2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hN0
    nlinarith [sq_nonneg (q : ℝ)]
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [canonical,canonicalEntries] using hqq
  · simpa [canonical,canonicalEntries,abs_of_nonneg hb0] using hbq.trans hqq
  · simpa [canonical,canonicalEntries,abs_of_nonneg (mul_nonneg hN0 ha0)] using hNa
  · simpa [canonical,canonicalEntries,abs_of_nonneg hc0] using hcq

theorem branch_canonical_height (N q : ℕ) [Fact q.Prime] (hq : ¬q∣N)
    (j : Fin (q-1)) :
    MatrixEntryBound (branchCanonical N q hq j).val ((1+(N : ℝ))*(q : ℝ)^2) := by
  apply canonical_entry_bound N q (Fact.out : q.Prime).one_lt.le
  · have h := (permutation q N hq j).isLt
    constructor <;> omega
  · have h := j.isLt
    constructor <;> omega

theorem swapped_canonical_height (N q : ℕ) [Fact q.Prime] (hq : ¬q∣N)
    (j : Fin (q-1)) :
    MatrixEntryBound (swappedCanonical N q hq j).val ((1+(N : ℝ))*(q : ℝ)^2) := by
  apply canonical_entry_bound N q (Fact.out : q.Prime).one_lt.le
  · have h := j.isLt
    constructor <;> omega
  · have h := (permutation q N hq j).isLt
    constructor <;> omega

def defectIntegerMatrix (N q : ℕ) [Fact q.Prime] (hq : ¬q∣N)
    (j : Fin (q-1)) : IntegerMatrix2 :=
  integralFrickeMatrix N*(branchCanonical N q hq j).val

theorem defect_integer_action (N q : ℕ) [Fact q.Prime] (hN : 0<N)
    (hq : ¬q∣N) (j : Fin (q-1)) :
    IntegerAction (defectLabel N q hN hq j) (defectIntegerMatrix N q hq j) := by
  rw [defectLabel_eq_fricke]
  exact (integerAction_fricke N hN).mul (integerAction_integralLabel _)

theorem defect_integer_height (N q : ℕ) [Fact q.Prime] (hq : ¬q∣N)
    (j : Fin (q-1)) :
    MatrixEntryBound (defectIntegerMatrix N q hq j) (2*(1+(N : ℝ))^2*(q : ℝ)^2) := by
  have h := matrix_entry_bound_mul (by positivity) (fricke_entry_bound N)
    (branch_canonical_height N q hq j)
  change MatrixEntryBound (integralFrickeMatrix N*(branchCanonical N q hq j).val) _
  convert h using 1
  ring

theorem translation_label_integer_action (q a : ℕ) (hq : 0<q) :
    IntegerAction (translationLabel ((a : ℚ)/q)) (translationIntegerMatrix q a) :=
  translation_integer_action q a hq

#print axioms canonical_entry_bound
#print axioms branch_canonical_height
#print axioms swapped_canonical_height
#print axioms defect_integer_action
#print axioms defect_integer_height
#print axioms translation_label_integer_action
end QuantitativeEulerEndpointPrepared
