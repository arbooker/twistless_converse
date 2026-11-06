module

public import QuantitativeArithmeticDiamondLabelsTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticDiamondLabels

open Matrix CongruenceSubgroup QuantitativeArithmetic QuantitativeEulerDensityGenerators
open AsymptoticCongruenceLabels AsymptoticFreshMatrices AsymptoticFreshResidues
open AsymptoticFreshAveraging AsymptoticRationalBranches AsymptoticIntegralSubgroup
open scoped MatrixGroups

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

/-- The precise integral canonical matrix underlying the existing defect label. -/
def branchCanonical (i : Fin (q-1)) : SL(2,ℤ) :=
  canonical N q ((permutation q N hq i).val+1) (i.val+1)
    (quotient q N hq i) (quotient_relation q N hq i)

theorem branchCanonical_mem (i : Fin (q-1)) : branchCanonical N q hq i∈Gamma0 N :=
  canonical_mem_Gamma0 N q _ _ _ _

theorem defectLabel_eq_fricke (i : Fin (q-1)) :
    defectLabel N q hN hq i=frickeLabel N hN*integralLabel (branchCanonical N q hq i) := by
  rw [branchCanonical,canonical_label]
  exact label_eq_fricke_canonical N q hN (Fact.out : q.Prime).pos _ _ _ _

theorem branch_difference_gamma1 (i j : Fin (q-1)) :
    branchCanonical N q hq i*(branchCanonical N q hq j)⁻¹∈Gamma1 N :=
  canonical_right_difference N q _ _ _ _ _ _ _ _

/-- Explicit Gamma1 matrix for the quotient of any two actual defects. -/
def defectDifference (i j : Fin (q-1)) : SL(2,ℤ) :=
  frickeConjugate N (branchCanonical N q hq i*(branchCanonical N q hq j)⁻¹)
    (Gamma1_in_Gamma0 N (branch_difference_gamma1 N q hq i j))

theorem defectDifference_mem (i j : Fin (q-1)) : defectDifference N q hq i j∈Gamma1 N :=
  frickeConjugate_gamma1 N _ (branch_difference_gamma1 N q hq i j)

/-- First requested identity, for the literal existing defect labels. -/
theorem defectLabel_mul_inv (i j : Fin (q-1)) :
    defectLabel N q hN hq i*(defectLabel N q hN hq j)⁻¹=
      integralLabel (defectDifference N q hq i j) := by
  rw [defectLabel_eq_fricke,defectLabel_eq_fricke,defectDifference]
  rw [← frickeConjugate_label N hN]
  simp only [map_mul,map_inv,_root_.mul_inv_rev]
  group

theorem branch_translation_gamma1 (j : Fin (q-1)) :
    branchCanonical N q hq j*upperSL 1*(branchCanonical N q hq j)⁻¹∈Gamma1 N := by
  have hh := gamma1_conjugate N (branchCanonical N q hq j)⁻¹ (upperSL 1)
    ((Gamma0 N).inv_mem (branchCanonical_mem N q hq j)) (upperSL_one_gamma1 N)
  simpa only [inv_inv] using hh

/-- Explicit Gamma1 matrix for conjugation of unit translation by a defect. -/
def defectTranslation (j : Fin (q-1)) : SL(2,ℤ) :=
  frickeConjugate N (branchCanonical N q hq j*upperSL 1*(branchCanonical N q hq j)⁻¹)
    (Gamma1_in_Gamma0 N (branch_translation_gamma1 N q hq j))

theorem defectTranslation_mem (j : Fin (q-1)) : defectTranslation N q hq j∈Gamma1 N :=
  frickeConjugate_gamma1 N _ (branch_translation_gamma1 N q hq j)

/-- Second requested identity: conjugated unit translation is literally Gamma1. -/
theorem defectLabel_translation_conjugate (j : Fin (q-1)) :
    defectLabel N q hN hq j*translationLabel 1*(defectLabel N q hN hq j)⁻¹=
      integralLabel (defectTranslation N q hq j) := by
  rw [defectLabel_eq_fricke,defectTranslation,← frickeConjugate_label N hN]
  rw [map_mul,map_mul,map_inv,upper_label]
  norm_num only [Int.cast_one]
  group

/-- The manuscript diamond matrix has the two residue parameters swapped. -/
def swappedCanonical (j : Fin (q-1)) : SL(2,ℤ) :=
  canonical N q (j.val+1) ((permutation q N hq j).val+1) (quotient q N hq j)
    (swapped_certificate N q _ _ _ (quotient_relation q N hq j))

theorem swappedCanonical_mem (j : Fin (q-1)) : swappedCanonical N q hq j∈Gamma0 N :=
  canonical_mem_Gamma0 N q _ _ _ _

theorem swappedCanonical_leading (j : Fin (q-1)) :
    (swappedCanonical N q hq j).val 0 0=(q:ℤ) := rfl

/-- Third requested identity, retaining the correct swapped residue convention. -/
theorem fricke_defectLabel_inv (j : Fin (q-1)) :
    frickeLabel N hN*(defectLabel N q hN hq j)⁻¹=
      integralLabel (swappedCanonical N q hq j) := by
  have hh := fricke_intertwine_label N hN (branchCanonical N q hq j)⁻¹
    (swappedCanonical N q hq j) (canonical_fricke_inverse N q _ _ _ (quotient_relation q N hq j))
  rw [map_inv] at hh
  rw [defectLabel_eq_fricke,_root_.mul_inv_rev,← mul_assoc,hh]
  group

#print axioms defectDifference_mem
#print axioms defectLabel_mul_inv
#print axioms defectTranslation_mem
#print axioms defectLabel_translation_conjugate
#print axioms swappedCanonical_mem
#print axioms swappedCanonical_leading
#print axioms fricke_defectLabel_inv

end QuantitativeArithmeticDiamondLabels
