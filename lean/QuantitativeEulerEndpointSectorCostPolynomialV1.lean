module

public import QuantitativeEulerEndpointSectorPacketSumV1
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Tactic.ComputeDegree

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticSectorSigns QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows Polynomial
open scoped Classical MatrixGroups

variable (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
  (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)

def sectorRowCostPolynomial (ε : ℝ) (t : ℕ) (i : SectorFamilyIndex N) : Polynomial ℝ :=
  C (sectorFamilyL N hN sector S hS i)*
    (1+C (ε*sectorFamilyK N hN sector S hS i)*
      (C (sectorFamilyC N hN sector S hS i)⁻¹*X+C 3)^2)^(2*t)

theorem sectorRowCostPolynomial_eval (ε H : ℝ) (t : ℕ) (i : SectorFamilyIndex N) :
    (sectorRowCostPolynomial N hN sector S hS ε t i).eval H=
      sectorFamilyCost N hN sector S hS H ε t i := by
  simp only [sectorRowCostPolynomial,sectorFamilyCost,eval_mul,eval_C,eval_pow,eval_add,eval_one,eval_X]
  congr 3
  rw [div_eq_mul_inv]
  ring

theorem sectorRowCostPolynomial_degree (ε : ℝ) (t : ℕ) (i : SectorFamilyIndex N) :
    (sectorRowCostPolynomial N hN sector S hS ε t i).natDegree≤4*t := by
  unfold sectorRowCostPolynomial
  compute_degree!
  omega

def sectorObservationPolynomial (W : Finset (List SL(2,ℤ))) (B ε : ℝ) (t : ℕ) : Polynomial ℝ :=
  (C (terminalObservationConstant S W)*(1+C (B^2)*(X+C 3)^2)^(2*t))*
    (1+C (sectorGap N hN)⁻¹*∑ i,(sectorRowCostPolynomial N hN sector S hS ε t i)^2)

theorem sectorObservationPolynomial_eval (W : Finset (List SL(2,ℤ))) (B ε H : ℝ) (t : ℕ) :
    (sectorObservationPolynomial N hN sector S hS W B ε t).eval H=
      sectorObservationCost N hN sector S hS W B H ε t := by
  simp only [sectorObservationPolynomial,sectorObservationCost,eval_mul,eval_C,eval_pow,
    eval_add,eval_one,eval_X,eval_finsetSum,sectorRowCostPolynomial_eval]

theorem sectorObservationPolynomial_degree (W : Finset (List SL(2,ℤ))) (B ε : ℝ) (t : ℕ) :
    (sectorObservationPolynomial N hN sector S hS W B ε t).natDegree≤12*t := by
  have hr : (∑ i,(sectorRowCostPolynomial N hN sector S hS ε t i)^2).natDegree≤8*t := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_pow_le_of_le 2 (sectorRowCostPolynomial_degree N hN sector S hS ε t i)).trans_eq (by omega)
  have hl : (C (terminalObservationConstant S W)*(1+C (B^2)*(X+C 3)^2)^(2*t) : Polynomial ℝ).natDegree≤4*t := by
    compute_degree!
    omega
  have hh : (1+C (sectorGap N hN)⁻¹*∑ i,(sectorRowCostPolynomial N hN sector S hS ε t i)^2).natDegree≤8*t := by
    rw [natDegree_one_add]
    exact (natDegree_mul_le_of_le (by simp : (C (sectorGap N hN)⁻¹ : Polynomial ℝ).natDegree≤0) hr).trans_eq (by omega)
  exact (natDegree_mul_le_of_le hl hh).trans_eq (by omega)

/-- At fixed epsilon and weight, the actual source observation cost is
an explicit polynomial of degree at most 12t in the common height. -/
theorem sectorObservationCost_polynomial (W : Finset (List SL(2,ℤ))) (B ε : ℝ) (t : ℕ) :
    ∃ p : Polynomial ℝ, p.natDegree≤12*t ∧
      ∀ H : ℝ,p.eval H=sectorObservationCost N hN sector S hS W B H ε t :=
  ⟨sectorObservationPolynomial N hN sector S hS W B ε t,
    sectorObservationPolynomial_degree N hN sector S hS W B ε t,
    fun H => sectorObservationPolynomial_eval N hN sector S hS W B ε H t⟩

#print axioms sectorObservationCost_polynomial
end QuantitativeEulerEndpointPrepared
