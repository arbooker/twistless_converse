module

public import QuantitativeNewGapTreeArithmeticV1
public import AsymptoticAtkinLehnerTraceCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticNestedQuotients AsymptoticAtkinLehner AsymptoticRamifiedCosets
open scoped MatrixGroups BigOperators lp ComplexConjugate

instance degeneracyQuotientFinite (M p : ℕ) [NeZero M] (hp : 0 < p) :
    Finite (degeneracyGroup M p hp ⧸
      (gamma (p*M)).subgroupOf (degeneracyGroup M p hp)) := by
  rw [← frickeOldGroup_eq_degeneracy M p (Nat.pos_of_ne_zero (NeZero.ne M)) hp]
  infer_instance

/-- Exact cross Gram of the two actual old embeddings, expanded over the
p+1 explicit trace representatives. The input is an arbitrary square-summable
function on the second old quotient. -/
theorem old_cross_gram_trace (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) (A B : ℤ) (hAB : (p : ℤ)*A+(M : ℤ)*B=1)
    (f : ℓ²(Classes (degeneracyGroup M p (Fact.out : p.Prime).pos), ℂ))
    (g : AsymptoticRationalGroup.Group) :
    ((isometry (gamma_le_of_dvd (Nat.dvd_mul_left M p))).toContinuousLinearMap.adjoint
      (isometry (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
        (Fact.out : p.Prime).pos) f)) (classOf (gamma M) g) =
      ((p+1 : ℕ) : ℂ)⁻¹ *
        (f (classOf (degeneracyGroup M p (Fact.out : p.Prime).pos) g) +
          ∑ a : Fin p, f (classOf (degeneracyGroup M p (Fact.out : p.Prime).pos)
            (integralLabel (traceSL M p A B hAB a.val) * g))) := by
  classical
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  let hp := (Fact.out : p.Prime).pos
  let hJ : gamma (p*M) ≤ gamma M := gamma_le_of_dvd (Nat.dvd_mul_left M p)
  let hK := gamma_le_degeneracyGroup M p hM hp
  have hi : ((gamma (p*M)).subgroupOf (gamma M)).index = p+1 :=
    projective_index_coprime M p hM Fact.out ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM)
  have hk : ((gamma (p*M)).subgroupOf (degeneracyGroup M p hp)).index = p+1 := by
    change (gamma (p*M)).relIndex (degeneracyGroup M p hp) = _
    rw [degeneracyGroup_index M p hM hp]
    exact hi
  change (AsymptoticFiniteFiberInduction.isometry (forget hJ) _
    index_pos (fibre_card hJ)).toContinuousLinearMap.adjoint (isometry hK f)
      (classOf (gamma M) g) = _
  rw [AsymptoticFiniteFiberInduction.adjoint_apply]
  rw [fibre_sum_eq_coset_sum hJ (traceRepresentative M p A B hAB)
    (traceCosetEquiv M p hM hpM A B hAB) (fun _ => rfl)]
  simp_rw [isometry_apply, forget_classOf]
  rw [hi, hk, ← Finset.mul_sum, ← mul_assoc]
  have hc : conj (AsymptoticFiniteFiberInduction.coefficient (p+1)) *
      AsymptoticFiniteFiberInduction.coefficient (p+1) = ((p+1 : ℕ) : ℂ)⁻¹ := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      AsymptoticFiniteFiberInduction.coefficient_norm_sq (by omega)]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hc]
  congr 1
  rw [Fintype.sum_option]
  simp [traceRepresentative]

#print axioms old_cross_gram_trace

end QuantitativeNewGap
