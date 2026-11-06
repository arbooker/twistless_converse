module

public import AsymptoticClassicalHeckeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticAtkinLehner AsymptoticClassicalCosets
open AsymptoticCongruenceLabels AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups

variable (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0 < N) (hpN : ¬ p ∣ N)
variable (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (k : ℤ)

include hN hpN

/-- Explicit good-prime cosets for the trace on genuine cusp forms. -/
theorem arithmeticTrace_prime_sum (f : CuspForm (level (p * N)) k) :
    (by
      let : NeZero (p * N) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne N)⟩
      exact (arithmeticTrace (level (p * N)) (level N) k f : ℍ → ℂ)) =
      f + ∑ a : Fin p, (f : ℍ → ℂ) ∣[k] traceSL N p A B hAB a.val := by
  classical
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne N)⟩
  let : (level (p * N)).IsFiniteRelIndex (level N) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * N))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).symm).1
  let := Fintype.ofFinite (level N ⧸ (level (p * N)).subgroupOf (level N))
  let := Fintype.ofFinite (AsymptoticCongruenceStrip.gamma N ⧸
    (AsymptoticCongruenceStrip.gamma (p * N)).subgroupOf (AsymptoticCongruenceStrip.gamma N))
  let e := (traceCosetEquiv N p hN hpN A B hAB).trans (traceEquiv (p * N) N).symm
  have hnone : SlashInvariantForm.quotientFunc f (e none) = f := by
    have he : e none = QuotientGroup.mk
        ((SpecialLinearGroup.mapGL ℝ).subgroupMap (CongruenceSubgroup.Gamma0 N) 1) := by
      apply (traceEquiv (p * N) N).injective
      rw [traceEquiv_mk]
      change (traceEquiv (p * N) N) ((traceEquiv (p * N) N).symm _) = _
      rw [Equiv.apply_symm_apply]
      change QuotientGroup.mk (1 : AsymptoticCongruenceStrip.gamma N) =
        QuotientGroup.mk (integralLabel.subgroupMap (CongruenceSubgroup.Gamma0 N) 1)
      rw [map_one]
      rfl
    rw [he, SlashInvariantForm.quotientFunc_mk]
    simp
  have hsome (a : Fin p) : SlashInvariantForm.quotientFunc f (e (some a)) =
      (f : ℍ → ℂ) ∣[k] traceSL N p A B hAB a.val := by
    let t : CongruenceSubgroup.Gamma0 N :=
      ⟨traceSL N p A B hAB a.val, traceSL_mem N p A B hAB a.val⟩
    have he : e (some a) = QuotientGroup.mk
        ((SpecialLinearGroup.mapGL ℝ).subgroupMap (CongruenceSubgroup.Gamma0 N) t⁻¹) := by
      apply (traceEquiv (p * N) N).injective
      rw [traceEquiv_mk]
      change (traceEquiv (p * N) N) ((traceEquiv (p * N) N).symm _) = _
      rw [Equiv.apply_symm_apply]
      change QuotientGroup.mk (traceRepresentative N p A B hAB (some a)) = _
      congr 1
      apply Subtype.ext
      change (integralLabel (traceSL N p A B hAB a.val))⁻¹ =
        integralLabel (traceSL N p A B hAB a.val)⁻¹
      exact (map_inv integralLabel _).symm
    rw [he, SlashInvariantForm.quotientFunc_mk]
    change (f : ℍ → ℂ) ∣[k] (SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB a.val)⁻¹)⁻¹ = _
    rw [map_inv, inv_inv]
    rfl
  change (∑ q : level N ⧸ (level (p * N)).subgroupOf (level N),
    SlashInvariantForm.quotientFunc f q) = _
  rw [← e.sum_comp (fun q => SlashInvariantForm.quotientFunc f q), Fintype.sum_option]
  rw [hnone]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => hsome a)

#print axioms arithmeticTrace_prime_sum

end AsymptoticClassicalCusp
