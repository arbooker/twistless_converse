module

public import QuantitativeArithmeticHeckeCuspIndicatorV1
public import QuantitativeArithmeticSmallLevelEisensteinBoundaryPrimeFactorsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix
open scoped MatrixGroups

theorem integral_hecke_indicator (p : ℕ) (hp : p.Prime) (γ : SL(2,ℤ)) :
    (if (p:ℤ)∣γ 1 0 then 1 else 0) +
      (∑ j : Fin p, if (p:ℤ)∣γ 0 0+(j.val:ℤ)*γ 1 0 then 1 else 0 : ℕ) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hd := congrArg (Int.castRingHom (ZMod p)) γ.property
  rw [Matrix.det_fin_two] at hd
  have hd' : (γ 0 0 : ZMod p)*(γ 1 1 : ZMod p)-(γ 0 1 : ZMod p)*(γ 1 0 : ZMod p)=1 := by
    simpa using hd
  have h := QuantitativeArithmeticHeckeCuspIndicator.fin_indicator
    (γ 0 0 : ZMod p) (γ 0 1 : ZMod p) (γ 1 0 : ZMod p) (γ 1 1 : ZMod p) hd'
  simpa only [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_add,Int.cast_mul,Int.cast_natCast] using h

private theorem weighted_indicator_sum {ι : Type*} [Fintype ι] (P : Prop) (Q : ι → Prop) [Decidable P] [DecidablePred Q]
    (A B : ℂ) (hc : (if P then (1:ℂ) else 0)+(∑ j, if Q j then (1:ℂ) else 0)=1) :
    (if P then A else B)+(∑ j, if Q j then A else B)=A+(Fintype.card ι:ℂ)*B := by
  classical
  have hi (R : Prop) [Decidable R] : (if R then A else B)=(if R then (1:ℂ) else 0)*(A-B)+B := by
    by_cases hR : R <;> simp [hR]
  have hs : (∑ j, if Q j then A else B) =
      ∑ j, ((if Q j then (1:ℂ) else 0)*(A-B)+B) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hi (Q j)
  rw [hi P,hs,Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  linear_combination (A-B)*hc

theorem integral_hecke_weights (p : ℕ) (hp : p.Prime) (γ : SL(2,ℤ)) (A B : ℂ) :
    (if (p:ℤ)∣γ 1 0 then A else B) +
      (∑ j : Fin p, if (p:ℤ)∣γ 0 0+(j.val:ℤ)*γ 1 0 then A else B) = A+(p:ℂ)*B := by
  classical
  have hc : (if (p:ℤ)∣γ 1 0 then (1:ℂ) else 0) +
      (∑ j : Fin p, if (p:ℤ)∣γ 0 0+(j.val:ℤ)*γ 1 0 then (1:ℂ) else 0) = 1 := by
    exact_mod_cast integral_hecke_indicator p hp γ
  simpa only [Fintype.card_fin] using weighted_indicator_sum
    ((p:ℤ)∣γ 1 0) (fun j : Fin p ↦ (p:ℤ)∣γ 0 0+(j.val:ℤ)*γ 1 0) A B hc

theorem prime_boundary_weights (p : ℕ) (hp : p.Prime) (γ : SL(2,ℤ)) (k : ℤ) :
    (if (p:ℤ)∣γ 1 0 then (p:ℂ)^(k-1) else (p:ℂ)⁻¹) +
      (∑ j : Fin p, if (p:ℤ)∣γ 0 0+(j.val:ℤ)*γ 1 0 then (p:ℂ)^(k-1) else (p:ℂ)⁻¹) =
        1+(p:ℂ)^(k-1) := by
  rw [integral_hecke_weights p hp γ]
  have hpC : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [mul_inv_cancel₀ hpC,add_comm]

#print axioms integral_hecke_indicator
#print axioms integral_hecke_weights
#print axioms prime_boundary_weights

end QuantitativeArithmeticSmallLevelEisenstein
