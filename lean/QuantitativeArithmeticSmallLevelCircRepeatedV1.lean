module

public import QuantitativeArithmeticSmallLevelCircOriginalOrbitV1
public import QuantitativeArithmeticSmallLevelCircTraceSumV1
public import AsymptoticRamifiedOldBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane Matrix AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticFreshMatrices AsymptoticOrbitDecode AsymptoticClassicalCosets
open AsymptoticClassicalPetersson QuantitativeEulerOldProjectionHolomorphic
open scoped ModularForm MatrixGroups

theorem repeated_trace_orbit_zero (M p m : ℕ) (hM : 0<M) (hp : 0<p)
    (F : ℍ → ℂ) (w : ℂ)
    (hW : ∀ z g, w * orbit m F z
      (frickeLabel (p*M) (Nat.mul_pos hp hM)*g) = orbit m F z g)
    (hU : ∀ z g, (∑ a : Fin p, orbit m F z (ramifiedLabel p hp a*g)) = 0)
    (z : ℍ) (g : AsymptoticRationalGroup.Group) :
    (∑ a : Fin p, orbit m F z (integralLabel (lowerSL M (-(a.val : ℤ)))*g)) = 0 := by
  have hh := hU z (dilationLabel p hp * frickeLabel (p*M) (Nat.mul_pos hp hM) * g)
  have he (a : Fin p) :
      ramifiedLabel p hp a * (dilationLabel p hp * frickeLabel (p*M) (Nat.mul_pos hp hM) * g) =
      frickeLabel (p*M) (Nat.mul_pos hp hM) * (integralLabel (lowerSL M (-(a.val : ℤ))) * g) := by
    rw [← mul_assoc, ← mul_assoc, ramifiedLabel_mul_dilation]
    rw [← mul_assoc, fricke_lower_div M p hM hp]
    simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
  simp_rw [he] at hh
  have hh' := congrArg (fun t : ℂ => w*t) hh
  rw [Finset.mul_sum] at hh'
  simpa only [hW, mul_zero] using hh'

theorem modularTrace_repeated_sum (M p : ℕ) [NeZero M] (hp : 0<p)
    (hM : 0<M) (hpM : p∣M) (k : ℤ) (F : ModularForm (level (p*M)) k) :
    (by
      let : NeZero (p*M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
      let : (level (p*M)).IsFiniteRelIndex (level M) :=
        ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p*M))).trans
          (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
      exact (ModularForm.trace (level M) F : ℍ → ℂ)) =
      ∑ a : Fin p, (F : ℍ → ℂ) ∣[k] lowerSL M (-(a.val : ℤ)) := by
  classical
  let : NeZero (p*M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
  let : (level (p*M)).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p*M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let := Fintype.ofFinite (level M ⧸ (level (p*M)).subgroupOf (level M))
  let e := (AsymptoticRamifiedCosets.cosetEquiv M p hM hp hpM).trans (matrixEquiv (p*M) M)
  change (∑ q : level M ⧸ (level (p*M)).subgroupOf (level M),
    SlashInvariantForm.quotientFunc F q) = _
  rw [← e.sum_comp (fun q => SlashInvariantForm.quotientFunc F q)]
  apply Finset.sum_congr rfl
  intro a _
  change (F : ℍ → ℂ) ∣[k] (SpecialLinearGroup.mapGL ℝ (lowerSL M a.val))⁻¹ = _
  rw [← map_inv, lowerSL_inv]
  rfl

theorem repeated_trace_slash_zero (M p m : ℕ) (hM : 0<M) (hp : 0<p)
    (F : ℍ → ℂ) (w : ℂ)
    (hW : ∀ z g, w * orbit m F z
      (frickeLabel (p*M) (Nat.mul_pos hp hM)*g) = orbit m F z g)
    (hU : ∀ z g, (∑ a : Fin p, orbit m F z (ramifiedLabel p hp a*g)) = 0) :
    (∑ a : Fin p, F ∣[((2*m : ℕ) : ℤ)] lowerSL M (-(a.val : ℤ))) = 0 := by
  funext z
  have hh := repeated_trace_orbit_zero M p m hM hp F w hW hU z 1
  simp only [mul_one, orbit_integral, ← Finset.mul_sum] at hh
  have hz : (z.im : ℂ)^m ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr z.im_pos.ne')
  simpa only [Finset.sum_apply, Pi.zero_apply] using (mul_eq_zero.mp hh).resolve_left hz

#print axioms repeated_trace_orbit_zero
#print axioms modularTrace_repeated_sum
#print axioms repeated_trace_slash_zero
end QuantitativeArithmeticSmallLevelCirc
