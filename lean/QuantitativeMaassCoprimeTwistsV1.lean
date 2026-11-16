module

public import QuantitativeMaassCoprimeTwistPermutationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticIntegralSubgroup

namespace QuantitativeMaass

/-- The literal primitive translation sum at an arbitrary modulus. -/
def primitiveTranslationSum (q : ℕ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  ∑ a ∈ FinitenessRamanujanSum.residues q,f (translationLabel ((a:ℚ)/q) • z)

theorem primitiveTranslationSum_units (q : ℕ) [NeZero q] (f : ℍ → ℂ) (z : ℍ) :
    primitiveTranslationSum q f z=
      ∑ u : (ZMod q)ˣ,f (translationLabel (((u:ZMod q).val:ℚ)/q) • z) := by
  classical
  unfold primitiveTranslationSum
  rw [←Finset.sum_coe_sort]
  exact (Equiv.sum_comp (primitiveResidueUnitsEquiv q)
    (fun a : FinitenessRamanujanSum.residues q => f (translationLabel ((a.val:ℚ)/q) • z))).symm

/-- Every modulus coprime to the level satisfies its actual Ramanujan
reflection law, with the lcm conductor appearing in the original equations. -/
theorem coprime_twist_of_modular (N q : ℕ) (hN : 0<N) (hq : 0<q)
    (hc : N.Coprime q) (f : ℍ → ℂ)
    (hmod : ∀ a : gamma N,∀ z,f (a.val • z)=f z)
    (w : ℂ) (hW : ∀ z,w*f (frickeLabel N hN • z)=f z) (z : ℍ) :
    w*primitiveTranslationSum q f
      (frickeLabel (Nat.lcm N (q^2)) (Nat.lcm_pos hN (pow_pos hq 2)) • z)=
      primitiveTranslationSum q f z := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  have hlevel : Nat.lcm N (q^2)=N*q^2 := (hc.pow_right 2).lcm_eq_mul
  simp only [hlevel]
  rw [primitiveTranslationSum_units,primitiveTranslationSum_units,Finset.mul_sum]
  have hterm (u : (ZMod q)ˣ) :
      w*f (translationLabel (((coprimeTwistPermutation N q hc u:ZMod q).val:ℚ)/q) •
        (frickeLabel (N*q^2) (Nat.mul_pos hN (pow_pos hq 2)) • z))=
      f (translationLabel (((u:ZMod q).val:ℚ)/q) • z) := by
    let a : ℤ := (coprimeTwistPermutation N q hc u:ZMod q).val
    let b : ℤ := (u:ZMod q).val
    let c : ℤ := ((N:ℤ)*a*b+1)/q
    have hrel : (q:ℤ)*c=(N:ℤ)*a*b+1 :=
      Int.mul_ediv_cancel' (coprimeTwistPermutation_divisibility N q hc u)
    have hd (y : ℍ) : w*f (label N q hN hq a b • y)=f y := by
      rw [label_eq_fricke_canonical N q hN hq a b c hrel,mul_smul,hW,←canonical_label]
      exact hmod ⟨_,⟨_,canonical_mem_Gamma0 N q a b c hrel,rfl⟩⟩ y
    have ht := hd (translationLabel ((b:ℚ)/q) • z)
    rw [←mul_smul,twist_label_translation N q hN hq a b,mul_smul] at ht
    simpa only [a,b,Int.cast_natCast] using ht
  calc
    _ = ∑ u : (ZMod q)ˣ,w*f
        (translationLabel (((coprimeTwistPermutation N q hc u:ZMod q).val:ℚ)/q) •
          (frickeLabel (N*q^2) (Nat.mul_pos hN (pow_pos hq 2)) • z)) :=
      (Equiv.sum_comp (coprimeTwistPermutation N q hc) (fun u : (ZMod q)ˣ =>
        w*f (translationLabel (((u:ZMod q).val:ℚ)/q) •
          (frickeLabel (N*q^2) (Nat.mul_pos hN (pow_pos hq 2)) • z)))).symm
    _ = _ := Finset.sum_congr rfl (fun u _ => hterm u)

#print axioms primitiveTranslationSum_units
#print axioms coprime_twist_of_modular

end QuantitativeMaass
