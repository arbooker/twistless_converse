module

public import QuantitativeMaassModularPrimeTwistsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix AsymptoticFreshMatrices AsymptoticCongruenceLabels
open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticReconstructionBranch
open AsymptoticIntegralSubgroup AsymptoticFreshAveraging

namespace QuantitativeMaass

/-- Inversion of primitive residue classes works at every modulus
coprime to N, not only at primes. -/
def coprimeTwistPermutation (N q : ℕ) (hc : N.Coprime q) : Equiv.Perm (ZMod q)ˣ :=
  (Equiv.inv (ZMod q)ˣ).trans (Equiv.mulLeft (-(ZMod.unitOfCoprime N hc)⁻¹))

theorem coprimeTwistPermutation_relation (N q : ℕ) [NeZero q] (hc : N.Coprime q)
    (u : (ZMod q)ˣ) :
    (N:ZMod q)*((coprimeTwistPermutation N q hc u:ZMod q).val:ZMod q)*
      ((u:ZMod q).val:ZMod q)= -1 := by
  have he : ZMod.unitOfCoprime N hc*coprimeTwistPermutation N q hc u*u= -1 := by
    change ZMod.unitOfCoprime N hc*((-(ZMod.unitOfCoprime N hc)⁻¹)*u⁻¹)*u= -1
    simp
  have hz := congrArg (fun x : (ZMod q)ˣ => (x:ZMod q)) he
  simpa only [Units.val_mul,Units.val_neg,Units.val_one,ZMod.coe_unitOfCoprime,
    ZMod.natCast_zmod_val] using hz

theorem coprimeTwistPermutation_divisibility (N q : ℕ) [NeZero q] (hc : N.Coprime q)
    (u : (ZMod q)ˣ) :
    (q:ℤ)∣(N:ℤ)*((coprimeTwistPermutation N q hc u:ZMod q).val:ℤ)*
      ((u:ZMod q).val:ℤ)+1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  push_cast
  rw [coprimeTwistPermutation_relation]
  simp

/-- Literal cancellation of the input translation in a reconstruction
branch, valid at composite moduli as well. -/
theorem twist_label_translation (N q : ℕ) (hN : 0<N) (hq : 0<q) (a b : ℤ) :
    label N q hN hq a b*translationLabel ((b:ℚ)/q)=
      translationLabel ((a:ℚ)/q)*frickeLabel (N*q^2) (Nat.mul_pos hN (pow_pos hq 2)) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branchMatrix N q hN.ne' hq.ne' a b)*
      rationalMap (AsymptoticMobiusFold.translation ((b:ℚ)/q))=
    rationalMap (AsymptoticMobiusFold.translation ((a:ℚ)/q))*
      rationalMap (branch ((N*q^2:ℕ):ℚ) 0 0 _)
  rw [←map_mul,←map_mul]
  congr 1
  unfold branchMatrix
  rw [neg_div,branch_cancel_translation]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branch,AsymptoticMobiusFold.translation,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- Units parametrize exactly the primitive residues used in the
original analytic twist definition, including q=1. -/
def primitiveResidueUnitsEquiv (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ FinitenessRamanujanSum.residues q where
  toFun u := ⟨(u:ZMod q).val,Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (ZMod.val_lt _),ZMod.val_coe_unit_coprime u⟩⟩
  invFun a := ZMod.unitOfCoprime a.val (Finset.mem_filter.mp a.property).2
  left_inv u := by
    apply Units.ext
    exact ZMod.natCast_zmod_val _
  right_inv a := by
    apply Subtype.ext
    change ((a.val:ZMod q).val)=a.val
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp a.property).1)]

#print axioms coprimeTwistPermutation_relation
#print axioms coprimeTwistPermutation_divisibility
#print axioms twist_label_translation
#print axioms primitiveResidueUnitsEquiv

end QuantitativeMaass
