module

public import QuantitativeMaassCoprimeAnalyticLawsV1
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Ring.Periodic

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- The CRT parametrization adapted to adding primitive translations. -/
def primitiveTranslationCRT (m n : ℕ) (hc : m.Coprime n) :
    (ZMod m)ˣ × (ZMod n)ˣ ≃ (ZMod (m*n))ˣ :=
  ((Equiv.mulLeft (ZMod.unitOfCoprime n hc.symm)).prodCongr
    (Equiv.mulLeft (ZMod.unitOfCoprime m hc))).trans
    ((MulEquiv.prodUnits.toEquiv.symm).trans
      (Units.mapEquiv (ZMod.chineseRemainder hc).toMulEquiv).toEquiv.symm)

theorem primitiveTranslationCRT_value (m n : ℕ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (primitiveTranslationCRT m n hc (a,b):ZMod (m*n))=
      (n:ZMod (m*n))*((a:ZMod m).val:ZMod (m*n))+
      (m:ZMod (m*n))*((b:ZMod n).val:ZMod (m*n)) := by
  apply (ZMod.chineseRemainder hc).injective
  have hh := congrArg (fun u : (ZMod m × ZMod n)ˣ => (u:ZMod m × ZMod n))
    ((Units.mapEquiv (ZMod.chineseRemainder hc).toMulEquiv).apply_symm_apply
      (MulEquiv.prodUnits.symm
        (ZMod.unitOfCoprime n hc.symm*a,ZMod.unitOfCoprime m hc*b)))
  change (ZMod.chineseRemainder hc)
    (primitiveTranslationCRT m n hc (a,b):ZMod (m*n))=
    (((ZMod.unitOfCoprime n hc.symm*a: (ZMod m)ˣ):ZMod m),
     ((ZMod.unitOfCoprime m hc*b: (ZMod n)ˣ):ZMod n)) at hh
  rw [hh]
  simp only [map_add,map_mul,map_natCast]
  ext <;> simp

theorem periodic_fraction_congr (F : ℂ → ℂ) (hF : Function.Periodic F 1)
    (q : ℕ) (hq : 0<q) (a b : ℤ) (h : (a:ZMod q)=(b:ZMod q)) (z : ℂ) :
    F (z+(a:ℂ)/q)=F (z+(b:ℂ)/q) := by
  have hd : (q:ℤ)∣a-b := (ZMod.intCast_zmod_eq_zero_iff_dvd (a-b) q).mp (by
    push_cast
    exact sub_eq_zero.mpr h)
  obtain ⟨k,hk⟩ := hd
  have hqC : (q:ℂ)≠0 := by exact_mod_cast hq.ne'
  have he : z+(a:ℂ)/q=(z+(b:ℂ)/q)+(k:ℂ)*1 := by
    have hh : (a:ℂ)-(b:ℂ)=(q:ℂ)*(k:ℂ) := by exact_mod_cast hk
    field_simp
    linear_combination hh
  rw [he]
  exact hF.int_mul k _

#print axioms primitiveTranslationCRT_value
#print axioms periodic_fraction_congr

end QuantitativeMaass
