module

public import QuantitativeMaassHalfTranslationNormalizerV1
public import AsymptoticCongruenceTransvectionsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticFreshCRT
open scoped MatrixGroups

namespace QuantitativeMaass

theorem lowerHalf_conjugate_mem (L : ℕ) (n : ℤ) (a : SL(2,ℤ))
    (ha : a∈CongruenceSubgroup.Gamma0 (4*L)) :
    lowerSL (2*L) n*a*(lowerSL (2*L) n)⁻¹∈CongruenceSubgroup.Gamma0 (4*L) := by
  obtain ⟨c,hc⟩ := (gamma0_mem_dvd (4*L) a).mp ha
  have hc' : a 1 0=4*((L:ℤ)*c) := by simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using hc
  obtain ⟨r,hr⟩ := halfTranslation_diagonal_difference a ((L:ℤ)*c) hc'
  apply (gamma0_mem_dvd (4*L) _).mpr
  rw [lowerSL_inv]
  refine ⟨c-n*r-(L:ℤ)*n^2*a 0 1,?_⟩
  change ((lowerSL (2*L) n).val*a.val*(lowerSL (2*L) (-n)).val) 1 0=_
  simp [lowerSL,lower,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hc']
  linear_combination -(2:ℤ)*L*n*hr

theorem lowerHalfLabel_conj_mem (L : ℕ) (n : ℤ)
    {b : AsymptoticRationalGroup.Group} (hb : b∈gamma (4*L)) :
    integralLabel (lowerSL (2*L) n)*b*(integralLabel (lowerSL (2*L) n))⁻¹∈gamma (4*L) := by
  obtain ⟨a,ha,rfl⟩ := hb
  rw [←map_inv,←map_mul,←map_mul]
  exact ⟨_,lowerHalf_conjugate_mem L n a ha,rfl⟩

theorem lowerHalfLabel_inv_conj_mem (L : ℕ) (n : ℤ)
    {b : AsymptoticRationalGroup.Group} (hb : b∈gamma (4*L)) :
    (integralLabel (lowerSL (2*L) n))⁻¹*b*integralLabel (lowerSL (2*L) n)∈gamma (4*L) := by
  have h := lowerHalfLabel_conj_mem L (-n) hb
  simpa only [←map_inv,lowerSL_inv,neg_neg] using h

#print axioms lowerHalf_conjugate_mem
#print axioms lowerHalfLabel_conj_mem
#print axioms lowerHalfLabel_inv_conj_mem

end QuantitativeMaass
