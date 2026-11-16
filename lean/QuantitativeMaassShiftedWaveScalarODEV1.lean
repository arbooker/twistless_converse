module

public import QuantitativeMaassShiftedWaveScalarV1
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeMaass.Wave

/-- Time velocity of the signed cosine, valid on ordinary and exceptional energies. -/
def signedVelocity (t x : ℝ) : ℝ :=
  -Real.sqrt x*Real.sin (t*Real.sqrt x)+
    Real.sqrt (-x)*Real.sinh (t*Real.sqrt (-x))

theorem signedCosine_hasDerivAt (t x : ℝ) :
    HasDerivAt (fun u => signedCosine u x) (signedVelocity t x) t := by
  have h := ((((hasDerivAt_id t).mul_const (Real.sqrt x)).cos).add
    (((hasDerivAt_id t).mul_const (Real.sqrt (-x))).cosh)).sub_const 1
  convert h using 1 <;> simp [signedCosine,signedVelocity]
  ring

theorem signedVelocity_hasDerivAt (t x : ℝ) :
    HasDerivAt (fun u => signedVelocity u x) (-x*signedCosine t x) t := by
  have h := ((((hasDerivAt_id t).mul_const (Real.sqrt x)).sin).const_mul (-Real.sqrt x)).add
    ((((hasDerivAt_id t).mul_const (Real.sqrt (-x))).sinh).const_mul (Real.sqrt (-x)))
  have he : -Real.sqrt x*(Real.cos (t*Real.sqrt x)*(1*Real.sqrt x))+
      Real.sqrt (-x)*(Real.cosh (t*Real.sqrt (-x))*(1*Real.sqrt (-x)))=
      -x*signedCosine t x := by
    rcases le_total 0 x with hx | hx
    · rw [Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hx),
        signedCosine_nonneg_energy t x hx]
      have hs := Real.sq_sqrt hx
      nlinarith [congrArg (fun a : ℝ => a*Real.cos (t*Real.sqrt x)) hs]
    · rw [Real.sqrt_eq_zero_of_nonpos hx,signedCosine_nonpos_energy t x hx]
      have hs := Real.sq_sqrt (neg_nonneg.mpr hx)
      nlinarith [congrArg (fun a : ℝ => a*Real.cosh (t*Real.sqrt (-x))) hs]
  exact he ▸ h

theorem signedVelocity_zero (x : ℝ) : signedVelocity 0 x=0 := by
  simp [signedVelocity]

/-- Pointwise first derivative after two resolvents. -/
theorem twiceShiftedDamped_hasDerivAt (t : ℝ) {s : ℝ} (hs : 0≤s) (hs1 : s≤1) :
    HasDerivAt (fun u => shiftedDampedCosine u s*s)
      (s^2*signedVelocity t (s⁻¹-1-1/4)) t := by
  by_cases hz : s=0
  · subst s
    simpa using hasDerivAt_const t (0:ℝ)
  have hspos : 0<s := lt_of_le_of_ne hs (Ne.symm hz)
  have h := (signedCosine_hasDerivAt t (s⁻¹-1-1/4)).const_mul (s^2)
  convert h using 1
  funext u
  rw [shiftedDampedCosine_on_spectrum u s hspos hs1]
  ring

/-- Pointwise acceleration simplifies to a continuous resolvent multiplier. -/
theorem twiceShiftedVelocity_hasDerivAt (t : ℝ) {s : ℝ} (hs : 0≤s) (hs1 : s≤1) :
    HasDerivAt (fun u => s^2*signedVelocity u (s⁻¹-1-1/4))
      (shiftedDampedCosine t s*((5/4)*s-1)) t := by
  by_cases hz : s=0
  · subst s
    simpa [shiftedDampedCosine] using hasDerivAt_const t (0:ℝ)
  have hspos : 0<s := lt_of_le_of_ne hs (Ne.symm hz)
  have h := (signedVelocity_hasDerivAt t (s⁻¹-1-1/4)).const_mul (s^2)
  convert h using 1
  rw [shiftedDampedCosine_on_spectrum t s hspos hs1]
  field_simp
  ring

#print axioms signedVelocity_hasDerivAt
#print axioms twiceShiftedVelocity_hasDerivAt

end QuantitativeMaass.Wave
