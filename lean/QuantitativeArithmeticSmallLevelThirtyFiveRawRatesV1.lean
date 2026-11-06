module

public import QuantitativeArithmeticSmallLevelThirtyFiveRawWordsV1
public import QuantitativeArithmeticSmallLevelThirtyFiveWordGridGermsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Matrix Complex

def rawA (w : Word) : ℝ := raw w 0 0
def rawB (w : Word) : ℝ := raw w 0 1
def rawC (w : Word) : ℝ := raw w 1 0
def rawD (w : Word) : ℝ := raw w 1 1
def rawDen (w : Word) (t : ℤ) : ℝ := rawC w*((t:ℝ)/210)+rawD w

theorem raw_det_formula (w : Word) : (raw w).det=rawA w*rawD w-rawB w*rawC w := by
  simp only [Matrix.det_fin_two,rawA,rawB,rawC,rawD]

theorem raw_coordinates (w : Word) :
    coordA w=wordScale w*rawA w ∧ coordB w=wordScale w*rawB w ∧
    coordC w=wordScale w*rawC w ∧ coordD w=wordScale w*rawD w := by
  have hh (i j : Fin 2) := congrFun (congrFun (value_raw w) i) j
  exact ⟨hh 0 0,hh 0 1,hh 1 0,hh 1 1⟩

theorem wordDen_raw (w : Word) (t : ℤ) : wordDen w t=wordScale w*rawDen w t := by
  rw [wordDen,rawDen,(raw_coordinates w).2.2.1,(raw_coordinates w).2.2.2]
  ring

theorem raw_rate (w : Word) (t : ℤ) :
    (wordDen w t)^2=(rawDen w t)^2/(raw w).det := by
  rw [wordDen_raw]
  apply (eq_div_iff (raw_det_pos w).ne').mpr
  calc
    (wordScale w*rawDen w t)^2*(raw w).det=
        ((wordScale w)^2*(raw w).det)*(rawDen w t)^2 := by ring
    _ = (rawDen w t)^2 := by rw [raw_det_scale,one_mul]

theorem raw_derivative_rate (w : Word) (t : ℤ) :
    coordC w*wordDen w t=rawC w*rawDen w t/(raw w).det := by
  rw [wordDen_raw,(raw_coordinates w).2.2.1]
  apply (eq_div_iff (raw_det_pos w).ne').mpr
  calc
    (wordScale w*rawC w*(wordScale w*rawDen w t))*(raw w).det=
        ((wordScale w)^2*(raw w).det)*(rawC w*rawDen w t) := by ring
    _ = rawC w*rawDen w t := by rw [raw_det_scale,one_mul]

theorem raw_partner (w : Word) (t : ℤ) :
    (coordA w*((t:ℝ)/210)+coordB w)/wordDen w t=
      (rawA w*((t:ℝ)/210)+rawB w)/rawDen w t := by
  rw [(raw_coordinates w).1,(raw_coordinates w).2.1,wordDen_raw]
  rw [show wordScale w*rawA w*((t:ℝ)/210)+wordScale w*rawB w=
    wordScale w*(rawA w*((t:ℝ)/210)+rawB w) by ring]
  exact mul_div_mul_left _ _ (wordScale_pos w).ne'

theorem raw_C_ne_zero (w : Word) : coordC w≠0 ↔ rawC w≠0 := by
  rw [(raw_coordinates w).2.2.1,mul_ne_zero_iff]
  exact and_iff_right (wordScale_pos w).ne'

theorem raw_den_ne_zero (w : Word) (t : ℤ) : wordDen w t≠0 ↔ rawDen w t≠0 := by
  rw [wordDen_raw,mul_ne_zero_iff]
  exact and_iff_right (wordScale_pos w).ne'

/-- This is exactly the coefficient used by the rational projective-matrix
builder, including every positive Taylor coefficient. -/
theorem wordCoefficient_raw (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ) (n : ℕ) (s : ℂ) :
    wordCoefficient m χ w t n s=
      character χ w*(((rawDen w t)^2/(raw w).det:ℝ):ℂ)^(s-(m:ℂ))*
        (I*((rawC w*rawDen w t/(raw w).det:ℝ):ℂ))^n*
          Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  rw [wordCoefficient,raw_rate,raw_derivative_rate]

#print axioms raw_coordinates
#print axioms raw_rate
#print axioms raw_derivative_rate
#print axioms raw_partner
#print axioms wordCoefficient_raw
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
