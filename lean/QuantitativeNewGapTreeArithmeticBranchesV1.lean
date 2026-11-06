module

public import QuantitativeNewGapTreeArithmeticHeckeV1
public import AsymptoticClassicalHeckeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticNestedQuotients AsymptoticAtkinLehner AsymptoticClassicalCusp
open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open scoped MatrixGroups BigOperators lp

/-- The literal upper triangular good-prime representative. -/
def upperHeckeGL (p : ℕ) (hp : 0 < p) (a : ℤ) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![1,(a : ℚ);0,(p : ℚ)] (by
    simpa [Matrix.det_fin_two] using (show (p : ℚ) ≠ 0 by exact_mod_cast hp.ne'))

theorem upperHeckeGL_positive (p : ℕ) (hp : 0 < p) (a : ℤ) :
    0 < (realMatrix (upperHeckeGL p hp a)).det.val := by
  change 0 < ((!![1,(a : ℚ);0,(p : ℚ)]).map (algebraMap ℚ ℝ)).det
  simpa [Matrix.det_fin_two] using (show (0 : ℝ) < p by exact_mod_cast hp)

def upperHeckeLabel (p : ℕ) (hp : 0 < p) (a : ℤ) : AsymptoticRationalGroup.Group :=
  ofMatrix (upperHeckeGL p hp a) (upperHeckeGL_positive p hp a)

/-- The trace representatives become the actual upper triangular Hecke
matrices after dilation and multiplication by an integral level matrix. -/
theorem dilation_trace_label (M p : ℕ) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1) (a : ℤ) :
    dilationLabel p hp * integralLabel (traceSL M p A B hAB a) =
      integralLabel (heckeSL M p A B hAB) * upperHeckeLabel p hp a := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (dilationGL p hp) * rationalMap (rationalGL (traceSL M p A B hAB a)) =
    rationalMap (rationalGL (heckeSL M p A B hAB)) * rationalMap (upperHeckeGL p hp a)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  change (dilationGL p hp).val * (traceSL M p A B hAB a).val.map (fun z : ℤ => (z : ℚ)) =
    (heckeSL M p A B hAB).val.map (fun z : ℤ => (z : ℚ)) * (upperHeckeGL p hp a).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationGL, upperHeckeGL, GeneralLinearGroup.mkOfDetNeZero, traceSL, heckeSL,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Both matrix descriptions give exactly the same second-old coset,
with the inverse dilation required by its conjugated subgroup. -/
theorem trace_upper_coset (M p : ℕ) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1) (a : ℤ) (g : AsymptoticRationalGroup.Group) :
    classOf (degeneracyGroup M p hp) (integralLabel (traceSL M p A B hAB a)*g) =
      classOf (degeneracyGroup M p hp) ((dilationLabel p hp)⁻¹*upperHeckeLabel p hp a*g) := by
  let D := dilationLabel p hp
  let j := integralLabel (heckeSL M p A B hAB)
  have hj : j ∈ gamma M := ⟨heckeSL M p A B hAB, heckeSL_mem M p A B hAB, rfl⟩
  let k : degeneracyGroup M p hp := ⟨D⁻¹*j*D, ⟨j,hj,by
    change D⁻¹*j*(D⁻¹)⁻¹ = D⁻¹*j*D
    rw [inv_inv]⟩⟩
  have he : integralLabel (traceSL M p A B hAB a)*g =
      k.val*((dilationLabel p hp)⁻¹*upperHeckeLabel p hp a*g) := by
    have hh := dilation_trace_label M p hp A B hAB a
    have hh' : integralLabel (traceSL M p A B hAB a) = D⁻¹*j*upperHeckeLabel p hp a := by
      apply (mul_left_cancel (a := D))
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
    rw [hh']
    dsimp only [k, D]
    group
  rw [he]
  exact classOf_mul _ k _

/-- Exact Hecke expansion of the old cross Gram on the actual regular
coset Hilbert spaces. No tree identification or spectral bound is assumed. -/
theorem old_cross_gram_hecke (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) (A B : ℤ) (hAB : (p : ℤ)*A+(M : ℤ)*B=1)
    (f : ℓ²(Classes (degeneracyGroup M p (Fact.out : p.Prime).pos), ℂ))
    (g : AsymptoticRationalGroup.Group) :
    ((isometry (gamma_le_of_dvd (Nat.dvd_mul_left M p))).toContinuousLinearMap.adjoint
      (isometry (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
        (Fact.out : p.Prime).pos) f)) (classOf (gamma M) g) =
      ((p+1 : ℕ) : ℂ)⁻¹ *
        (f (classOf (degeneracyGroup M p (Fact.out : p.Prime).pos) g) +
          ∑ a : Fin p, f (classOf (degeneracyGroup M p (Fact.out : p.Prime).pos)
            ((dilationLabel p (Fact.out : p.Prime).pos)⁻¹ *
              upperHeckeLabel p (Fact.out : p.Prime).pos a.val * g))) := by
  rw [old_cross_gram_trace M p hpM A B hAB]
  simp_rw [trace_upper_coset]

#print axioms dilation_trace_label
#print axioms trace_upper_coset
#print axioms old_cross_gram_hecke

end QuantitativeNewGap
