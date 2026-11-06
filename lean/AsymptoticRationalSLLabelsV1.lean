module

public import AsymptoticLocalCongruenceIntegralV1
public import AsymptoticProjectiveIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticLocalCongruence

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open scoped MatrixGroups

theorem rationalSL_positive (A : SL(2,ℚ)) : 0<(realMatrix (SpecialLinearGroup.toGL A)).det.val := by
  change 0<(A.val.map (fun r : ℚ => (r:ℝ))).det
  rw [← Rat.cast_det,A.property,Rat.cast_one]
  norm_num

/-- The determinant-one rational group mapped to the same positive
projective orbit group used throughout the analytic proof. -/
noncomputable def rationalSLLabel : SL(2,ℚ) →* AsymptoticRationalGroup.Group where
  toFun A := ofMatrix (SpecialLinearGroup.toGL A) (rationalSL_positive A)
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (rationalMap.comp SpecialLinearGroup.toGL)
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (rationalMap.comp SpecialLinearGroup.toGL) A B

theorem rationalSLLabel_integral (B : SL(2,ℤ)) :
    rationalSLLabel (SpecialLinearGroup.map (Int.castRingHom ℚ) B)=integralLabel B := rfl

theorem rationalSLLabel_ker_lower (A : SL(2,ℚ)) (hA : A∈rationalSLLabel.ker) : A.val 1 0=0 := by
  have he : ProjGenLinGroup.mk (realMatrix (SpecialLinearGroup.toGL A))=1 :=
    congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) hA
  have hc := ProjGenLinGroup.mk_eq_one.mp he
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u,hu⟩ := hc
  have h10 := congrArg (fun B : GL (Fin 2) ℝ => B.val 1 0) hu
  change (0:ℝ)=(A.val 1 0:ℝ) at h10
  exact_mod_cast h10.symm

/-- Scalar rational special-linear matrices satisfy every local
congruence condition, so passage to projective labels preserves meets. -/
theorem rationalSLLabel_ker_le (N : ℕ) (S : Set ℕ) : rationalSLLabel.ker ≤ outside N S := by
  intro A hA
  have he : rationalMap (SpecialLinearGroup.toGL A)=rationalMap (rationalGL (1:SL(2,ℤ))) := by
    have hh := congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) hA
    change rationalMap (SpecialLinearGroup.toGL A)=1 at hh
    simpa only [map_one] using hh
  rw [mem_outside]
  intro q hq _
  let : Fact q.Prime := ⟨hq⟩
  constructor
  · intro i j
    obtain ⟨a,ha⟩ := projective_det_one_integral (SpecialLinearGroup.toGL A) A.property 1 he i j
    rw [show A.val i j=(a:ℚ) from ha]
    exact padicNorm.of_int a
  · change padicNorm q (A.val 1 0/(N:ℚ))≤1
    rw [rationalSLLabel_ker_lower A hA,zero_div,padicNorm.zero]
    norm_num

#print axioms rationalSL_positive
#print axioms rationalSLLabel_integral
#print axioms rationalSLLabel_ker_lower
#print axioms rationalSLLabel_ker_le

end AsymptoticLocalCongruence
