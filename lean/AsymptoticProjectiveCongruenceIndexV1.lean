module

public import AsymptoticLowerLevelOldSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness
open scoped MatrixGroups

/-- Scalar integral labels already belong to every congruence subgroup.
Consequently passing to the projective action loses no relative index. -/
theorem integralLabel_ker_le (N : ℕ) : integralLabel.ker≤CongruenceSubgroup.Gamma0 N := by
  intro A hA
  have he : Matrix.ProjGenLinGroup.mk (realMatrix (rationalGL A))=1 :=
    congrArg (fun g : AsymptoticRationalGroup.Group => g.val.val) hA
  have hc := Matrix.ProjGenLinGroup.mk_eq_one.mp he
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u,hu⟩ := hc
  have he10 := congrArg (fun B : GL (Fin 2) ℝ => B.val 1 0) hu
  change (0:ℝ)=((A.val 1 0:ℚ):ℝ) at he10
  have hz : (A.val 1 0:ℝ)=0 := by
    simpa only [Rat.cast_intCast] using he10.symm
  have hz' : A.val 1 0=0 := by exact_mod_cast hz
  rw [CongruenceSubgroup.Gamma0_mem]
  simp only [hz',Int.cast_zero]

#print axioms integralLabel_ker_le

end AsymptoticCongruenceLabels

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels

theorem gamma_relIndex (N d : ℕ) : (gamma N).relIndex (gamma d)=
    (CongruenceSubgroup.Gamma0 N).relIndex (CongruenceSubgroup.Gamma0 d) := by
  rw [gamma,gamma,Subgroup.relIndex_map_map,
    sup_eq_left.mpr (integralLabel_ker_le N),sup_eq_left.mpr (integralLabel_ker_le d)]

#print axioms gamma_relIndex

end AsymptoticCongruenceStrip
