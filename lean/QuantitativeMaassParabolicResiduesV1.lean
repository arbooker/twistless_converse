module

public import QuantitativeMaassParabolicLatticeSpacingV1
public import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups

namespace QuantitativeMaass

abbrev cuspAdmissibleResidues (N : ℕ) (A : SL(2,ℤ)) :=
  {r : Fin N // (N:ℤ)∣(r.val:ℤ)*(A 1 0)^2}

theorem cusp_admissible_quotient_remainder (N : ℕ) (A : SL(2,ℤ)) (k r : ℤ) :
    (N:ℤ)∣(k*N+r)*(A 1 0)^2 ↔ (N:ℤ)∣r*(A 1 0)^2 := by
  have hd : (N:ℤ)∣(k*N)*(A 1 0)^2 := ⟨k*(A 1 0)^2,by ring⟩
  rw [add_mul]
  constructor
  · intro h
    simpa only [add_sub_cancel_left] using dvd_sub h hd
  · intro h
    exact dvd_add hd h

/-- Exact Euclidean-division coordinates on the actual admissible translations. -/
def cuspParabolicResidueEquiv (N : ℕ) [NeZero N] (A : SL(2,ℤ)) :
    {n : ℤ // (N:ℤ)∣n*(A 1 0)^2} ≃ ℤ × cuspAdmissibleResidues N A where
  toFun n :=
    let p := Int.divModEquiv N n.val
    (p.1,⟨p.2,by
      apply (cusp_admissible_quotient_remainder N A p.1 p.2.val).mp
      have he : p.1*N+(p.2.val:ℤ)=n.val := (Int.divModEquiv N).symm_apply_apply n.val
      rw [he]
      exact n.property⟩)
  invFun p := ⟨p.1*N+(p.2.val.val:ℤ),
    (cusp_admissible_quotient_remainder N A p.1 p.2.val.val).mpr p.2.property⟩
  left_inv n := Subtype.ext ((Int.divModEquiv N).symm_apply_apply n.val)
  right_inv p := by
    have he := (Int.divModEquiv N).apply_symm_apply (p.1,p.2.val)
    apply Prod.ext
    · change (Int.divModEquiv N (p.1*N+(p.2.val.val:ℤ))).1=p.1
      exact congrArg (fun q : ℤ × Fin N => q.1) he
    · apply Subtype.ext
      change (Int.divModEquiv N (p.1*N+(p.2.val.val:ℤ))).2=p.2.val
      exact congrArg (fun q : ℤ × Fin N => q.2) he

/-- The actual parabolic sum splits into integer lattices, one for each
admissible residue class. No convergence hypothesis is needed to reindex. -/
theorem cusp_parabolic_sum_residues (N : ℕ) [NeZero N] (A : SL(2,ℤ)) (f : ℤ → ℂ) :
    (∑' n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2},f n.val)=
      ∑' p : ℤ × cuspAdmissibleResidues N A,f (p.1*N+(p.2.val.val:ℤ)) :=
  ((cuspParabolicResidueEquiv N A).symm.tsum_eq (fun n => f n.val)).symm

#print axioms cusp_admissible_quotient_remainder
#print axioms cusp_parabolic_sum_residues

end QuantitativeMaass
