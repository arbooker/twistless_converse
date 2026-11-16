module

public import QuantitativeMaassParabolicResiduesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups ContDiff

namespace QuantitativeMaass

/-- The actual congruence-restricted parabolic sum has a height-independent
variation error, with at most one contribution per admissible residue. -/
theorem parabolic_residue_sum_discrepancy (N : ℕ) [NeZero N] (hN : 0<N) (A : SL(2,ℤ))
    (g : ℝ → ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ)
    (hs : Function.support g⊆Iic B) (y s : ℝ) (hy : 0<y) :
    ‖(∑' n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2},parabolicLineProfile g y ((n.val:ℝ)+s))-
      Fintype.card (cuspAdmissibleResidues N A) •
        ((N:ℝ)⁻¹ • ∫ v,parabolicLineProfile g y v)‖≤
      (Fintype.card (cuspAdmissibleResidues N A):ℝ)*
        ∫ v,‖deriv (parabolicLineProfile g 1) v‖ := by
  classical
  let S := cuspAdmissibleResidues N A
  let F : ℤ → ℂ := fun n => parabolicLineProfile g y ((n:ℝ)+s)
  let G : ℤ × S → ℂ := fun p => F (p.1*N+(p.2.val.val:ℤ))
  have hAll : Summable F := by
    simpa only [F,add_comm] using (parabolicLineProfile_lattice_discrepancy g hg B hs y hy s).1
  have hRest : Summable (fun n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2} => F n.val) :=
    hAll.subtype _
  have hP : Summable G := (cuspParabolicResidueEquiv N A).symm.summable_iff.mpr hRest
  have hsum : (∑' n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2},F n.val)=
      ∑ r : S,∑' k : ℤ,parabolicLineProfile g y ((s+(r.val.val:ℝ))+(N:ℝ)*k) := by
    rw [cusp_parabolic_sum_residues N A F]
    change (∑' p,G p)=_
    rw [←(Equiv.prodComm S ℤ).tsum_eq G]
    change (∑' p : S × ℤ,G p.swap)=_
    rw [hP.prod_symm.tsum_prod,tsum_fintype]
    apply Finset.sum_congr rfl
    intro r _
    apply tsum_congr
    intro k
    dsimp only [G,F,Prod.swap]
    congr 1
    push_cast
    ring
  change ‖(∑' n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2},F n.val)-_‖≤_
  rw [hsum]
  let M : ℂ := (N:ℝ)⁻¹ • ∫ v,parabolicLineProfile g y v
  let V : ℝ := ∫ v,‖deriv (parabolicLineProfile g 1) v‖
  have hb (r : S) : ‖(∑' k : ℤ,parabolicLineProfile g y ((s+(r.val.val:ℝ))+(N:ℝ)*k))-M‖≤V :=
    (parabolicLineProfile_spacing_discrepancy g hg B hs y N (s+(r.val.val:ℝ)) hy
      (Nat.cast_pos.mpr hN)).2
  have he : (∑ r : S,((∑' k : ℤ,parabolicLineProfile g y ((s+(r.val.val:ℝ))+(N:ℝ)*k))-M))=
      (∑ r : S,∑' k : ℤ,parabolicLineProfile g y ((s+(r.val.val:ℝ))+(N:ℝ)*k))-
      Fintype.card S • M := by rw [Finset.sum_sub_distrib];simp
  rw [←he]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun r _ => hb r)).trans_eq (by simp [nsmul_eq_mul,S,V]))

#print axioms parabolic_residue_sum_discrepancy

end QuantitativeMaass
