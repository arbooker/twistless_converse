module

public import QuantitativeMaassParabolicResiduesV1
public import QuantitativeMaassPositiveParabolicSpacingV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups ContDiff FourierTransform

namespace QuantitativeMaass

/-- Each actual admissible residue contributes at most the same positive
nonzero Fourier mass, uniformly in the horizontal shift. -/
theorem parabolic_positive_residue_bound (N : ℕ) [NeZero N] (hN : 0<N) (A : SL(2,ℤ))
    (g : ℝ → ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1)) (B : ℝ)
    (hs : Function.support g⊆Iic B)
    (hr : ∀ u,star (g u)=g u)
    (hp : ∀ ξ,0≤(𝓕 (parabolicLineProfile g 1) ξ).re) (y s : ℝ) (hy : 0<y) :
    ‖(∑' n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2},parabolicLineProfile g y ((n.val:ℝ)+s))-
      Fintype.card (cuspAdmissibleResidues N A) •
        ((N:ℝ)⁻¹ • ∫ v,parabolicLineProfile g y v)‖≤
      (Fintype.card (cuspAdmissibleResidues N A):ℝ)*
        (2*(y/(N:ℝ))*(∑' n : ℕ,(𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(y/(N:ℝ)))).re)) := by
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
  let V : ℝ := (2*(y/(N:ℝ))*(∑' n : ℕ,(𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(y/(N:ℝ)))).re))
  have hb (r : S) : ‖(∑' k : ℤ,parabolicLineProfile g y ((s+(r.val.val:ℝ))+(N:ℝ)*k))-M‖≤V :=
    parabolic_positive_spacing_bound g hg B hs hr hp y N (s+(r.val.val:ℝ)) hy
      (Nat.cast_pos.mpr hN)
  have he : (∑ r : S,((∑' k : ℤ,parabolicLineProfile g y ((s+(r.val.val:ℝ))+(N:ℝ)*k))-M))=
      (∑ r : S,∑' k : ℤ,parabolicLineProfile g y ((s+(r.val.val:ℝ))+(N:ℝ)*k))-
      Fintype.card S • M := by rw [Finset.sum_sub_distrib];simp
  rw [←he]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun r _ => hb r)).trans_eq (by simp [nsmul_eq_mul,S,V]))

#print axioms parabolic_positive_residue_bound

end QuantitativeMaass
