module

public import QuantitativeMaassParabolicResidueErrorV1
public import QuantitativeMaassCuspCenteredKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace MatrixGroups

namespace QuantitativeMaass

/-- Subtracting a unit-period average doubles a uniform deviation bound. -/
theorem unit_average_centering_bound (f : ℝ → ℂ) (hf : Continuous f)
    (C : ℂ) (D z : ℝ) (hz : ‖f z-C‖≤D) (hb : ∀ x∈Icc (0:ℝ) 1,‖f x-C‖≤D) :
    ‖f z-∫ x in Icc (0:ℝ) 1,f x‖≤2*D := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
  have he : (∫ x in (0:ℝ)..1,f z-f x)=f z-∫ x in (0:ℝ)..1,f x := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _),intervalIntegral.integral_const]
    simp
  rw [←he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (f:=fun x => f z-f x) (C:=2*D) (fun x hx => by
      rw [uIoc_of_le zero_le_one] at hx
      have h := norm_sub_le_norm_sub_add_norm_sub (f z) C (f x)
      rw [norm_sub_rev C (f x)] at h
      exact h.trans (by linarith [hb x ⟨hx.1.le,hx.2⟩]))
  simpa using hh

/-- Centered high-cusp column energy is bounded by twice the number of
admissible residues times the height-one radial variation. All group sums,
period averaging and lattice errors are derived from the actual kernel. -/
theorem cuspColumn_high_centered_variation (N : ℕ) [NeZero N] (hN : 0<N)
    (c : ℍ → AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (g : ℝ → ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1))
    (hk : ∀ z w,inner ℂ (c z) (c w)=radialPoincareKernel N g w z)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (A : SL(2,ℤ)) (u : ℝ) (hu : R/2<u) (x : ℝ) :
    ‖c (cuspLogPoint N A u x)-cuspColumnMean N c A u‖^2≤
      2*(Fintype.card (cuspAdmissibleResidues N A):ℝ)*
        ∫ v,‖deriv (parabolicLineProfile g 1) v‖ := by
  classical
  let F : ℝ → ℂ := fun y => radialPoincareKernel N g
    (cuspLogPoint N A u y) (cuspLogPoint N A u x)
  let M : ℂ := Fintype.card (cuspAdmissibleResidues N A) •
    ((N:ℝ)⁻¹ • ∫ v,parabolicLineProfile g (Real.exp u) v)
  let D : ℝ := (Fintype.card (cuspAdmissibleResidues N A):ℝ)*
    ∫ v,‖deriv (parabolicLineProfile g 1) v‖
  have he : F=fun y => inner ℂ (c (cuspLogPoint N A u x)) (c (cuspLogPoint N A u y)) := by
    funext y
    exact (hk _ _).symm
  have hF : Continuous F := by
    rw [he]
    exact continuous_const.inner (hc.comp ((cuspLogPoint_continuous N A).comp
      (continuous_const.prodMk continuous_id)))
  have hb (y : ℝ) : ‖F y-M‖≤D := by
    dsimp only [F]
    rw [radialPoincareKernel_high_cusp_line_sum N A g R hR hs u hu x y]
    exact parabolic_residue_sum_discrepancy N hN A g hg (Real.cosh R) hs
      (Real.exp u) ((N:ℝ)*(x-y)) (Real.exp_pos u)
  have hnorm := unit_average_centering_bound F hF M D x (hb x) (fun y _ => hb y)
  have hdiag : ‖c (cuspLogPoint N A u x)‖^2=(F x).re := by
    rw [he]
    exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm
  have hcen := cuspColumn_high_centered_kernel N c hc hinv g hk R hR hs A u hu x
  change ‖c (cuspLogPoint N A u x)-cuspColumnMean N c A u‖^2=
    ‖c (cuspLogPoint N A u x)‖^2-(∫ y in Icc (0:ℝ) 1,F y).re at hcen
  rw [hdiag,←Complex.sub_re] at hcen
  calc
    _ = (F x-∫ y in Icc (0:ℝ) 1,F y).re := hcen
    _ ≤ ‖F x-∫ y in Icc (0:ℝ) 1,F y‖ := Complex.re_le_norm _
    _ ≤ 2*D := hnorm
    _ = _ := by dsimp only [D];ring

#print axioms unit_average_centering_bound
#print axioms cuspColumn_high_centered_variation

end QuantitativeMaass
