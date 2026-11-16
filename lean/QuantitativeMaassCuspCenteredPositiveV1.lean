module

public import QuantitativeMaassPositiveParabolicResiduesV1
public import QuantitativeMaassCuspCenteredVariationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace MatrixGroups FourierTransform

namespace QuantitativeMaass

/-- The actual centered cusp column is controlled by positive nonzero
Fourier mass, with an explicit count of admissible parabolic residues. -/
theorem cuspColumn_high_centered_positive (N : ℕ) [NeZero N] (hN : 0<N)
    (c : ℍ → AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (g : ℝ → ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1))
    (hr : ∀ v,star (g v)=g v)
    (hp : ∀ ξ,0≤(𝓕 (parabolicLineProfile g 1) ξ).re)
    (hk : ∀ z w,inner ℂ (c z) (c w)=radialPoincareKernel N g w z)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (A : SL(2,ℤ)) (u : ℝ) (hu : R/2<u) (x : ℝ) :
    ‖c (cuspLogPoint N A u x)-cuspColumnMean N c A u‖^2≤
      2*(Fintype.card (cuspAdmissibleResidues N A):ℝ)*
        (2*(Real.exp u/(N:ℝ))*(∑' n : ℕ,(𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(Real.exp u/(N:ℝ)))).re)) := by
  classical
  let F : ℝ → ℂ := fun y => radialPoincareKernel N g
    (cuspLogPoint N A u y) (cuspLogPoint N A u x)
  let M : ℂ := Fintype.card (cuspAdmissibleResidues N A) •
    ((N:ℝ)⁻¹ • ∫ v,parabolicLineProfile g (Real.exp u) v)
  let D : ℝ := (Fintype.card (cuspAdmissibleResidues N A):ℝ)*
    (2*(Real.exp u/(N:ℝ))*(∑' n : ℕ,(𝓕 (parabolicLineProfile g 1) (((n:ℝ)+1)*(Real.exp u/(N:ℝ)))).re))
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
    exact parabolic_positive_residue_bound N hN A g hg (Real.cosh R) hs hr hp
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

#print axioms cuspColumn_high_centered_positive

end QuantitativeMaass
