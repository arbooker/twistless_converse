module

public import QuantitativeMaassStationaryMeanV1
public import QuantitativeMaassHighCuspKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace MatrixGroups

namespace QuantitativeMaass

/-- Actual invariant Hilbert columns have the common cusp period. -/
theorem cuspColumn_log_periodic (N : ℕ) (c : ℍ → AutomorphicSpace N)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z) (A : SL(2,ℤ)) (u : ℝ) :
    Function.Periodic (fun x => c (cuspLogPoint N A u x)) 1 := by
  intro x
  apply ext_inner_right ℂ
  intro v
  have hh := cuspProfile_periodic N A (fun z => inner ℂ (c z) v)
    (fun γ z => congrArg (fun q => inner ℂ q v) (hinv γ z)) (Real.exp u) x
  simpa only [cuspProfile,dite_eq_left (Real.exp_pos u),cuspLogPoint,
    MulAction.compHom_smul_def] using hh

theorem cuspLogPoint_add (N : ℕ) (A : SL(2,ℤ)) (u x r : ℝ) :
    cuspLogPoint N A u (x+r)=A•(((N:ℝ)*r)+ᵥ
      horocyclePoint ((N:ℝ)*x) (Real.exp u) (Real.exp_pos u)) := by
  unfold cuspLogPoint
  congr 1
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (N:ℝ)*(x+r)=(N:ℝ)*r+(N:ℝ)*x
    ring
  · exact (vadd_im _ _).symm

/-- A genuine compact radial column kernel is stationary along high cusps. -/
theorem cuspColumn_high_stationary (N : ℕ) (c : ℍ → AutomorphicSpace N)
    (g : ℝ → ℂ) (hk : ∀ z w,inner ℂ (c z) (c w)=radialPoincareKernel N g w z)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (A : SL(2,ℤ)) (u : ℝ) (hu : R/2<u) (r x y : ℝ) :
    inner ℂ (c (cuspLogPoint N A u (x+r))) (c (cuspLogPoint N A u (y+r)))=
      inner ℂ (c (cuspLogPoint N A u x)) (c (cuspLogPoint N A u y)) := by
  rw [hk,hk,cuspLogPoint_add,cuspLogPoint_add]
  exact radialPoincareKernel_high_cusp_translation N A g R hR hs
    (horocyclePoint ((N:ℝ)*x) (Real.exp u) (Real.exp_pos u))
    (horocyclePoint ((N:ℝ)*y) (Real.exp u) (Real.exp_pos u)) rfl
    (Real.exp_lt_exp.mpr hu) ((N:ℝ)*r)

/-- Exact cancellation of the period-average term in a high cusp. The kernel
on the right is the original radial Poincare kernel, with no trace hypothesis. -/
theorem cuspColumn_high_centered_kernel (N : ℕ) (c : ℍ → AutomorphicSpace N)
    (hc : Continuous c) (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (g : ℝ → ℂ) (hk : ∀ z w,inner ℂ (c z) (c w)=radialPoincareKernel N g w z)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (A : SL(2,ℤ)) (u : ℝ) (hu : R/2<u) (x : ℝ) :
    ‖c (cuspLogPoint N A u x)-cuspColumnMean N c A u‖^2=
      ‖c (cuspLogPoint N A u x)‖^2-
      (∫ y in Icc (0:ℝ) 1,radialPoincareKernel N g
        (cuspLogPoint N A u y) (cuspLogPoint N A u x)).re := by
  have hcont : Continuous (fun x => c (cuspLogPoint N A u x)) :=
    hc.comp ((cuspLogPoint_continuous N A).comp (continuous_const.prodMk continuous_id))
  have hh := stationary_column_centered_norm _ hcont (cuspColumn_log_periodic N c hinv A u)
    (cuspColumn_high_stationary N c g hk R hR hs A u hu) x
  simpa only [hk,cuspColumnMean] using hh

#print axioms cuspColumn_log_periodic
#print axioms cuspLogPoint_add
#print axioms cuspColumn_high_stationary
#print axioms cuspColumn_high_centered_kernel

end QuantitativeMaass
