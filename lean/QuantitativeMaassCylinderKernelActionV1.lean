module

public import QuantitativeMaassCylinderConjugationV1
public import QuantitativeMaassConjugatedKernelV1
public import QuantitativeMaassContinuousRadialUnfoldV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Exact integral action of the bounded capped operator on arbitrary
weighted cylinder L2 inputs. -/
theorem cylinderCappedRadialOperator_kernel_coeFn (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (ε : ℝ) (hε : 0<ε) (t : ℕ) (f : Lp ℂ 2 (quotientMeasure 0)) :
    cylinderCappedRadialOperator g hg R hR hs ε hε t f=ᵐ[quotientMeasure 0]
      (fun x => (cappedHeightWeight ε t x:ℂ)*
        (radialKernelData 0 g hg R hR hs).output
          (fun y => (Real.exp (-Real.log (cappedHeightWeight ε t y)):ℂ)*f y) x) := by
  have hk : ∀ (n m : ℤ),(⌈(t:ℝ)*R+1⌉₊:ℤ) < |n-m| →
      ∀ x∈LogBands.region (fun z => Real.log (cappedHeightWeight ε t z)) n,
      ∀ y∈LogBands.region (fun z => Real.log (cappedHeightWeight ε t z)) m,
      (radialKernelData 0 g hg R hR hs).kernel x y=0 := by
    intro n m hnm x hx y hy
    apply cylinder_radial_kernel_band_zero g R hR hs hε t n m x y hx hy
    have hh : (⌈(t:ℝ)*R+1⌉₊:ℝ) < |(n:ℝ)-(m:ℝ)| := by exact_mod_cast hnm
    exact (Nat.le_ceil _).trans hh.le
  have hh := LogBands.boundedConjugation_kernel_coeFn (quotientMeasure 0)
    (fun z => Real.log (cappedHeightWeight ε t z)) (cappedHeightWeight_log_measurable ε t)
    (radialKernelData 0 g hg R hR hs) ⌈(t:ℝ)*R+1⌉₊
    (cylinder_radial_band_propagation g hg R hR hs hε t _ (Nat.le_ceil _)) hk f
  simpa only [Real.exp_log (cappedHeightWeight_pos hε t _)] using! hh

theorem cappedHeightWeight_inverse_cancel {ε : ℝ} (hε : 0<ε) (t : ℕ) (y : ℍ) (a : ℂ) :
    (Real.exp (-Real.log (cappedHeightWeight ε t y)):ℂ)*((cappedHeightWeight ε t y:ℂ)*a)=a := by
  rw [Real.exp_neg,Real.exp_log (cappedHeightWeight_pos hε t y),Complex.ofReal_inv,
    ←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (cappedHeightWeight_pos hε t y).ne'),one_mul]

/-- The operator acts on the literal original Euler function by hyperbolic
radial convolution, despite possible failure of unweighted global L2.
This establishes integral action; its spectral eigenvalue still needs proof. -/
theorem cylinderCappedRadialOperator_original {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) :
    cylinderCappedRadialOperator g hg R hR hs P.ε P.epsilon_pos (P.s+3)
      (principalEulerCylinderLp hN A P r σ hb)=ᵐ[quotientMeasure 0]
      (fun x => (cappedHeightWeight P.ε (P.s+3) x:ℂ)*
        ∫ y : ℍ,g (Real.cosh (dist y x))*principalEulerPhysical b r σ y) := by
  let f := principalEulerCylinderLp hN A P r σ hb
  have he : (fun y => (Real.exp (-Real.log (cappedHeightWeight P.ε (P.s+3) y)):ℂ)*f y)=ᵐ[quotientMeasure 0]
      (fun y => principalEulerPhysical b r σ y) := by
    filter_upwards [principalEulerCylinderLp_coeFn hN A P r σ hb] with y hy
    change f y=AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0 (principalEulerPhysical b r σ) y at hy
    rw [hy,weighted_zero_eq_capped,cappedHeightWeight_inverse_cancel P.epsilon_pos]
  have ho := (radialKernelData 0 g hg R hR hs).output_congr_ae he
  filter_upwards [cylinderCappedRadialOperator_kernel_coeFn g hg R hR hs P.ε P.epsilon_pos (P.s+3) f]
    with x hx
  rw [hx,ho]
  rw [(continuous_radial_output_unfold 0 g hg R hR hs
    (fun y => principalEulerPhysical b r σ y)
    (principalEulerPhysical_continuous_upper hb.polynomialGrowth r σ)
    (principalEulerPhysical_cylinder_invariant b r σ) x).2.2]

#print axioms cylinderCappedRadialOperator_kernel_coeFn
#print axioms cappedHeightWeight_inverse_cancel
#print axioms cylinderCappedRadialOperator_original

end QuantitativeMaass
