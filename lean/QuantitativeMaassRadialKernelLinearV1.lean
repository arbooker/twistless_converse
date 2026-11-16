module

public import QuantitativeMaassRadialKernelOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem radialPoincareKernel_linear (N : ℕ) (g h j : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (R : ℝ) (hR : 0≤R)
    (hsg : Function.support g⊆Iic (Real.cosh R))
    (hsh : Function.support h⊆Iic (Real.cosh R))
    (c : ℂ) (he : ∀ q,j q=c*g q-h q) (x y : ℍ) :
    radialPoincareKernel N j x y=c*radialPoincareKernel N g x y-radialPoincareKernel N h x y := by
  have hgS : Summable (fun γ : gamma N => upperFunction (radialFunction g x) (γ•y)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support _ (radialSeed g hg x R hR hsg).compact y)
  have hhS : Summable (fun γ : gamma N => upperFunction (radialFunction h x) (γ•y)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support _ (radialSeed h hh x R hR hsh).compact y)
  simp only [radialFunction_upper] at hgS hhS
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper,he]
  rw [(hgS.mul_left c).tsum_sub hhS,tsum_mul_left]

/-- Linearity in the literal radial profile follows from finite group
sums and the proved almost-everywhere absolute integrability of each row. -/
theorem radialKernelOperator_linear (N : ℕ) [NeZero N] (g h j : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hj : ContDiff ℝ ∞ j)
    (R : ℝ) (hR : 0≤R)
    (hsg : Function.support g⊆Iic (Real.cosh R))
    (hsh : Function.support h⊆Iic (Real.cosh R))
    (hsj : Function.support j⊆Iic (Real.cosh R))
    (c : ℂ) (he : ∀ q,j q=c*g q-h q) (f : AutomorphicSpace N) :
    radialKernelOperator N j hj R hR hsj f=
      c • radialKernelOperator N g hg R hR hsg f-radialKernelOperator N h hh R hR hsh f := by
  apply Subtype.ext
  apply Lp.ext
  let K := radialKernelOperator N g hg R hR hsg f
  let H := radialKernelOperator N h hh R hR hsh f
  filter_upwards [radialKernelOperator_coeFn N j hj R hR hsj f,
    radialKernelOperator_coeFn N g hg R hR hsg f,
    radialKernelOperator_coeFn N h hh R hR hsh f,
    Lp.coeFn_sub (c • K.val) H.val,Lp.coeFn_smul c K.val,
    (radialKernelData N g hg R hR hsg).output_row_ae f.val
      (Lp.stronglyMeasurable f.val).measurable (Lp.memLp f.val),
    (radialKernelData N h hh R hR hsh).output_row_ae f.val
      (Lp.stronglyMeasurable f.val).measurable (Lp.memLp f.val)] with x hx hgx hhx hsub hsmul hig hih
  change _=(c • K.val-H.val) x
  rw [hsub,Pi.sub_apply,hsmul]
  change _=c*K.val x-H.val x
  rw [hx,hgx,hhx]
  simp_rw [radialPoincareKernel_linear N g h j hg hh R hR hsg hsh c he,sub_mul,mul_assoc]
  have hig' : Integrable (fun y => radialPoincareKernel N g x y*f.val y) (quotientMeasure N) := hig.1
  have hih' : Integrable (fun y => radialPoincareKernel N h x y*f.val y) (quotientMeasure N) := hih.1
  rw [integral_sub (hig'.const_mul c) hih',integral_const_mul]

#print axioms radialPoincareKernel_linear
#print axioms radialKernelOperator_linear

end QuantitativeMaass
