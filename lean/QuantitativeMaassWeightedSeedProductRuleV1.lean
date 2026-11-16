module

public import QuantitativeMaassQuotientWeightGradientV1
public import QuantitativeMaassQuotientWeightSeedLipschitzV1
public import QuantitativeMaassEnergyLocalizationV1
public import QuantitativeArithmeticMaassGradientExtensionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential QuantitativeArithmeticMaassGradient

/-- Multiplication by the literal invariant weight commutes with periodization
on the open upper half-plane, even though the weight is only Lipschitz. -/
theorem quotientWeight_seed_poincare_germ (N : ℕ) (ε : ℝ) (v : ℕ) (w : SmoothUpperSeed)
    (Z : Point) (hZ : 0<Z.2) :
    congruencePoincareCartesian N (fun W => (quotientWeightPlane N ε v W:ℂ)*
      upperSeedExtension (upperFunction w.toFun) W)=ᶠ[𝓝 Z]
      fun W => (quotientWeightPlane N ε v W:ℂ)*congruencePoincareCartesian N w.toFun W := by
  let f : Point → ℂ := fun W => (quotientWeightPlane N ε v W:ℂ)*
    upperSeedExtension (upperFunction w.toFun) W
  have hf : upperFunction f=(fun z => (weight N ε v z:ℂ)*upperFunction w.toFun z) := by
    funext z
    change (quotientWeightPlane N ε v (z.re,z.im):ℂ)*
      upperSeedExtension (upperFunction w.toFun) (z.re,z.im)=_
    rw [quotientWeightPlane_upper,upperSeedExtension_positive w.toFun _ z.im_pos]
    rfl
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW
  change poincareSum (G := gamma N) (upperFunction f) (cartesianLift W)=_
  rw [hf,poincareSum_mul_invariant (upperFunction w.toFun)
    (fun z => (weight N ε v z:ℂ))
    (fun g z => congrArg Complex.ofReal (weight_invariant N ε v g z))]
  change (weight N ε v (cartesianLift W):ℂ)*congruencePoincareCartesian N w.toFun W=_
  rw [cartesianLift_positive W hW]
  congr 1
  exact congrArg Complex.ofReal (quotientWeightPlane_upper N ε v (⟨⟨W.1,W.2⟩,hW⟩:ℍ)).symm

/-- The actual coordinate gradient obeys the product rule at each point where
the orbit weight is differentiable. -/
theorem quotientWeight_seed_gradient_product_at (N : ℕ) (ε : ℝ) (v : ℕ)
    (i : Bool) (w : SmoothUpperSeed) (z : ℍ)
    (hd : DifferentiableAt ℝ (quotientWeightPlane N ε v) (z.re,z.im)) :
    (z.im:ℂ)*dir (axis i)
      (congruencePoincareCartesian N (fun W => (quotientWeightPlane N ε v W:ℂ)*
        upperSeedExtension (upperFunction w.toFun) W)) (z.re,z.im)=
      (weight N ε v z:ℂ)*seedGradient N i w z+
      quotientWeightGradientColumn N ε v i z*
        poincareSum (G := gamma N) (upperFunction w.toFun) z := by
  have hb : HasFDerivAt (fun W => (quotientWeightPlane N ε v W:ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (quotientWeightPlane N ε v) (z.re,z.im)))
      (z.re,z.im) := Complex.ofRealCLM.hasFDerivAt.comp (z.re,z.im) hd.hasFDerivAt
  have hp : DifferentiableAt ℝ (congruencePoincareCartesian N w.toFun) (z.re,z.im) :=
    ((congruencePoincareCartesian_smooth N w.smooth w.compact).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos)).differentiableAt (by simp)
  have he := (quotientWeight_seed_poincare_germ N ε v w (z.re,z.im) z.im_pos).fderiv_eq (𝕜 := ℝ)
  rw [(hb.fun_mul hp.hasFDerivAt).fderiv] at he
  have hval := congrArg (fun D : Point →L[ℝ] ℂ => D (axis i)) he
  simp only [add_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,quotientWeightPlane_upper] at hval
  unfold dir D
  rw [hval]
  change (z.im:ℂ)*((weight N ε v z:ℂ)*
      (fderiv ℝ (congruencePoincareCartesian N w.toFun) (z.re,z.im)) (axis i)+
      congruencePoincareCartesian N w.toFun (z.re,z.im)*
        ((fderiv ℝ (quotientWeightPlane N ε v) (z.re,z.im)) (axis i):ℂ))=
    (weight N ε v z:ℂ)*((z.im:ℂ)*
      (fderiv ℝ (congruencePoincareCartesian N w.toFun) (z.re,z.im)) (axis i))+
      ((z.im:ℂ)*((fderiv ℝ (quotientWeightPlane N ε v) (z.re,z.im)) (axis i):ℂ))*
        poincareSum (G := gamma N) (upperFunction w.toFun) z
  rw [show congruencePoincareCartesian N w.toFun (z.re,z.im)=
    poincareSum (G := gamma N) (upperFunction w.toFun) z from
      congruencePoincareCartesian_represents N w.toFun z]
  ring

/-- The product rule holds for the actual quotient measure. -/
theorem quotientWeight_seed_gradient_product_ae (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (i : Bool) (w : SmoothUpperSeed) :
    ∀ᵐ z : ℍ ∂quotientMeasure N,
      (z.im:ℂ)*dir (axis i)
        (congruencePoincareCartesian N (fun W => (quotientWeightPlane N ε v W:ℂ)*
          upperSeedExtension (upperFunction w.toFun) W)) (z.re,z.im)=
        (weight N ε v z:ℂ)*seedGradient N i w z+
        quotientWeightGradientColumn N ε v i z*
          poincareSum (G := gamma N) (upperFunction w.toFun) z :=
  (quotientWeight_ae_differentiable N hε hv).mono
    (fun z hz => quotientWeight_seed_gradient_product_at N ε v i w z hz)

#print axioms quotientWeight_seed_poincare_germ
#print axioms quotientWeight_seed_gradient_product_at
#print axioms quotientWeight_seed_gradient_product_ae

end QuantitativeMaass
