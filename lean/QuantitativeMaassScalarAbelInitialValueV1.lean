module

public import QuantitativeMaassScalarAbelOriginalTestV1
public import QuantitativeMaassScalarTimeInitialV1
public import QuantitativeMaassContinuousRadialInitialV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- The geometric and time approximate identities fix the literal initial
position, with the half-line normalization explicitly equal to two. -/
theorem scalarAbel_initial_value (N : ℕ) (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ γ : gamma N,∀ y,f (γ•y)=f y) (x : ℍ)
    (v : ℝ → ℂ) (hv : Continuous v)
    (hvT : ∀ φ : PositiveSmoothTest,scalarAbelDistribution f hf x φ=∫ t,φ t • v t) :
    v 0=2*f x := by
  let R : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hR (n : ℕ) : 0<R n := by dsimp [R]; positivity
  have hR0 : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hg := ContinuousRadial.abelNormalizedProfile_output_tendsto atTop N R hR hR0 f hf hinv x
  have he (n : ℕ) :
      (radialKernelData N (abelNormalizedProfile (R n))
        (abelNormalizedProfile_smooth _ (hR n)) (R n) (hR n).le
        (abelNormalizedProfile_support _ (hR n))).output f x=
      scalarAbelConvolution f x (abelNormalizedTest (R n)) :=
    (continuous_radial_output_unfold N (abelNormalizedProfile (R n))
      (abelNormalizedProfile_smooth _ (hR n)) (R n) (hR n).le
      (abelNormalizedProfile_support _ (hR n)) f hf hinv x).2.2
  have hg' : Tendsto (fun n => (2:ℂ)*scalarAbelConvolution f x (abelNormalizedTest (R n))) atTop
      (𝓝 (2*f x)) := by
    apply (hg.const_mul (2:ℂ)).congr'
    filter_upwards with n
    rw [he]
  have ht := normalizedContinuousCurve_initial atTop R hR hR0 v hv
  have he' (n : ℕ) : scalarAbelConvolution f x (abelNormalizedTest (R n))=
      ∫ t in Ioi (0:ℝ),coshTimeTest (abelNormalizedTest (R n)) t*v t :=
    scalarAbel_originalTest f hf x v hv hvT (abelNormalizedTest (R n))
      (abelNormalizedTest_smooth _) (abelNormalizedTest_compact _ (hR n))
      (abelNormalizedTest_real _) (R n) (hR n).le (abelNormalizedTest_support _ (hR n))
  exact (tendsto_nhds_unique hg' (ht.congr' (Eventually.of_forall
    (fun n => by dsimp only; rw [he'])))).symm

#print axioms scalarAbel_initial_value

end QuantitativeMaass
