module

public import QuantitativeMaassAbelCutoffMassV1
public import QuantitativeMaassRadialApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem abelProfile_const_mul (c : ℂ) (F : ℝ → ℂ) (q : ℝ) :
    abelProfile (fun v => c*F v) q=c*abelProfile F q := by
  simp only [abelProfile,deriv_const_mul_field',abelIntegral,integral_const_mul]
  ring

def abelNormalizedTest (R q : ℝ) : ℂ :=
  (abelCutoffMass R:ℂ)⁻¹*abelCutoff (Real.cosh R-1) q

def abelNormalizedProfile (R : ℝ) : ℝ → ℂ := abelProfile (abelNormalizedTest R)

theorem abelNormalizedTest_smooth (R : ℝ) : ContDiff ℝ ∞ (abelNormalizedTest R) :=
  contDiff_const.mul (abelCutoff_smooth _)

theorem abelNormalizedTest_compact (R : ℝ) (hR : 0<R) : HasCompactSupport (abelNormalizedTest R) :=
  (abelCutoff_compact _ (sub_pos.mpr (Real.one_lt_cosh.mpr (ne_of_gt hR)))).mul_left

theorem abelNormalizedTest_support (R : ℝ) (hR : 0<R) :
    Function.support (abelNormalizedTest R)⊆Iic (Real.cosh R) := by
  intro q hq
  apply abelCutoff_radius_support R hR
  intro hz
  exact hq (by simp [abelNormalizedTest,hz])

theorem abelNormalizedTest_real (R q : ℝ) : star (abelNormalizedTest R q)=abelNormalizedTest R q := by
  simp [abelNormalizedTest,abelCutoff,star_mul,mul_comm]

theorem abelNormalizedProfile_smooth (R : ℝ) (hR : 0<R) : ContDiff ℝ ∞ (abelNormalizedProfile R) :=
  abelProfile_smooth _ (abelNormalizedTest_smooth R) (abelNormalizedTest_compact R hR)

theorem abelNormalizedProfile_support (R : ℝ) (hR : 0<R) :
    Function.support (abelNormalizedProfile R)⊆Iic (Real.cosh R) :=
  abelProfile_support _ _ (abelNormalizedTest_support R hR)

theorem abelNormalizedProfile_eq (R q : ℝ) : abelNormalizedProfile R q=
    (abelCutoffMass R:ℂ)⁻¹*abelProfile (abelCutoff (Real.cosh R-1)) q :=
  abelProfile_const_mul _ _ q

theorem abelNormalizedProfile_mass (R : ℝ) (hR : 0<R) :
    (2*Real.pi:ℂ)*(∫ q in Ioi (1:ℝ),abelNormalizedProfile R q)=1 := by
  simp_rw [abelNormalizedProfile_eq]
  rw [integral_const_mul,mul_left_comm,abelCutoffProfile_mass R hR]
  exact inv_mul_cancel₀ (by exact_mod_cast ne_of_gt (abelCutoffMass_pos R hR))

theorem abelNormalizedProfile_norm_mass (R : ℝ) (hR : 0<R) :
    2*Real.pi*(∫ q in Ioi (1:ℝ),‖abelNormalizedProfile R q‖)=1 := by
  simp_rw [abelNormalizedProfile_eq,norm_mul]
  rw [integral_const_mul,mul_left_comm,abelCutoffProfile_norm_mass R hR,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (abelCutoffMass_pos R hR)]
  exact inv_mul_cancel₀ (ne_of_gt (abelCutoffMass_pos R hR))

/-- The constructed, normalized Abel family recovers every continuous
invariant quotient-L2 representative at each point as its radius shrinks. -/
theorem abelNormalizedProfile_output_tendsto {ι : Type*} (l : Filter ι) (N : ℕ)
    (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (f : ℍ → ℂ) (hf : Measurable f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (hL : MemLp f 2 (quotientMeasure N)) (x : ℍ) (hfx : ContinuousAt f x) :
    Tendsto (fun i => (radialKernelData N (abelNormalizedProfile (R i))
      (abelNormalizedProfile_smooth _ (hR i)) (R i) (hR i).le
      (abelNormalizedProfile_support _ (hR i))).output f x) l (𝓝 (f x)) :=
  radialKernel_output_tendsto l N (fun i => abelNormalizedProfile (R i))
    (fun i => abelNormalizedProfile_smooth _ (hR i)) R (fun i => (hR i).le)
    (fun i => abelNormalizedProfile_support _ (hR i)) hlim
    (fun i => abelNormalizedProfile_mass _ (hR i)) 1 (by norm_num)
    (fun i => (abelNormalizedProfile_norm_mass _ (hR i)).le) f hf hinv hL x hfx

#print axioms abelProfile_const_mul
#print axioms abelNormalizedProfile_smooth
#print axioms abelNormalizedProfile_mass
#print axioms abelNormalizedProfile_norm_mass
#print axioms abelNormalizedProfile_output_tendsto

end QuantitativeMaass
