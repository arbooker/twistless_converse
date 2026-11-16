module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Polar integration of an arbitrary complex-valued radial function.
The Bochner conventions apply even when the function is not integrable. -/
theorem integral_complex_norm (f : ℝ → ℂ) :
    (∫ z : ℂ,f ‖z‖)=(2*Real.pi:ℂ)*∫ r in Ioi (0:ℝ),(r:ℂ)*f r := by
  rw [← Complex.integral_comp_polarCoord_symm]
  have he : (∫ p in polarCoord.target, p.1 • f ‖Complex.polarCoord.symm p‖)=
      ∫ p in (Ioi (0:ℝ)) ×ˢ Ioo (-Real.pi) Real.pi, (p.1:ℂ)*f p.1 := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    rw [Complex.norm_polarCoord_symm,abs_of_pos hp.1,Complex.real_smul]
  rw [he,Measure.volume_eq_prod,← Measure.prod_restrict,
    integral_fun_fst (fun r : ℝ => (r:ℂ)*f r)]
  simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo,sub_neg_eq_add,
    ← two_mul,ENNReal.toReal_ofReal (by positivity : 0≤2*Real.pi),Complex.real_smul,
    Complex.ofReal_mul,Complex.ofReal_ofNat]

/-- Squaring the radius removes its Jacobian. -/
theorem integral_square_radius (f : ℝ → ℂ) :
    (∫ r in Ioi (0:ℝ),(r:ℂ)*f (r^2))=(1/2:ℂ)*∫ u in Ioi (0:ℝ),f u := by
  have him : (fun r : ℝ => r^2) '' Ioi (0:ℝ)=Ioi (0:ℝ) := by
    ext u
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact sq_pos_of_pos hr
    · intro hu
      exact ⟨Real.sqrt u,Real.sqrt_pos.mpr hu,Real.sq_sqrt (le_of_lt hu)⟩
  have hinj : InjOn (fun r : ℝ => r^2) (Ioi (0:ℝ)) := by
    intro r hr s hs he
    exact (sq_eq_sq₀ (le_of_lt hr) (le_of_lt hs)).mp he
  have hd (r : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · rfl
    · simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (hd r).hasDerivWithinAt) hinj f
  rw [him] at h
  have he : (∫ r in Ioi (0:ℝ),|2*r| • f (r^2))=
      (2:ℂ)*∫ r in Ioi (0:ℝ),(r:ℂ)*f (r^2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hr),Complex.real_smul,Complex.ofReal_mul]
    norm_num
    ring
  rw [he] at h
  linear_combination (-1/2:ℂ)*h

/-- Radial integration in the squared Euclidean radius. -/
theorem integral_complex_normSq (f : ℝ → ℂ) :
    (∫ z : ℂ,f (Complex.normSq z))=(Real.pi:ℂ)*∫ u in Ioi (0:ℝ),f u := by
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [integral_complex_norm (fun r => f (r^2)),integral_square_radius]
  ring

#print axioms integral_complex_norm
#print axioms integral_square_radius
#print axioms integral_complex_normSq

end QuantitativeMaass
