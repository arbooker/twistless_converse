module

public import SmallLevelAdditiveMellinV1
public import Mathlib.Analysis.Analytic.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticMellinScale
open Complex Filter Set MeasureTheory FinitenessAllLevelAxisDecay FinitenessFourierConstruction

theorem axis_one_rescale {N : ℕ} (hN : 0<N) (a : ℕ → ℂ) (t : ℝ) :
    axis N a (Real.sqrt N*t)=axis 1 a t := by
  have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  unfold axis
  simp only [Nat.cast_one,Real.sqrt_one,div_one]
  congr 2
  field_simp

theorem mellin_one_scale {N : ℕ} (hN : 0<N) (a : ℕ → ℂ) (s : ℂ) :
    mellin (axis 1 a) s=(Real.sqrt N:ℂ)^(-s)*mellin (axis N a) s := by
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h := mellin_comp_mul_left (axis N a) s hs
  simpa only [axis_one_rescale hN a,smul_eq_mul] using h

theorem entire_at_one {N : ℕ} (hN : 0<N) (a : ℕ → ℂ)
    (h : Differentiable ℂ (mellin (axis N a))) :
    Differentiable ℂ (mellin (axis 1 a)) := by
  have hs : (Real.sqrt N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (show (0:ℝ)<N by exact_mod_cast hN)).ne'
  have he : mellin (axis 1 a)=(fun s : ℂ => (Real.sqrt N:ℂ)^(-s)*mellin (axis N a) s) :=
    funext (mellin_one_scale hN a)
  rw [he]
  have hp : Differentiable ℂ (fun s : ℂ => (Real.sqrt N:ℂ)^(-s)) := by
    simp_rw [Complex.cpow_def_of_ne_zero hs]
    fun_prop
  exact hp.mul h

#print axioms axis_one_rescale
#print axioms mellin_one_scale
#print axioms entire_at_one
end QuantitativeArithmeticMellinScale
