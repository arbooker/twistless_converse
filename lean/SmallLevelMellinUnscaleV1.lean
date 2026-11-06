module

public import QuantitativeArithmeticMellinScaleV1
public import FinitenessFiniteOrderV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelMellinUnscale
open Complex MeasureTheory FinitenessAllLevelAxisDecay

/-- Positive real exponential powers have a global finite-order envelope. -/
theorem negative_cpow_bound {r : ℝ} (hr : 0<r) :
    FinitenessFiniteOrder.Bound (fun s : ℂ => (r:ℂ)^(-s)) := by
  have he : (fun s : ℂ => (r:ℂ)^(-s))=
      (fun s : ℂ => Complex.exp (((-Real.log r:ℝ):ℂ)*s)) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
      ← Complex.ofReal_log hr.le,Complex.ofReal_neg]
    congr 1
    ring
  rw [he]
  exact FinitenessFiniteOrder.exp_linear (-Real.log r)

theorem finite_order_at_one {N : ℕ} (hN : 0<N) (a : ℕ → ℂ)
    (h : FinitenessFiniteOrder.Bound (mellin (axis N a))) :
    FinitenessFiniteOrder.Bound (mellin (axis 1 a)) := by
  have he : mellin (axis 1 a)=(fun s : ℂ => (Real.sqrt N:ℂ)^(-s)*mellin (axis N a) s) :=
    funext (QuantitativeArithmeticMellinScale.mellin_one_scale hN a)
  rw [he]
  exact FinitenessFiniteOrder.mul
    (negative_cpow_bound (Real.sqrt_pos.mpr (by exact_mod_cast hN))) h

/-- Unscaling also works when the functional equation exchanges two sequences. -/
theorem reflection_pair {N k : ℕ} (hN : 0<N) (a b : ℕ → ℂ) (ε : ℂ)
    (h : ∀ s : ℂ, mellin (axis N a) s=ε*mellin (axis N b) ((k:ℂ)-s)) (s : ℂ) :
    mellin (axis 1 a) s=ε*(Real.sqrt N:ℂ)^((k:ℂ)-2*s)*
      mellin (axis 1 b) ((k:ℂ)-s) := by
  have hn : (Real.sqrt N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (show (0:ℝ)<N by exact_mod_cast hN)).ne'
  have hp : (Real.sqrt N:ℂ)^((k:ℂ)-2*s)*(Real.sqrt N:ℂ)^(-((k:ℂ)-s))=
      (Real.sqrt N:ℂ)^(-s) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    ring
  rw [QuantitativeArithmeticMellinScale.mellin_one_scale hN a,h,
    QuantitativeArithmeticMellinScale.mellin_one_scale hN b]
  rw [← hp]
  ring

#print axioms negative_cpow_bound
#print axioms finite_order_at_one
#print axioms reflection_pair
end SmallLevelMellinUnscale
