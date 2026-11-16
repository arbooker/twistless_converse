module

public import QuantitativeMaassEulerSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

def complexSqrtWave (f : ℝ → ℂ) (y : ℝ) : ℂ := (Real.sqrt y:ℂ)*f y

def complexSqrtFirst (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  f y/(2*(Real.sqrt y:ℂ))+(Real.sqrt y:ℂ)*g y

def complexSqrtSecond (f g h : ℝ → ℂ) (y : ℝ) : ℂ :=
  -(f y/(4*(y:ℂ)*(Real.sqrt y:ℂ)))+g y/(Real.sqrt y:ℂ)+(Real.sqrt y:ℂ)*h y

theorem complexSqrtWave_hasDerivAt {f g : ℝ → ℂ} {y : ℝ} (hy : 0<y)
    (hf : HasDerivAt f (g y) y) :
    HasDerivAt (complexSqrtWave f) (complexSqrtFirst f g y) y := by
  convert ((Real.hasDerivAt_sqrt hy.ne').ofReal_comp).mul hf using 1
  · rfl
  · dsimp [complexSqrtFirst]
    push_cast
    ring

theorem complexSqrtFirst_hasDerivAt {f g h : ℝ → ℂ} {y : ℝ} (hy : 0<y)
    (hf : HasDerivAt f (g y) y) (hg : HasDerivAt g (h y) y) :
    HasDerivAt (complexSqrtFirst f g) (complexSqrtSecond f g h y) y := by
  have hs : (Real.sqrt y:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
  have hyc : (y:ℂ)≠0 := by exact_mod_cast hy.ne'
  have hsq : (Real.sqrt y:ℂ)^2=(y:ℂ) := by exact_mod_cast Real.sq_sqrt hy.le
  have hd := (Real.hasDerivAt_sqrt hy.ne').ofReal_comp
  convert (hf.div (hd.const_mul 2) (mul_ne_zero (by norm_num) hs)).add (hd.mul hg) using 1
  · rfl
  · dsimp [complexSqrtSecond]
    push_cast
    field_simp [hs,hyc]
    rw [hsq]
    ring

#print axioms complexSqrtWave_hasDerivAt
#print axioms complexSqrtFirst_hasDerivAt

end QuantitativeMaass
