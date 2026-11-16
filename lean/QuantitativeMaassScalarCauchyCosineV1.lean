module

public import QuantitativeMaassScalarAbelCauchyV1
public import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Uniqueness for a bounded first-order linear equation on positive time. -/
theorem bounded_linear_ode_unique_nonneg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : H →L[ℝ] H) (u v : ℝ → H)
    (hu : ∀ t,HasDerivAt u (A (u t)) t) (hv : ∀ t,HasDerivAt v (A (v t)) t)
    (h0 : u 0=v 0) (t : ℝ) (ht : 0≤t) : u t=v t := by
  let w : ℝ → H := fun s => u s-v s
  have hw (s : ℝ) : HasDerivAt w (A (w s)) s := by
    simpa only [w,map_sub,Pi.sub_apply] using! (hu s).sub (hv s)
  have hc : Continuous w := continuous_iff_continuousAt.mpr (fun s => (hw s).continuousAt)
  have hz : w 0=0 := sub_eq_zero.mpr h0
  have hh := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (a:=0) (b:=t) (K:=‖A‖) hc.continuousOn
    (fun s _ => (hw s).hasDerivWithinAt) hz (fun s _ => A.le_opNorm (w s)) t ⟨ht,le_rfl⟩
  exact sub_eq_zero.mp hh

/-- The scalar Cauchy evolution with zero velocity is the literal cosine
for a real spectral parameter, including r=0. -/
theorem scalarCauchy_cosine (r : ℝ) (c : ℂ × ℂ) (hc : c.2=0) (t : ℝ) (ht : 0≤t) :
    boundedCauchyPosition ((scalarAbelGenerator (1/4+(r:ℂ)^2)).restrictScalars ℝ) c t=
      (Real.cos (r*t):ℂ)*c.1 := by
  let A := (scalarAbelGenerator (1/4+(r:ℂ)^2)).restrictScalars ℝ
  let B := distributionCauchyOperator A
  let u : ℝ → ℂ × ℂ := fun s => (boundedCauchyPosition A c s,boundedCauchyVelocity A c s)
  let v : ℝ → ℂ × ℂ := fun s => ((Real.cos (r*s):ℂ)*c.1,-(r:ℂ)*(Real.sin (r*s):ℂ)*c.1)
  have hA (z : ℂ) : A z=(r:ℂ)^2*z := by
    change ((1/4+(r:ℂ)^2)-1/4)*z=_
    ring
  have hu (s : ℝ) : HasDerivAt u (B (u s)) s := by
    exact (boundedCauchyPosition_hasDerivAt A c s).prodMk (boundedCauchyVelocity_hasDerivAt A c s)
  have hv (s : ℝ) : HasDerivAt v (B (v s)) s := by
    have hd : HasDerivAt (fun a : ℝ => r*a) r s := by
      simpa only [mul_one,id_eq] using! (hasDerivAt_id s).const_mul r
    have hcos := (hd.cos.ofReal_comp).mul_const c.1
    have hsin := ((hd.sin.ofReal_comp).const_mul (-(r:ℂ))).mul_const c.1
    have hh := hcos.prodMk hsin
    convert hh using 1
    · change (-(r:ℂ)*(Real.sin (r*s):ℂ)*c.1,-A ((Real.cos (r*s):ℂ)*c.1))=_
      rw [hA]
      push_cast
      apply Prod.ext <;> ring
  have h0 : u 0=v 0 := by
    simp only [u,v,(boundedCauchy_initial A c).1,(boundedCauchy_initial A c).2,hc,
      neg_zero,mul_zero,zero_mul,Real.cos_zero,Real.sin_zero,Complex.ofReal_one,Complex.ofReal_zero,one_mul]
  exact congrArg Prod.fst (bounded_linear_ode_unique_nonneg B u v hu hv h0 t ht)

#print axioms bounded_linear_ode_unique_nonneg
#print axioms scalarCauchy_cosine

end QuantitativeMaass
