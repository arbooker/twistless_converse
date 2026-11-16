module

public import QuantitativeMaassGrowingMomentLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

/-- Exponentially increasing cusp cutoffs remain compatible with the
uniform growing-degree geometric error and every allowed shrinking width. -/
theorem growing_cusp_geometric_limit (ε : ℝ → ℝ) (b C A E v L : ℝ)
    (hb : 0<b) (hC : 0≤C) (hE : 0<E) (hv : 0≤v) (hL : 0≤L)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => C*Real.sqrt t*b^(growingMomentDegree t)*
      Real.exp (A+30*Real.log (E*(Real.exp (v+L*(growingMomentDegree t:ℝ))+3)^2))/(t*ε t))
      atTop (𝓝 0) := by
  let D := A+30*Real.log E+60*Real.log 4+60*v
  have hm := growingMomentDegree_cost ε (b*Real.exp (60*L)) (C*Real.exp D)
    (by positivity) (by positivity) hε hproduct
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    let n := growingMomentDegree t
    have hH : 1≤Real.exp (v+L*(n:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    have hlog : Real.log (Real.exp (v+L*(n:ℝ))+3)≤Real.log 4+v+L*(n:ℝ) := by
      have hh := Real.log_le_log (by positivity : 0<Real.exp (v+L*(n:ℝ))+3)
        (show Real.exp (v+L*(n:ℝ))+3≤4*Real.exp (v+L*(n:ℝ)) by linarith only [hH])
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hh
      simpa only [add_assoc] using hh
    have hgeom : Real.exp (A+30*Real.log (E*(Real.exp (v+L*(n:ℝ))+3)^2))≤
        Real.exp D*(Real.exp (60*L))^n := by
      rw [←Real.exp_nat_mul,←Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul hE.ne' (by positivity),Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      dsimp only [D]
      linarith only [hlog]
    calc
      _ ≤ C*Real.sqrt t*b^n*(Real.exp D*(Real.exp (60*L))^n)/(t*ε t) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = _ := by rw [mul_pow];ring

/-- The same exponential cutoff makes the actual operator-norm tail
negligible when its per-degree decay factor is below one. -/
theorem growing_cusp_tail_limit (ε : ℝ → ℝ) (u C v L : ℝ)
    (hu : 0<u) (hdecay : u*Real.exp (-L)<1)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (C*t*u^(growingMomentDegree t)/
      Real.exp (v+L*(growingMomentDegree t:ℝ)))/(t*ε t)) atTop (𝓝 0) := by
  have hh := (growingMomentDegree_decay ε (u*Real.exp (-L)) (by positivity)
    hdecay hε hproduct).const_mul (C*Real.exp (-v))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
  rw [Real.exp_add,mul_comm L,Real.exp_nat_mul,Real.exp_neg,Real.exp_neg,mul_pow,inv_pow]
  field_simp

/-- A concrete positive cutoff slope beats any positive operator-norm
base, so the tail decay condition is always available. -/
theorem growing_cusp_slope (u : ℝ) (hu : 0<u) :
    0<1+|Real.log u| ∧ u*Real.exp (-(1+|Real.log u|))<1 := by
  refine ⟨by positivity,?_⟩
  have hh : Real.log u-(1+|Real.log u|)<0 := by linarith only [le_abs_self (Real.log u)]
  calc
    _ = Real.exp (Real.log u-(1+|Real.log u|)) := by rw [Real.exp_sub,Real.exp_log hu,Real.exp_neg];ring
    _ < 1 := Real.exp_lt_one_iff.mpr hh

#print axioms growing_cusp_geometric_limit
#print axioms growing_cusp_tail_limit
#print axioms growing_cusp_slope

end QuantitativeMaass
