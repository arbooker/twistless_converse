module
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassLocalWave

/-- A transport equation determines the solution on each characteristic.
No integrability on the whole spatial line is required. -/
theorem transport_initial (v : ℝ × ℝ → ℂ) (hv : Differentiable ℝ v)
    (c : ℝ) (htransport : ∀ p, fderiv ℝ v p (1,c)=0) (t x : ℝ) :
    v (t,x)=v (0,x-c*t) := by
  let path : ℝ → ℝ × ℝ := fun r => (r,x+c*(r-t))
  have hp (r : ℝ) : HasDerivAt path (1,c) r := by
    simpa [path] using (hasDerivAt_id r).prodMk
      ((((hasDerivAt_id r).sub_const t).const_mul c).const_add x)
  have hd (r : ℝ) : HasDerivAt (fun r => v (path r)) 0 r := by
    simpa only [htransport,Function.comp_def] using
      (hv (path r)).hasFDerivAt.comp_hasDerivAt r (hp r)
  have h := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa [path,sub_eq_add_neg] using h

/-- Classical uniqueness for the free wave equation on the full plane,
proved by the two characteristic directions. This is the classical component
of local weak uniqueness; it does not assume global L2 control. -/
theorem classical_wave_zero (u : ℝ × ℝ → ℂ) (hu : ContDiff ℝ 2 u)
    (hPDE : ∀ p, fderiv ℝ (fderiv ℝ u) p (1,0) (1,0)=
      fderiv ℝ (fderiv ℝ u) p (0,1) (0,1))
    (hvalue : ∀ x, u (0,x)=0)
    (hvelocity : ∀ x, fderiv ℝ u (0,x) (1,0)=0) (t x : ℝ) :
    u (t,x)=0 := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu2 : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m:=1) (by norm_num)).differentiable one_ne_zero
  let r : ℝ × ℝ → ℂ := fun p => fderiv ℝ u p (1,1)
  have hr (p : ℝ × ℝ) : HasFDerivAt r
      ((fderiv ℝ (fderiv ℝ u) p).flip (1,1)) p := by
    simpa [r] using (hu2 p).hasFDerivAt.clm_apply
      (hasFDerivAt_const ((1,1) : ℝ × ℝ) p)
  have hplus : ((1,1) : ℝ × ℝ)=(1,0)+(0,1) := by ext <;> norm_num
  have hminus : ((1,-1) : ℝ × ℝ)=(1,0)-(0,1) := by ext <;> norm_num
  have hrPDE (p : ℝ × ℝ) : fderiv ℝ r p (1,-1)=0 := by
    rw [(hr p).fderiv]
    change fderiv ℝ (fderiv ℝ u) p (1,-1) (1,1)=0
    rw [hminus,hplus]
    simp only [map_sub,map_add,sub_apply]
    have hs := ((hu.contDiffAt (x:=p)).isSymmSndFDerivAt (by norm_num)).eq
      ((1,0) : ℝ × ℝ) ((0,1) : ℝ × ℝ)
    rw [hs,hPDE p]
    ring
  have hr0 (x : ℝ) : r (0,x)=0 := by
    have hc := (hu1 (0,x)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x (0:ℝ)).prodMk (hasDerivAt_id x))
    have he : (fun y : ℝ => u (0,y))=fun _ => (0:ℂ) := funext hvalue
    have hx : fderiv ℝ u (0,x) (0,1)=0 := by
      have hd := hc.deriv
      change deriv (fun y => u (0,y)) x=fderiv ℝ u (0,x) (0,1) at hd
      rw [he,deriv_const] at hd
      exact hd.symm
    change fderiv ℝ u (0,x) (1,1)=0
    rw [hplus,map_add,hvelocity,hx,add_zero]
  have hrzero (t x : ℝ) : r (t,x)=0 :=
    (transport_initial r (fun p => (hr p).differentiableAt) (-1) hrPDE t x).trans (hr0 _)
  exact (transport_initial u hu1 1 (fun p => hrzero p.1 p.2) t x).trans (hvalue _)

#print axioms transport_initial
#print axioms classical_wave_zero
end QuantitativeArithmeticMaassLocalWave
