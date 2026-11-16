module

public import QuantitativeArithmeticMaassClassicalWaveUniquenessV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open scoped ContDiff

namespace QuantitativeMaass.Wave
open QuantitativeArithmeticMaassLocalWave

/-- D'Alembert's formula for C2 free waves with zero initial velocity.
The proof follows the two characteristic directions and needs no global
spatial integrability assumption. -/
theorem classical_wave_dAlembert (u : ℝ × ℝ → ℂ) (hu : ContDiff ℝ 2 u)
    (hPDE : ∀ p, fderiv ℝ (fderiv ℝ u) p (1,0) (1,0)=
      fderiv ℝ (fderiv ℝ u) p (0,1) (0,1))
    (hvelocity : ∀ x, fderiv ℝ u (0,x) (1,0)=0) (t x : ℝ) :
    u (t,x)=(u (0,x+t)+u (0,x-t))/2 := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu2 : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m:=1) (by norm_num)).differentiable one_ne_zero
  let r : ℝ × ℝ → ℂ := fun p => fderiv ℝ u p (1,1)
  have hr (p : ℝ × ℝ) : HasFDerivAt r ((fderiv ℝ (fderiv ℝ u) p).flip (1,1)) p := by
    simpa [r] using (hu2 p).hasFDerivAt.clm_apply (hasFDerivAt_const ((1,1):ℝ × ℝ) p)
  have hplus : ((1,1):ℝ × ℝ)=(1,0)+(0,1) := by ext <;> norm_num
  have hminus : ((1,-1):ℝ × ℝ)=(1,0)-(0,1) := by ext <;> norm_num
  have hrPDE (p : ℝ × ℝ) : fderiv ℝ r p (1,-1)=0 := by
    rw [(hr p).fderiv]
    change fderiv ℝ (fderiv ℝ u) p (1,-1) (1,1)=0
    rw [hminus,hplus]
    simp only [map_sub,map_add,sub_apply]
    have hs := (hu.contDiffAt (x:=p)).isSymmSndFDerivAt (by norm_num)
    rw [hs.eq ((1,0):ℝ × ℝ) ((0,1):ℝ × ℝ),hPDE p]
    ring
  have htransport (a b : ℝ) : r (a,b)=r (0,b+a) := by
    simpa only [neg_one_mul,sub_neg_eq_add] using
      transport_initial r (fun p => (hr p).differentiableAt) (-1) hrPDE a b
  let a : ℝ → ℂ := fun y => u (0,y)
  have ha (y : ℝ) : HasDerivAt a (fderiv ℝ u (0,y) (0,1)) y :=
    (hu1 (0,y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y (0:ℝ)).prodMk (hasDerivAt_id y))
  have hr0 (y : ℝ) : r (0,y)=deriv a y := by
    rw [(ha y).deriv]
    change fderiv ℝ u (0,y) (1,1)=fderiv ℝ u (0,y) (0,1)
    rw [hplus,map_add,hvelocity,zero_add]
  have hzero (v : ℝ) : HasDerivAt
      (fun v => (2:ℂ)*u (v,x-t+v)-a (x-t+2*v)) 0 v := by
    have hp : HasDerivAt (fun v : ℝ => (v,x-t+v)) (1,1) v :=
      (hasDerivAt_id v).prodMk ((hasDerivAt_id v).const_add (x-t))
    have hq : HasDerivAt (fun v : ℝ => x-t+2*v) 2 v := by
      simpa only [mul_one,id_eq] using ((hasDerivAt_id v).const_mul 2).const_add (x-t)
    have hv := ((hu1 (v,x-t+v)).hasFDerivAt.comp_hasDerivAt v hp).const_mul (2:ℂ)
    have hav := ((ha (x-t+2*v)).scomp v hq)
    have h := hv.fun_sub hav
    apply h.congr_deriv
    rw [← (ha (x-t+2*v)).deriv]
    change (2:ℂ)*r (v,x-t+v)-(2:ℝ) • deriv a (x-t+2*v)=0
    rw [htransport,hr0]
    have he : x-t+v+v=x-t+2*v := by ring
    rw [he,Complex.real_smul]
    norm_num
  have hc := is_const_of_deriv_eq_zero (fun v => (hzero v).differentiableAt)
    (fun v => (hzero v).deriv) t 0
  have he1 : x-t+t=x := by ring
  have he2 : x-t+2*t=x+t := by ring
  simp only [he1,he2,mul_zero,add_zero,a] at hc
  linear_combination (1/2:ℂ)*hc

#print axioms classical_wave_dAlembert

end QuantitativeMaass.Wave
