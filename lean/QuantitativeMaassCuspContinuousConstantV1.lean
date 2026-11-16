module

public import QuantitativeMaassLVCuspHeightV1
public import QuantitativeMaassRawColumnBesselV1
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace MatrixGroups

namespace QuantitativeMaass

/-- Integral cusp coordinates with logarithmic height and common period N. -/
def cuspLogPoint (N : ℕ) (s : SL(2,ℤ)) (u x : ℝ) : ℍ :=
  s • horocyclePoint ((N:ℝ)*x) (Real.exp u) (Real.exp_pos u)

theorem cuspLogPoint_continuous (N : ℕ) (s : SL(2,ℤ)) :
    Continuous (Function.uncurry (cuspLogPoint N s)) := by
  have hh : Continuous (fun p : ℝ × ℝ =>
      horocyclePoint ((N:ℝ)*p.2) (Real.exp p.1) (Real.exp_pos p.1)) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : ℝ × ℝ => (⟨(N:ℝ)*p.2,Real.exp p.1⟩ : ℂ))
    have he : (fun p : ℝ × ℝ => (⟨(N:ℝ)*p.2,Real.exp p.1⟩ : ℂ))=
        fun p => (((N:ℝ)*p.2:ℝ):ℂ)+(Real.exp p.1:ℂ)*Complex.I := by
      funext p
      apply Complex.ext <;>
        simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
          Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
          mul_zero,mul_one,add_zero,zero_add,sub_zero]
    rw [he]
    fun_prop
  exact (continuous_const_smul (SpecialLinearGroup.mapGL ℝ s)).comp hh

theorem cuspConstant_log_continuous (N : ℕ) (s : SL(2,ℤ))
    (f : ℍ → ℂ) (hf : Continuous f) :
    Continuous (fun u => cuspConstant N s f (Real.exp u)) := by
  have hh := continuous_parametric_integral_of_continuous
    (f:=fun u x => f (cuspLogPoint N s u x))
    (hf.comp (cuspLogPoint_continuous N s)) (μ:=volume) (s:=Icc (0:ℝ) 1) isCompact_Icc
  have he : (fun u => cuspConstant N s f (Real.exp u))=
      fun u => ∫ x in Icc (0:ℝ) 1,f (cuspLogPoint N s u x) := by
    funext u
    simp only [cuspConstant,zeroFourier,cuspProfile,dite_eq_left (Real.exp_pos u)]
    rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
    rfl
  rw [he]
  exact hh

/-- Continuous representatives of the actual closed cusp space have vanishing
literal constant term at every positive height, not merely in local L2. -/
theorem localCuspidalSpace_continuous_constant_zero (N : ℕ) (hN : 0<N)
    (v : AutomorphicSpace N) (hv : v∈localCuspidalSpace N hN)
    (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ γ : gamma N,∀ z,f (γ•z)=f z)
    (he : v.val=ᵐ[quotientMeasure N]f) (s : SL(2,ℤ)) (y : ℝ) (hy : 0<y) :
    cuspConstant N s f y=0 := by
  have hm : f∈AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
    ⟨hf.measurable,hinv,(memLp_congr_ae he).mp (Lp.memLp v.val)⟩
  let w : AutomorphicL2.representatives (gamma N) (quotientMeasure N) := ⟨f,hm⟩
  have hw : AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) w=v := by
    apply Subtype.ext
    apply Lp.ext
    exact hm.2.2.coeFn_toLp.trans he.symm
  let u := Real.log y
  have hz := (mem_localCuspidalSpace N hN v).mp hv s (u-1) (u+1)
  have ha := cuspLogConstant_representative_ae N hN s (u-1) (u+1) w hf
  rw [hw,hz] at ha
  have hae : logHalfDensity (cuspConstant N s f)=ᵐ[volume.restrict (Icc (u-1) (u+1))]
      (fun _ => (0:ℂ)) := ha.symm.trans (Lp.coeFn_zero _ _ _)
  have hc : Continuous (logHalfDensity (cuspConstant N s f)) := by
    unfold logHalfDensity
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_neg.div_const 2))).mul (cuspConstant_log_continuous N s f hf)
  have hpoint := Measure.eqOn_Icc_of_ae_eq volume
    (by linarith : u-1≠u+1) hae hc.continuousOn continuous_const.continuousOn
    (by constructor <;> linarith : u∈Icc (u-1) (u+1))
  change (Real.exp (-u/2):ℂ)*cuspConstant N s f (Real.exp u)=0 at hpoint
  have hn : (Real.exp (-u/2):ℂ)≠0 := by exact_mod_cast Real.exp_ne_zero (-u/2)
  have hzero := (mul_eq_zero.mp hpoint).resolve_left hn
  simpa only [u,Real.exp_log hy] using hzero

#print axioms cuspLogPoint_continuous
#print axioms cuspConstant_log_continuous
#print axioms localCuspidalSpace_continuous_constant_zero

end QuantitativeMaass
