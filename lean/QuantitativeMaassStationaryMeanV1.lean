module

public import QuantitativeMaassColumnMeanEnergyV1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- A periodic stationary kernel has the same period integral at every center. -/
theorem stationary_period_integral (F : ℝ → ℝ → ℂ)
    (hp : ∀ x,Function.Periodic (F x) 1)
    (hs : ∀ r x y,F (x+r) (y+r)=F x y) (x : ℝ) :
    (∫ y in Icc (0:ℝ) 1,F x y)=∫ y in Icc (0:ℝ) 1,F 0 y := by
  have he (y : ℝ) : F x y=F 0 (y+(-x)) := by
    simpa only [add_neg_cancel] using (hs (-x) x y).symm
  simp_rw [he]
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_add_right]
  have hh := (hp 0).intervalIntegral_add_eq (-x) 0
  simp only [zero_add] at hh
  simpa only [zero_add,add_zero,add_comm,intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using hh

/-- For a continuous periodic Hilbert column with stationary Gram kernel,
its period mean is the orthogonal mean component at every center. -/
theorem stationary_column_mean_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (c : ℝ → H) (hc : Continuous c)
    (hp : Function.Periodic c 1)
    (hs : ∀ r x y,inner ℂ (c (x+r)) (c (y+r))=inner ℂ (c x) (c y)) (x : ℝ) :
    inner ℂ (c x) (∫ y in Icc (0:ℝ) 1,c y)=
      inner ℂ (∫ y in Icc (0:ℝ) 1,c y) (∫ y in Icc (0:ℝ) 1,c y) := by
  let m := ∫ y in Icc (0:ℝ) 1,c y
  have hi : IntegrableOn c (Icc (0:ℝ) 1) volume := hc.integrableOn_Icc
  have hconst (y : ℝ) : inner ℂ (c y) m=inner ℂ (c 0) m := by
    simp only [m,←integral_inner hi]
    exact stationary_period_integral (fun x y => inner ℂ (c x) (c y))
      (fun z y => by simp only [hp y]) hs y
  have hmean : inner ℂ m m=inner ℂ (c 0) m := by
    have hh : inner ℂ m m=∫ y in Icc (0:ℝ) 1,inner ℂ (c y) m := by
      change inner ℂ (∫ y in Icc (0:ℝ) 1,c y) m=_
      rw [←inner_conj_symm (∫ y in Icc (0:ℝ) 1,c y) m,
        ←integral_inner hi m,←integral_conj]
      simp only [inner_conj_symm]
    rw [hh]
    simp only [hconst]
    simp
  exact (hconst x).trans hmean.symm

/-- Exact cancellation of the constant mode for a stationary periodic column. -/
theorem stationary_column_centered_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (c : ℝ → H) (hc : Continuous c)
    (hp : Function.Periodic c 1)
    (hs : ∀ r x y,inner ℂ (c (x+r)) (c (y+r))=inner ℂ (c x) (c y)) (x : ℝ) :
    ‖c x-∫ y in Icc (0:ℝ) 1,c y‖^2=‖c x‖^2-
      (∫ y in Icc (0:ℝ) 1,inner ℂ (c x) (c y)).re := by
  have hi : IntegrableOn c (Icc (0:ℝ) 1) volume := hc.integrableOn_Icc
  have h := congrArg Complex.re (stationary_column_mean_pairing c hc hp hs x)
  rw [show (inner ℂ (∫ y in Icc (0:ℝ) 1,c y) (∫ y in Icc (0:ℝ) 1,c y)).re=
      ‖∫ y in Icc (0:ℝ) 1,c y‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _] at h
  rw [centered_column_norm_square _ _ h,integral_inner hi,h]

#print axioms stationary_period_integral
#print axioms stationary_column_mean_pairing
#print axioms stationary_column_centered_norm

end QuantitativeMaass
