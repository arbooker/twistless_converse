module

public import FinitenessPolynomialSeriesV1
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option autoImplicit false

public section

namespace FinitenessSeriesIndependence

open FinitenessPolynomialSeries FormalMultilinearSeries Metric

variable {I : Type*}

theorem finite_series (a : I → ℕ → ℂ) (ha : ∀ i, PolynomialBound (a i))
    (c : I → ℂ) (s : Finset I) :
    HasFPowerSeriesAt (∑ i ∈ s, c i • sum (a i))
      (ofScalars ℂ (∑ i ∈ s, c i • a i)) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      change HasFPowerSeriesAt (fun _ : ℂ => (0:ℂ)) (ofScalars ℂ (0 : ℕ → ℂ)) 0
      simpa only [ofScalars_series_eq_zero_of_scalar_zero,
        constFormalMultilinearSeries_zero] using
        (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (c := (0:ℂ)) (e := 0))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ofScalars_add, ofScalars_smul]
      exact (has_series (ha i)).const_smul.add ih

/-- Local equality of a finite linear combination of power series forces
the same equality coefficient by coefficient. -/
theorem relation (a : I → ℕ → ℂ) (ha : ∀ i, PolynomialBound (a i))
    (c : I → ℂ) (s : Finset I)
    (hz : ∀ w ∈ ball (0:ℂ) 1, ∑ i ∈ s, c i*sum (a i) w=0) :
    ∑ i ∈ s, c i • a i = 0 := by
  have hs := finite_series a ha c s
  have hzero : HasFPowerSeriesAt (fun _ : ℂ => (0:ℂ))
      (ofScalars ℂ (0 : ℕ → ℂ)) 0 := by
    simpa only [ofScalars_series_eq_zero_of_scalar_zero,
      constFormalMultilinearSeries_zero] using
      (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (c := (0:ℂ)) (e := 0))
  apply ofScalars_series_injective ℂ ℂ
  apply hs.eq_formalMultilinearSeries_of_eventually hzero
  apply Filter.mem_of_superset (ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num))
  intro w hw
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.mem_ofPred_eq] using hz w hw

theorem independent (a : I → ℕ → ℂ) (ha : ∀ i, PolynomialBound (a i))
    (hlin : LinearIndependent ℂ a) (G : I → ℂ → ℂ)
    (hG : ∀ i w, ‖w‖ < 1 → G i w=sum (a i) w) :
    LinearIndependent ℂ G := by
  rw [linearIndependent_iff'] at hlin ⊢
  intro s c hc
  apply hlin s c
  apply relation a ha c s
  intro w hw
  have hh := congrFun hc w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hh
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  simpa only [hG _ _ hw'] using hh

#print axioms independent

end FinitenessSeriesIndependence
