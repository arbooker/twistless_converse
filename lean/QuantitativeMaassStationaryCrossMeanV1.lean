module

public import QuantitativeMaassStationaryMeanV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Simultaneous stationarity makes the means of two different horizontal
orbits orthogonal to the centered parts of both orbits. -/
theorem stationary_cross_mean_pairing (c d : ℝ→H) (hc : Continuous c)
    (hd : Continuous d) (hp : Function.Periodic d 1)
    (hs : ∀ r x y,inner ℂ (c (x+r)) (d (y+r))=inner ℂ (c x) (d y)) (x : ℝ) :
    inner ℂ (c x) (∫ y in Icc (0:ℝ) 1,d y)=
      inner ℂ (∫ y in Icc (0:ℝ) 1,c y) (∫ y in Icc (0:ℝ) 1,d y) := by
  let m := ∫ y in Icc (0:ℝ) 1,d y
  have hi : IntegrableOn d (Icc (0:ℝ) 1) volume := hd.integrableOn_Icc
  have hconst (y : ℝ) : inner ℂ (c y) m=inner ℂ (c 0) m := by
    simp only [m,←integral_inner hi]
    exact stationary_period_integral (fun x y => inner ℂ (c x) (d y))
      (fun z y => by simp only [hp y]) hs y
  have hmean : inner ℂ (∫ y in Icc (0:ℝ) 1,c y) m=inner ℂ (c 0) m := by
    have hh : inner ℂ (∫ y in Icc (0:ℝ) 1,c y) m=
        ∫ y in Icc (0:ℝ) 1,inner ℂ (c y) m := by
      rw [←inner_conj_symm (∫ y in Icc (0:ℝ) 1,c y) m,
        ←integral_inner hc.integrableOn_Icc m,←integral_conj]
      simp only [inner_conj_symm]
    rw [hh]
    simp only [hconst]
    simp
  exact (hconst x).trans hmean.symm

/-- Centering subtracts exactly the mixed mean term, also for columns at
different heights. -/
theorem stationary_cross_centered_inner (c d : ℝ→H) (hc : Continuous c)
    (hd : Continuous d) (hcp : Function.Periodic c 1) (hdp : Function.Periodic d 1)
    (hs : ∀ r x y,inner ℂ (c (x+r)) (d (y+r))=inner ℂ (c x) (d y)) (x y : ℝ) :
    inner ℂ (c x-∫ u in Icc (0:ℝ) 1,c u) (d y-∫ u in Icc (0:ℝ) 1,d u)=
      inner ℂ (c x) (d y)-
        inner ℂ (∫ u in Icc (0:ℝ) 1,c u) (∫ u in Icc (0:ℝ) 1,d u) := by
  have h1 := stationary_cross_mean_pairing c d hc hd hdp hs x
  have h2 := stationary_cross_mean_pairing d c hd hc hcp
    (fun r x y => by rw [←inner_conj_symm,hs,inner_conj_symm]) y
  have h2' := congrArg (starRingEnd ℂ) h2
  simp only [inner_conj_symm] at h2'
  rw [inner_sub_left,inner_sub_right,inner_sub_right,h1,h2']
  abel

#print axioms stationary_cross_mean_pairing
#print axioms stationary_cross_centered_inner

end QuantitativeMaass
