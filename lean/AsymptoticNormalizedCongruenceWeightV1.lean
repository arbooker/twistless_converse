module

public import AsymptoticCongruenceWeightV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceWeight

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip
open AsymptoticCompactBranch AsymptoticMassTransport

/-- The scalar coefficient of the quotient induction isometry. -/
noncomputable def amplitude (N : ℕ) (ε : ℝ) (t : ℕ) (z : ℍ) : ℂ :=
  strip.indicator (fun w => ((cap ε t w/Real.sqrt (weight N ε t w):ℝ):ℂ)) z

theorem amplitude_measurable (N : ℕ) (ε : ℝ) (t : ℕ) :
    Measurable (amplitude N ε t) := by
  apply Measurable.indicator _ strip_measurable
  exact Complex.measurable_ofReal.comp
    ((cap_continuous ε t).measurable.div (weight_measurable N ε t).sqrt)

theorem amplitude_norm_sq (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (g : gamma N) (z : ℍ) :
    ‖amplitude N ε t (g.val • z)‖^2=
      strip.indicator (fun w => cap ε t w^2) (g.val • z)/weight N ε t z := by
  classical
  by_cases hg : g.val • z∈strip
  · rw [amplitude,Set.indicator_of_mem hg,Set.indicator_of_mem hg]
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,weight_invariant,
      Real.sq_sqrt (weight_pos N hε ht z).le]
  · rw [amplitude,Set.indicator_of_notMem hg,Set.indicator_of_notMem hg]
    simp

/-- Every congruence orbit has total squared amplitude one. Finiteness
and nonvanishing of the normalizing denominator are already proved. -/
theorem amplitude_hasSum (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    HasSum (fun g : gamma N => ‖amplitude N ε t (g.val • z)‖^2) 1 := by
  have hn := (weight_pos N hε ht z).ne'
  have hs := (weight_summable N hε ht z).hasSum.div_const (weight N ε t z)
  change HasSum (fun g : gamma N =>
    strip.indicator (fun w => cap ε t w^2) (g.val • z)/weight N ε t z)
      (weight N ε t z/weight N ε t z) at hs
  rw [div_self hn] at hs
  exact hs.congr_fun (fun g => amplitude_norm_sq N hε ht g z)

#print axioms amplitude_measurable
#print axioms amplitude_norm_sq
#print axioms amplitude_hasSum

end AsymptoticCongruenceWeight
