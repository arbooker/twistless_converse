module

public import QuantitativeHolomorphicTransferV1
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open Filter Asymptotics

/-- The manuscript convention, with positive logarithmic base already at k=2. -/
def shiftedRemainderScale (δ k : ℝ) : ℝ := k * (Real.log (Real.log (2*k))) ^ (-δ)

theorem shifted_loglog_pos {k : ℝ} (hk : 2 ≤ k) : 0 < Real.log (Real.log (2*k)) := by
  apply Real.log_pos
  rw [Real.lt_log_iff_exp_lt (by linarith : 0 < 2*k)]
  linarith [Real.exp_one_lt_three]

theorem shiftedRemainderScale_pos (δ : ℝ) {k : ℝ} (hk : 2 ≤ k) :
    0 < shiftedRemainderScale δ k :=
  mul_pos (by linarith) (Real.rpow_pos_of_pos (shifted_loglog_pos hk) _)

/-- The two logarithmic conventions have the same precise asymptotic scale,
for every real exponent, not only the positive exponents used in the theorem. -/
theorem shiftedRemainderScale_equivalent (δ : ℝ) :
    (fun k : ℕ => shiftedRemainderScale δ k) ~[atTop]
      (fun k : ℕ => remainderScale δ k) := by
  have ht : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp ht
  have hlog : (fun k : ℕ => Real.log (2*(k : ℝ))) ~[atTop] (fun k : ℕ => Real.log (k : ℝ)) := by
    have he := (IsEquivalent.refl (u := fun k : ℕ => Real.log (k : ℝ))).const_add_of_norm_tendsto_atTop
      (c := Real.log 2) (tendsto_norm_atTop_atTop.comp ht)
    apply he.congr_left
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [Real.log_mul (by norm_num) (by exact_mod_cast (show k ≠ 0 by omega))]
  have he := hlog.log ht
  have hc : (fun k : ℕ => Real.log (Real.log (k : ℝ))) =ᶠ[atTop]
      (fun k : ℕ => max (Real.log (Real.log (k : ℝ))) 0) := by
    filter_upwards [hL.eventually (eventually_ge_atTop 0)] with k hk
    exact (max_eq_left hk).symm
  have hp := (he.congr_right hc).rpow (r := -δ) (fun k => le_max_right _ _)
  have hp' : (fun k : ℕ => (Real.log (Real.log (2*(k : ℝ)))) ^ (-δ)) ~[atTop]
      (fun k : ℕ => (Real.log (Real.log (k : ℝ))) ^ (-δ)) := by
    apply hp.congr_right
    filter_upwards [hc] with k hk
    exact congrArg (fun x : ℝ => x ^ (-δ)) hk.symm
  exact (IsEquivalent.refl (u := fun k : ℕ => (k : ℝ))).mul hp'

/-- Transport an already-proved error bound to the corrected manuscript
notation along any subfilter, including the even-weight filter. -/
theorem isBigO_shiftedRemainderScale_iff {l : Filter ℕ} (hl : l ≤ atTop)
    (f : ℕ → ℝ) (δ : ℝ) :
    f =O[l] (fun k : ℕ => remainderScale δ k) ↔
      f =O[l] (fun k : ℕ => shiftedRemainderScale δ k) := by
  constructor
  · intro h
    exact h.trans ((shiftedRemainderScale_equivalent δ).isBigO_symm.mono hl)
  · intro h
    exact h.trans ((shiftedRemainderScale_equivalent δ).isBigO.mono hl)

#print axioms shifted_loglog_pos
#print axioms shiftedRemainderScale_equivalent
#print axioms isBigO_shiftedRemainderScale_iff

end QuantitativeHolomorphic
