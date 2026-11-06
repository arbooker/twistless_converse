module

public import AsymptoticCongruenceStripV1
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceWeight

open Matrix UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip
open AsymptoticCompactBranch AsymptoticMassTransport
open scoped MatrixGroups

/-- The squared cap is bounded by the convergent integral-lattice
Eisenstein majorant of weight `4*t`. -/
theorem cap_sq_le_eis {ε : ℝ} (hε : 0<ε) (t : ℕ) (A : SL(2,ℤ)) (z : ℍ) :
    cap ε t (A • z)^2≤(z.im/ε)^(2*t)*
      ‖EisensteinSeries.eisSummand ((4*t:ℕ):ℤ) (A.val 1) z‖ := by
  have hcap : cap ε t (A • z)^2≤((A • z).im/ε)^(2*t) := by
    rw [cap,← pow_mul,Nat.mul_comm t 2]
    exact pow_le_pow_left₀ (le_min (le_of_lt (div_pos (A • z).im_pos hε)) zero_le_one)
      (min_le_left _ _) _
  apply hcap.trans_eq
  rw [ModularGroup.im_smul_eq_div_normSq,ModularGroup.denom_apply,
    Complex.normSq_eq_norm_sq]
  have hp : (‖(A.val 1 0:ℂ)*z+(A.val 1 1:ℂ)‖^2)^(2*t)=
      ‖(A.val 1 0:ℂ)*z+(A.val 1 1:ℂ)‖^(4*t) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [div_pow,div_pow,hp]
  simp only [EisensteinSeries.eisSummand,_root_.zpow_neg,zpow_natCast,norm_inv,norm_pow,div_pow]
  ring

/-- The selected strip representatives have no repeated lower rows,
so the full lattice Eisenstein series dominates their cap weights. -/
theorem strip_summable (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Summable (fun g : Strip N z => cap ε t (g.val.val • z)^2) := by
  have he := (EisensteinSeries.summable_norm_eisSummand
    (k:=((4*t:ℕ):ℤ)) (by omega) z).comp_injective (bottom_injective N z)
  apply (he.mul_left ((z.im/ε)^(2*t))).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro g
  have hg := cap_sq_le_eis hε t (representative g.val) z
  rw [← integralLabel_action,representative_label] at hg
  exact hg

/-- Sum over the projective congruence subgroup with a strip cutoff.
This counts each integral-translation class exactly once. -/
noncomputable def weight (N : ℕ) (ε : ℝ) (t : ℕ) (z : ℍ) : ℝ :=
  ∑' g : gamma N,strip.indicator (fun w => cap ε t w^2) (g.val • z)

theorem weight_summable (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Summable (fun g : gamma N => strip.indicator (fun w => cap ε t w^2) (g.val • z)) := by
  have he := (summable_subtype_iff_indicator
    (s:={g : gamma N | g.val • z∈strip})
    (f:=fun g : gamma N => cap ε t (g.val • z)^2)).mp (strip_summable N hε ht z)
  apply he.congr
  intro g
  rfl

theorem weight_measurable (N : ℕ) (ε : ℝ) (t : ℕ) : Measurable (weight N ε t) := by
  apply Measurable.tsum
  intro g
  exact (((cap_continuous ε t).pow 2).measurable.indicator strip_measurable).comp
    (AsymptoticRationalGroup.measurePreserving g.val).measurable

theorem weight_invariant (N : ℕ) (ε : ℝ) (t : ℕ) (h : gamma N) (z : ℍ) :
    weight N ε t (h.val • z)=weight N ε t z := by
  have he := (Equiv.mulRight h).tsum_eq
      (fun g : gamma N => strip.indicator (fun w => cap ε t w^2) (g.val • z))
  change (∑' g : gamma N,strip.indicator (fun w => cap ε t w^2) ((g*h).val • z))=_ at he
  simpa only [weight,Subgroup.coe_mul,mul_smul] using he

theorem weight_lower (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    cap ε t z^2≤weight N ε t z := by
  let n : ℤ := -Int.floor z.re
  let g : gamma N := ⟨AsymptoticIntegralSubgroup.translationLabel (n:ℚ),translation_mem N n⟩
  have hg : g.val • z∈strip := by
    change 0≤(AsymptoticIntegralSubgroup.translationLabel (n:ℚ) • z).re ∧
      (AsymptoticIntegralSubgroup.translationLabel (n:ℚ) • z).re<1
    rw [translation_re]
    dsimp only [n]
    push_cast
    constructor <;> linarith [Int.floor_le z.re,Int.lt_floor_add_one z.re]
  have he := (weight_summable N hε ht z).le_tsum g
    (fun a _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
  simpa only [weight,Set.indicator_of_mem hg,g,AsymptoticCompactTranslation.cap_translate] using he

theorem weight_pos (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    0<weight N ε t z :=
  (sq_pos_of_pos (cap_pos hε t z)).trans_le (weight_lower N hε ht z)

#print axioms cap_sq_le_eis
#print axioms strip_summable
#print axioms weight_summable
#print axioms weight_measurable
#print axioms weight_invariant
#print axioms weight_lower
#print axioms weight_pos

end AsymptoticCongruenceWeight
