module

public import AsymptoticReconstructionBranchV1
public import AsymptoticFoldMajorantV1
public import AsymptoticMassTransportV1
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFoldedLow

open MeasureTheory UpperHalfPlane Set Filter ContinuousLinearMap
open AsymptoticReconstructionBranch AsymptoticHyperbolicSlash

variable {L : ℝ} (hL : 0<L) (b d : ℝ)

noncomputable def fold (n : ℤ) : GL (Fin 2) ℝ := branch L b (d-n) hL.ne'

noncomputable def ratio (n : ℤ) (z : ℍ) : ℝ := z.im/(fold hL b d n • z).im

theorem ratio_pos (n : ℤ) (z : ℍ) : 0<ratio hL b d n z :=
  div_pos z.im_pos (fold hL b d n • z).im_pos

theorem ratio_continuous (n : ℤ) : Continuous (ratio hL b d n) :=
  continuous_im.div₀ (continuous_im.comp (continuous_const_smul (fold hL b d n)))
    (fun z => (fold hL b d n • z).im_ne_zero)

/-- Cell restrictions and the ascending-height cutoff for one fold.
The target region is later chosen to be the low part of the strip. -/
def region (s r : Set ℍ) (cap : ℝ) (n : ℤ) : Set ℍ :=
  (s∩(fun z => fold hL b d n • z) ⁻¹' r)∩{z | ratio hL b d n z≤cap}

theorem region_measurable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    (cap : ℝ) (n : ℤ) : MeasurableSet (region hL b d s r cap n) :=
  (hs.inter (hr.preimage (continuous_const_smul (fold hL b d n)).measurable)).inter
    (isClosed_le (ratio_continuous hL b d n) continuous_const).measurableSet

noncomputable def coefficient (s r : Set ℍ) (cap : ℝ) (t : ℕ) (n : ℤ) : ℍ → ℂ :=
  (region hL b d s r cap n).indicator (fun z => ((ratio hL b d n z^t : ℝ) : ℂ))

theorem coefficient_measurable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    (cap : ℝ) (t : ℕ) (n : ℤ) : Measurable (coefficient hL b d s r cap t n) :=
  ((Complex.continuous_ofReal.comp ((ratio_continuous hL b d n).pow t)).measurable).indicator
    (region_measurable hL b d hs hr cap n)

/-- A pointwise coefficient bound uniform over the whole strip. The
bound is summable in n; it is not merely a bound on one orbit's column. -/
theorem coefficient_norm_le {s r : Set ℍ} {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤d) (hd1 : d≤1) (hr : r⊆AsymptoticMassTransport.strip)
    (t : ℕ) (n : ℤ) (z : ℍ) :
    ‖coefficient hL b d s r cap t n z‖≤AsymptoticFoldMajorant.majorant cap (4/L) n^t := by
  classical
  by_cases hz : z∈region hL b d s r cap n
  · rw [coefficient,Set.indicator_of_mem hz,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (ratio_pos hL b d n z).le t)]
    apply pow_le_pow_left₀ (ratio_pos hL b d n z).le
    apply le_min hz.2
    split_ifs with hn
    · exact hz.2
    · have hw := hr hz.1.2
      have ha : |(fold hL b d n • z).re-d|≤1 := by
        change 0≤(fold hL b d n • z).re ∧ (fold hL b d n • z).re<1 at hw
        rw [abs_le]
        constructor <;> linarith
      rw [ratio,fold,folded_ratio hL]
      simpa only [fold,add_sub_assoc] using AsymptoticFoldMajorant.inverse_ratio_tail
        (v:=(fold hL b d n • z).im) ha hL (by omega : 1 < |n|)
  · rw [coefficient,Set.indicator_of_notMem hz,norm_zero]
    exact pow_nonneg (AsymptoticFoldMajorant.majorant_nonneg hcap (by positivity) n) t

/-- One actual Möbius pullback, with its cell and height multiplier and
the full weight-dependent slash phase retained. -/
noncomputable def term {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) (t m : ℕ) (n : ℤ) : Space →L[ℂ] Space :=
  (AsymptoticL2Multiplier.operator (coefficient hL b d s r cap t n)
    (coefficient_measurable hL b d hs hr cap t n).aestronglyMeasurable
    (Filter.Eventually.of_forall (coefficient_norm_le hL b d hcap hd0 hd1 hstrip t n))).comp
      (AsymptoticHyperbolicSlash.operator (fold hL b d n) (2*m))

theorem term_norm_le {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) (t m : ℕ) (n : ℤ) :
    ‖term hL b d hs hr hcap hd0 hd1 hstrip t m n‖≤
      AsymptoticFoldMajorant.majorant cap (4/L) n^t := by
  apply (opNorm_comp_le _ _).trans
  have h₁ := AsymptoticL2Multiplier.operator_norm_le (μ:=volume)
    (coefficient hL b d s r cap t n)
    (coefficient_measurable hL b d hs hr cap t n).aestronglyMeasurable
    (pow_nonneg (AsymptoticFoldMajorant.majorant_nonneg hcap (by positivity) n) t)
    (Filter.Eventually.of_forall (coefficient_norm_le hL b d hcap hd0 hd1 hstrip t n))
  have h₂ := AsymptoticHyperbolicSlash.operator_norm_le (fold hL b d n) (2*m)
  simpa only [mul_one] using mul_le_mul h₁ h₂ (norm_nonneg _)
    (pow_nonneg (AsymptoticFoldMajorant.majorant_nonneg hcap (by positivity) n) t)

theorem term_norm_summable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t) (m : ℕ) :
    Summable (fun n => ‖term hL b d hs hr hcap hd0 hd1 hstrip t m n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (term_norm_le hL b d hs hr hcap hd0 hd1 hstrip t m)
    (AsymptoticFoldMajorant.power_summable_bound hcap (by positivity : 0≤4/L) ht).1

theorem term_coeFn {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) (t m : ℕ) (n : ℤ) (f : Space) :
    term hL b d hs hr hcap hd0 hd1 hstrip t m n f =ᵐ[volume]
      (fun z => coefficient hL b d s r cap t n z*
        phase (fold hL b d n) (2*m) z*f (fold hL b d n • z)) := by
  have hc := AsymptoticL2Multiplier.operator_coeFn
    (coefficient hL b d s r cap t n)
    (coefficient_measurable hL b d hs hr cap t n).aestronglyMeasurable
    (Filter.Eventually.of_forall (coefficient_norm_le hL b d hcap hd0 hd1 hstrip t n))
    (AsymptoticHyperbolicSlash.operator (fold hL b d n) (2*m) f)
  filter_upwards [hc,AsymptoticHyperbolicSlash.operator_coeFn (fold hL b d n) (2*m) f]
    with z hz hf
  exact hz.trans (by rw [hf]; ring)

/-- The low-to-low branch operator is the sum over ALL integer folds,
convergent in operator norm by the explicit inverse-height majorant. -/
noncomputable def operator {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) (t m : ℕ) : Space →L[ℂ] Space :=
  ∑' n,term hL b d hs hr hcap hd0 hd1 hstrip t m n

theorem operator_norm_le {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t) (m : ℕ) :
    ‖operator hL b d hs hr hcap hd0 hd1 hstrip t m‖≤cap^(t-1)*(3*cap+16/L) := by
  have hsumm := term_norm_summable hL b d hs hr hcap hd0 hd1 hstrip ht m
  have hb := AsymptoticFoldMajorant.power_summable_bound hcap (by positivity : 0≤4/L) ht
  apply (norm_tsum_le_tsum_norm hsumm).trans
  have hh := (hsumm.tsum_le_tsum (term_norm_le hL b d hs hr hcap hd0 hd1 hstrip t m) hb.1).trans hb.2
  convert hh using 1
  ring

/-- The norm-convergent operator sum has the literal folded formula
almost everywhere, which is needed to substitute the analytic equations. -/
theorem operator_coeFn {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t) (m : ℕ) (f : Space) :
    operator hL b d hs hr hcap hd0 hd1 hstrip t m f =ᵐ[volume]
      (fun z => ∑' n,coefficient hL b d s r cap t n z*
        phase (fold hL b d n) (2*m) z*f (fold hL b d n • z)) := by
  have hn := term_norm_summable hL b d hs hr hcap hd0 hd1 hstrip ht m
  have hf : Summable (fun n => ‖term hL b d hs hr hcap hd0 hd1 hstrip t m n f‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => (term hL b d hs hr hcap hd0 hd1 hstrip t m n).le_opNorm f)
      (hn.mul_right ‖f‖)
  have he : operator hL b d hs hr hcap hd0 hd1 hstrip t m f=
      ∑' n,term hL b d hs hr hcap hd0 hd1 hstrip t m n f :=
    tsum_apply (Summable.of_norm hn) f
  rw [he]
  apply (Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hf)).trans
  have hterms := ae_all_iff.mpr
    (fun n => term_coeFn hL b d hs hr hcap hd0 hd1 hstrip t m n f)
  filter_upwards [hterms] with z hz
  exact tsum_congr hz

#print axioms coefficient_norm_le
#print axioms term_norm_summable
#print axioms operator_norm_le
#print axioms operator_coeFn

end AsymptoticFoldedLow
