module

public import AsymptoticFoldedLowV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFoldedTerminal

open MeasureTheory UpperHalfPlane Set Filter ContinuousLinearMap
open AsymptoticReconstructionBranch AsymptoticHyperbolicSlash AsymptoticFoldedLow

variable {L : ℝ} (hL : 0<L) (b d : ℝ)

def region (s r : Set ℍ) (n : ℤ) : Set ℍ := s∩(fun z => fold hL b d n • z) ⁻¹' r

theorem region_measurable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    (n : ℤ) : MeasurableSet (region hL b d s r n) :=
  hs.inter (hr.preimage (continuous_const_smul (fold hL b d n)).measurable)

noncomputable def coefficient (s r : Set ℍ) (ε : ℝ) (t : ℕ) (n : ℤ) : ℍ → ℂ :=
  (region hL b d s r n).indicator (fun z => (((z.im/ε)^t : ℝ) : ℂ))

theorem coefficient_measurable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    (ε : ℝ) (t : ℕ) (n : ℤ) : Measurable (coefficient hL b d s r ε t n) :=
  ((Complex.continuous_ofReal.comp ((continuous_im.div_const ε).pow t)).measurable).indicator
    (region_measurable hL b d hs hr n)

theorem source_height {ε : ℝ} (hε : 0<ε) (n : ℤ) (z : ℍ) :
    z.im/ε=(fold hL b d n • z).im/
      (ε*L*(((n:ℝ)+(fold hL b d n • z).re-d)^2+(fold hL b d n • z).im^2)) := by
  have hh := inverse_height hL b (d-n) z
  change z.im=(fold hL b d n • z).im/
    (L*(((fold hL b d n • z).re-(d-n))^2+(fold hL b d n • z).im^2)) at hh
  rw [hh]
  have he : (fold hL b d n • z).re-(d-(n:ℝ))=(n:ℝ)+(fold hL b d n • z).re-d := by ring
  rw [he]
  field_simp

/-- For t≥2 the terminal coefficient is dominated by one summable
sequence independent of both t and the holomorphic weight. -/
theorem coefficient_norm_le {s r : Set ℍ} {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤d) (hd1 : d≤1) (hs : s⊆{z | z.im≤ε})
    (hr : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (n : ℤ) (z : ℍ) :
    ‖coefficient hL b d s r ε t n z‖≤AsymptoticFoldMajorant.majorant 1 ((ε*L)^2)⁻¹ n := by
  classical
  by_cases hz : z∈region hL b d s r n
  · have hy0 : 0≤z.im/ε := div_nonneg z.im_pos.le hε.le
    have hy1 : z.im/ε≤1 := (div_le_one hε).mpr (hs hz.1)
    rw [coefficient,Set.indicator_of_mem hz,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hy0 t)]
    have hp1 : (z.im/ε)^t≤1 := pow_le_one₀ hy0 hy1
    apply le_min hp1
    split_ifs with hn
    · exact hp1
    · have hw := hr hz.2
      have ha : |(fold hL b d n • z).re-d|≤1 := by
        change 0≤(fold hL b d n • z).re ∧ (fold hL b d n • z).re<1 at hw
        rw [abs_le]
        constructor <;> linarith
      have hb : z.im/ε≤(ε*L*|(n:ℝ)|)⁻¹ := by
        rw [source_height hL b d hε n z]
        simpa only [add_sub_assoc] using AsymptoticFoldMajorant.terminal_ratio_tail
          ha hL hε (fold hL b d n • z).im_pos (by omega : 1 < |n|)
      calc
        (z.im/ε)^t≤(z.im/ε)^2 := pow_le_pow_of_le_one hy0 hy1 ht
        _ ≤ ((ε*L*|(n:ℝ)|)⁻¹)^2 := pow_le_pow_left₀ hy0 hb 2
        _ = _ := by rw [inv_pow,mul_pow,sq_abs,mul_inv]
  · rw [coefficient,Set.indicator_of_notMem hz,norm_zero]
    exact AsymptoticFoldMajorant.majorant_nonneg zero_le_one (by positivity) n

noncomputable def term {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (n : ℤ) : Space →L[ℂ] Space :=
  (AsymptoticL2Multiplier.operator (coefficient hL b d s r ε t n)
    (coefficient_measurable hL b d hs hr ε t n).aestronglyMeasurable
    (Filter.Eventually.of_forall (coefficient_norm_le hL b d hε hd0 hd1 hsource hstrip ht n))).comp
      (AsymptoticHyperbolicSlash.operator (fold hL b d n) (2*m))

theorem term_norm_le {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (n : ℤ) :
    ‖term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n‖≤
      AsymptoticFoldMajorant.majorant 1 ((ε*L)^2)⁻¹ n := by
  apply (opNorm_comp_le _ _).trans
  have h₁ := AsymptoticL2Multiplier.operator_norm_le (μ:=volume)
    (coefficient hL b d s r ε t n)
    (coefficient_measurable hL b d hs hr ε t n).aestronglyMeasurable
    (AsymptoticFoldMajorant.majorant_nonneg zero_le_one (by positivity) n)
    (Filter.Eventually.of_forall (coefficient_norm_le hL b d hε hd0 hd1 hsource hstrip ht n))
  have h₂ := AsymptoticHyperbolicSlash.operator_norm_le (fold hL b d n) (2*m)
  simpa only [mul_one] using mul_le_mul h₁ h₂ (norm_nonneg _)
    (AsymptoticFoldMajorant.majorant_nonneg zero_le_one (by positivity) n)

theorem term_norm_summable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) :
    Summable (fun n => ‖term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (term_norm_le hL b d hs hr hε hd0 hd1 hsource hstrip ht m)
    (AsymptoticFoldMajorant.majorant_summable_bound zero_le_one (by positivity)).1

theorem term_coeFn {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (n : ℤ) (f : Space) :
    term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n f =ᵐ[volume]
      (fun z => coefficient hL b d s r ε t n z*
        phase (fold hL b d n) (2*m) z*f (fold hL b d n • z)) := by
  have hc := AsymptoticL2Multiplier.operator_coeFn
    (coefficient hL b d s r ε t n)
    (coefficient_measurable hL b d hs hr ε t n).aestronglyMeasurable
    (Filter.Eventually.of_forall (coefficient_norm_le hL b d hε hd0 hd1 hsource hstrip ht n))
    (AsymptoticHyperbolicSlash.operator (fold hL b d n) (2*m) f)
  filter_upwards [hc,AsymptoticHyperbolicSlash.operator_coeFn (fold hL b d n) (2*m) f]
    with z hz hf
  exact hz.trans (by rw [hf]; ring)

/-- The actual low-to-terminal operator, retaining every integer fold. -/
noncomputable def operator {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) : Space →L[ℂ] Space :=
  ∑' n,term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n

theorem operator_norm_le {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) :
    ‖operator hL b d hs hr hε hd0 hd1 hsource hstrip ht m‖≤3+4*((ε*L)^2)⁻¹ := by
  have hn := term_norm_summable hL b d hs hr hε hd0 hd1 hsource hstrip ht m
  have hb := AsymptoticFoldMajorant.majorant_summable_bound zero_le_one
    (by positivity : 0≤((ε*L)^2)⁻¹)
  apply (norm_tsum_le_tsum_norm hn).trans
  simpa only [mul_one] using (hn.tsum_le_tsum
    (term_norm_le hL b d hs hr hε hd0 hd1 hsource hstrip ht m) hb.1).trans hb.2

theorem operator_coeFn {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (f : Space) :
    operator hL b d hs hr hε hd0 hd1 hsource hstrip ht m f =ᵐ[volume]
      (fun z => ∑' n,coefficient hL b d s r ε t n z*
        phase (fold hL b d n) (2*m) z*f (fold hL b d n • z)) := by
  have hn := term_norm_summable hL b d hs hr hε hd0 hd1 hsource hstrip ht m
  have hf : Summable (fun n => ‖term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n f‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => (term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n).le_opNorm f)
      (hn.mul_right ‖f‖)
  have he : operator hL b d hs hr hε hd0 hd1 hsource hstrip ht m f=
      ∑' n,term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n f :=
    tsum_apply (Summable.of_norm hn) f
  rw [he]
  apply (Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hf)).trans
  have hterms := ae_all_iff.mpr
    (fun n => term_coeFn hL b d hs hr hε hd0 hd1 hsource hstrip ht m n f)
  filter_upwards [hterms] with z hz
  exact tsum_congr hz

#print axioms coefficient_norm_le
#print axioms term_norm_summable
#print axioms operator_norm_le
#print axioms operator_coeFn

end AsymptoticFoldedTerminal
