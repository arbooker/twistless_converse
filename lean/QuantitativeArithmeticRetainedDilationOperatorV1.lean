module

public import AsymptoticMobiusFoldV1
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedDilationOperator

open UpperHalfPlane Matrix MeasureTheory Set Filter ContinuousLinearMap
open AsymptoticHyperbolicSlash AsymptoticMobiusFold

/-- The actual retained branch, including an arbitrary real translation. -/
def affine (a b : ℝ) (ha : 0<a) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a,b;0,1] (by simpa using ha.ne')

theorem affine_det (a b : ℝ) (ha : 0<a) : (affine a b ha).det.val=a := by
  change Matrix.det !![a,b;0,1]=a
  simp

theorem affine_action (a b : ℝ) (ha : 0<a) (z : ℍ) :
    ((affine a b ha • z : ℍ):ℂ)=(a:ℂ)*(z:ℂ)+(b:ℂ) := by
  rw [coe_smul_of_det_pos (by rw [affine_det]; exact ha)]
  change ((a:ℂ)*(z:ℂ)+(b:ℂ))/((0:ℂ)*(z:ℂ)+1)=_
  simp

theorem affine_im (a b : ℝ) (ha : 0<a) (z : ℍ) :
    (affine a b ha • z).im=a*z.im := by
  simpa using congrArg Complex.im (affine_action a b ha z)

theorem affine_re (a b : ℝ) (ha : 0<a) (z : ℍ) :
    (affine a b ha • z).re=a*z.re+b := by
  simpa using congrArg Complex.re (affine_action a b ha z)

theorem affine_phase (a b : ℝ) (ha : 0<a) (k : ℕ) (z : ℍ) :
    phase (affine a b ha) k z=1 := by
  have hd : denom (affine a b ha) z=1 := by
    change (0:ℂ)*(z:ℂ)+1=1
    ring
  simp [phase,hd]

/-- All folds meeting the source strip, independent of weight and height. -/
def folds (a b : ℝ) : Finset ℤ := Finset.Icc ⌊b⌋ ⌊a+b⌋

theorem selected_mem (a b : ℝ) (ha : 0<a) (z : ℍ)
    (hz : z∈AsymptoticMassTransport.strip) :
    Int.floor (affine a b ha • z).re∈folds a b := by
  change 0≤z.re ∧ z.re<1 at hz
  rw [folds,Finset.mem_Icc,affine_re]
  constructor <;> apply Int.floor_mono <;> nlinarith

theorem folded_phase (a b : ℝ) (ha : 0<a) (n : ℤ) (k : ℕ) (z : ℍ) :
    phase (fold (affine a b ha) n) k z=1 := by
  rw [fold_phase _ (by rw [affine_det]; exact ha),affine_phase]

theorem height_ratio (a b : ℝ) (ha : 0<a) (n : ℤ) (z : ℍ) :
    z.im/(fold (affine a b ha) n • z).im=a⁻¹ := by
  rw [fold_im,affine_im]
  field_simp

/-- Normalization removes the whole weight dependence of the ramified
multiplier except for beta/a^m. This is an equality, not an absolute-value
replacement of a slash phase. -/
theorem normalized_branch (a b : ℝ) (ha : 0<a) (β : ℂ) (m t : ℕ)
    (F : ℍ → ℂ) (z : ℍ) :
    (z.im:ℂ)^(m+t)*β*F (affine a b ha • z)=
      (β/(a:ℂ)^m)*(a:ℂ)⁻¹^t*
        (((affine a b ha • z).im:ℂ)^(m+t)*F (affine a b ha • z)) := by
  rw [affine_im]
  push_cast
  have haC : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [mul_pow,pow_add (a:ℂ),inv_pow]
  field_simp [haC]

/-- The finite-fold pieces use the actual source and target regions. -/
def region (a b : ℝ) (ha : 0<a) (s r : Set ℍ) (n : ℤ) : Set ℍ :=
  s∩(fun z => fold (affine a b ha) n • z) ⁻¹' r

theorem region_measurable (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (n : ℤ) :
    MeasurableSet (region a b ha s r n) :=
  hs.inter (hr.preimage (continuous_const_smul _).measurable)

def coefficient (a b : ℝ) (ha : 0<a) (s r : Set ℍ) (n : ℤ) : ℍ → ℂ :=
  (region a b ha s r n).indicator (fun _ => 1)

theorem coefficient_measurable (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (n : ℤ) :
    Measurable (coefficient a b ha s r n) :=
  measurable_const.indicator (region_measurable a b ha hs hr n)

theorem coefficient_norm_le (a b : ℝ) (ha : 0<a) (s r : Set ℍ) (n : ℤ) (z : ℍ) :
    ‖coefficient a b ha s r n z‖≤1 := by
  classical
  by_cases hz : z∈region a b ha s r n <;> simp [coefficient,hz]

/-- Restricted actual affine slash on hyperbolic L2. -/
def term (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (k : ℕ) (n : ℤ) : Space →L[ℂ] Space :=
  (AsymptoticL2Multiplier.operator (coefficient a b ha s r n)
    (coefficient_measurable a b ha hs hr n).aestronglyMeasurable
    (Eventually.of_forall (coefficient_norm_le a b ha s r n))).comp
      (AsymptoticHyperbolicSlash.operator (fold (affine a b ha) n) k)

theorem term_norm_le (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (k : ℕ) (n : ℤ) :
    ‖term a b ha hs hr k n‖≤1 := by
  apply (opNorm_comp_le _ _).trans
  have h₁ := AsymptoticL2Multiplier.operator_norm_le (μ:=volume)
    (coefficient a b ha s r n)
    (coefficient_measurable a b ha hs hr n).aestronglyMeasurable zero_le_one
    (Eventually.of_forall (coefficient_norm_le a b ha s r n))
  have h₂ := AsymptoticHyperbolicSlash.operator_norm_le (fold (affine a b ha) n) k
  simpa only [one_mul] using mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one

theorem term_coeFn (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (k : ℕ) (n : ℤ) (f : Space) :
    term a b ha hs hr k n f =ᵐ[volume]
      fun z => coefficient a b ha s r n z*f (fold (affine a b ha) n • z) := by
  have hc := AsymptoticL2Multiplier.operator_coeFn
    (coefficient a b ha s r n)
    (coefficient_measurable a b ha hs hr n).aestronglyMeasurable
    (Eventually.of_forall (coefficient_norm_le a b ha s r n))
    (AsymptoticHyperbolicSlash.operator (fold (affine a b ha) n) k f)
  filter_upwards [hc,AsymptoticHyperbolicSlash.operator_coeFn
    (fold (affine a b ha) n) k f] with z hc hf
  rw [show term a b ha hs hr k n f z=_ from hc,hf,folded_phase,one_mul]

/-- Complete strip folding is finite for an affine retained branch. -/
def folded (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (k : ℕ) : Space →L[ℂ] Space :=
  ∑ n∈folds a b,term a b ha hs hr k n

theorem folded_norm_le (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (k : ℕ) :
    ‖folded a b ha hs hr k‖≤(folds a b).card := by
  apply (norm_sum_le _ _).trans
  exact (Finset.sum_le_sum (fun n _ => term_norm_le a b ha hs hr k n)).trans_eq (by simp)

/-- The extra radial exponent makes these branches strict contractions,
uniformly in weight and in every normalized ramified multiplier of norm at most one. -/
def weighted (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (β : ℂ) (t k : ℕ) : Space →L[ℂ] Space :=
  (β*((a⁻¹^t:ℝ):ℂ)) • folded a b ha hs hr k

theorem weighted_norm_le (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) {β : ℂ} (hβ : ‖β‖≤1) (t k : ℕ) :
    ‖weighted a b ha hs hr β t k‖≤a⁻¹^t*(folds a b).card := by
  rw [weighted,norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr ha.le) t)]
  apply mul_le_mul _ (folded_norm_le a b ha hs hr k) (norm_nonneg _)
    (pow_nonneg (inv_nonneg.mpr ha.le) t)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hβ
    (pow_nonneg (inv_nonneg.mpr ha.le) t)

theorem contraction (a b : ℝ) (ha : 1<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) :
    ∃ t₀ : ℕ, ∀ t≥t₀, ∀ β : ℂ, ‖β‖≤1 → ∀ k : ℕ,
      ‖weighted a b (by linarith) hs hr β t k‖<1/2 := by
  have ha0 : 0<a := by linarith
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr ha0.le) ((inv_lt_one₀ ha0).mpr ha)).mul_const ((folds a b).card:ℝ)
  simp only [zero_mul] at h
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  exact ⟨t₀,fun t ht β hβ k => (weighted_norm_le a b ha0 hs hr hβ t k).trans_lt (ht₀ t ht)⟩


/-- No nonselected fold contributes when the target lies in the unit strip. -/
theorem coefficient_zero (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hr : r⊆AsymptoticMassTransport.strip) (n : ℤ) (z : ℍ)
    (hn : n≠Int.floor (affine a b ha • z).re) :
    coefficient a b ha s r n z=0 := by
  apply Set.indicator_of_notMem
  intro hz
  exact hn ((fold_mem_strip_iff _ n z).mp (hr hz.2))

/-- The finite sum is the actual periodic pullback, with no missing folds. -/
theorem folded_value (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : s⊆AsymptoticMassTransport.strip) (hr : r⊆AsymptoticMassTransport.strip)
    (f : ℍ → ℂ) (z : ℍ) (hz : z∈s) :
    (∑ n∈folds a b,coefficient a b ha s r n z*f (fold (affine a b ha) n • z))=
      r.indicator f (fold (affine a b ha) (Int.floor (affine a b ha • z).re) • z) := by
  classical
  rw [Finset.sum_eq_single (Int.floor (affine a b ha • z).re)]
  · by_cases hw : fold (affine a b ha) (Int.floor (affine a b ha • z).re) • z∈r
    · simp [coefficient,region,hz,hw]
    · simp [coefficient,region,hz,hw]
  · intro n _ hn
    rw [coefficient_zero a b ha hr n z hn,zero_mul]
  · intro hn
    exact False.elim (hn (selected_mem a b ha z (hs hz)))

theorem folded_coeFn (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (k : ℕ) (f : Space) :
    folded a b ha hs hr k f =ᵐ[volume]
      fun z => ∑ n∈folds a b,coefficient a b ha s r n z*f (fold (affine a b ha) n • z) := by
  simp only [folded,_root_.sum_apply]
  apply (Lp.coeFn_finsetSum _ _).trans
  have h : (fun z : ℍ => ∑ n∈folds a b,
      coefficient a b ha s r n z*f (fold (affine a b ha) n • z))=
      ∑ n∈folds a b,fun z : ℍ =>
        coefficient a b ha s r n z*f (fold (affine a b ha) n • z) := by
    funext z
    simp only [Finset.sum_apply]
  rw [h]
  apply eventuallyEq_sum
  intro n _
  exact term_coeFn a b ha hs hr k n f

/-- The original ramified complete-row bound supplies a bounded normalized
amplitude, including the identically zero highly ramified case. -/
theorem normalized_amplitude (a : ℝ) (ha : 0<a) (m : ℕ) (β : ℂ)
    (hβ : ‖β‖≤a^m) : ‖β/(a:ℂ)^m‖≤1 := by
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  exact (div_le_one (pow_pos ha m)).mpr hβ

/-- The same rho used for Fricke branches controls every retained prime.
Consequently a single increased exponent contracts the whole mixed system. -/
theorem weighted_norm_le_rho (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) {β : ℂ} (hβ : ‖β‖≤1)
    {ρ : ℝ} (hρ : a⁻¹≤ρ) (t k : ℕ) :
    ‖weighted a b ha hs hr β t k‖≤ρ^t*(folds a b).card := by
  apply (weighted_norm_le a b ha hs hr hβ t k).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (inv_nonneg.mpr ha.le) hρ t) (Nat.cast_nonneg _)


/-- The capped radial factor in the existing cylinder realization. -/
def capWeight (ε : ℝ) (t : ℕ) (z : ℍ) : ℂ := ((min (z.im/ε) 1)^t:ℝ)

theorem capWeight_measurable (ε : ℝ) (t : ℕ) : Measurable (capWeight ε t) := by
  have h : Continuous (capWeight ε t) := by unfold capWeight; fun_prop
  exact h.measurable

theorem capWeight_norm_le (ε : ℝ) (hε : 0<ε) (t : ℕ) (z : ℍ) :
    ‖capWeight ε t z‖≤1 := by
  have h0 : 0≤min (z.im/ε) 1 := le_min (by positivity) zero_le_one
  rw [capWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg h0 t)]
  exact pow_le_one₀ h0 (min_le_right _ _)

def capOperator (ε : ℝ) (hε : 0<ε) (t : ℕ) : Space →L[ℂ] Space :=
  AsymptoticL2Multiplier.operator (capWeight ε t)
    (capWeight_measurable ε t).aestronglyMeasurable
    (Eventually.of_forall (capWeight_norm_le ε hε t))

theorem capOperator_norm_le (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    ‖capOperator ε hε t‖≤1 :=
  AsymptoticL2Multiplier.operator_norm_le _ _ zero_le_one _

/-- For a target above the cutoff the radial quotient is just the capped
source factor. Thus the terminal operator has a weight-independent bound. -/
def terminal (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (ε : ℝ) (hε : 0<ε)
    (β : ℂ) (t k : ℕ) : Space →L[ℂ] Space :=
  β • (capOperator ε hε t).comp (folded a b ha hs hr k)

theorem terminal_norm_le (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (ε : ℝ) (hε : 0<ε)
    {β : ℂ} (hβ : ‖β‖≤1) (t k : ℕ) :
    ‖terminal a b ha hs hr ε hε β t k‖≤(folds a b).card := by
  rw [terminal,norm_smul]
  apply (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg β)).trans
  calc
    ‖β‖ * (‖capOperator ε hε t‖ * ‖folded a b ha hs hr k‖) ≤
        1*(1*((folds a b).card:ℝ)) :=
      mul_le_mul hβ (mul_le_mul (capOperator_norm_le ε hε t)
        (folded_norm_le a b ha hs hr k) (norm_nonneg _) zero_le_one)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ = _ := by ring

/-- The terminal formula is the actual finite-fold pullback with its capped
radial multiplier, not an abstract bounded operator chosen afterward. -/
theorem terminal_coeFn (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (ε : ℝ) (hε : 0<ε)
    (β : ℂ) (t k : ℕ) (f : Space) :
    terminal a b ha hs hr ε hε β t k f =ᵐ[volume]
      fun z => β*capWeight ε t z*
        ∑ n∈folds a b,coefficient a b ha s r n z*f (fold (affine a b ha) n • z) := by
  have hc := AsymptoticL2Multiplier.operator_coeFn (capWeight ε t)
    (capWeight_measurable ε t).aestronglyMeasurable
    (Eventually.of_forall (capWeight_norm_le ε hε t)) (folded a b ha hs hr k f)
  filter_upwards [Lp.coeFn_smul β (capOperator ε hε t (folded a b ha hs hr k f)),
    hc,folded_coeFn a b ha hs hr k f] with z hsm hc hf
  change (β • capOperator ε hε t (folded a b ha hs hr k f)) z=_
  rw [hsm]
  change β*(capOperator ε hε t (folded a b ha hs hr k f) z)=_
  rw [show capOperator ε hε t (folded a b ha hs hr k f) z=_ from hc,hf]
  ring

#print axioms terminal_norm_le
#print axioms terminal_coeFn
#print axioms folded_value
#print axioms folded_coeFn
#print axioms normalized_amplitude
#print axioms weighted_norm_le_rho
#print axioms selected_mem
#print axioms height_ratio
#print axioms normalized_branch
#print axioms term_coeFn
#print axioms weighted_norm_le
#print axioms contraction

end QuantitativeArithmeticRetainedDilationOperator
