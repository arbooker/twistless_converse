module

public import AsymptoticRamifiedBranchV1
public import AsymptoticRamifiedFourierV1
public import AsymptoticTwistObservationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRamifiedObservation

open MeasureTheory UpperHalfPlane Set Filter AsymptoticHyperbolicSlash
open AsymptoticCompactBranch AsymptoticRamifiedBranch AsymptoticWeightedBranches
open FinitenessFourierConstruction FinitenessPolynomialSeries

noncomputable def average (p : ℕ) (hp : 0<p) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) : Space →L[ℂ] Space :=
  ∑ a ∈ Finset.range p,compactOperator (branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne')) hs hε t m

noncomputable def bound (p : ℕ) (hp : 0<p) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  ∑ a ∈ Finset.range p,AsymptoticTwistObservation.branchBound
    (branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne')) hs hε t

theorem bound_nonneg (p : ℕ) (hp : 0<p) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : 0≤bound p hp hs hε t :=
  Finset.sum_nonneg (fun _a _ => AsymptoticTwistObservation.branchBound_nonneg _ _ _ _)

noncomputable def residual (p : ℕ) (hp : 0<p) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (δ : ℂ) : Space →L[ℂ] Space :=
  average p hp hs hε t m-δ • compactOperator 1 hs hε t m

theorem residual_norm_le (p : ℕ) (hp : 0<p) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (δ : ℂ) :
    ‖residual p hp hs hε t m δ‖≤bound p hp hs hε t+
      ‖δ‖*AsymptoticTwistObservation.branchBound 1 hs hε t := by
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun a _ => compactOperator_norm_le _ hs hε t m)
  · exact mul_le_mul_of_nonneg_left (compactOperator_norm_le 1 hs hε t m) (norm_nonneg _)

theorem average_on_section (p : ℕ) (hp : 0<p) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (F : ℂ → ℂ) (hper : ∀ z,F (z+1)=F z)
    (u : Space) (hu : u =ᵐ[volume] stripSection ε t m F) :
    average p hp hs hε t m u =ᵐ[volume] s.indicator (fun z : ℍ =>
      (cap ε t z:ℂ)*(z.im:ℂ)^m/(p:ℂ)^m*∑ a ∈ Finset.range p,F (((z:ℂ)+(a:ℂ))/p)) := by
  rw [average,_root_.sum_apply]
  apply (Lp.coeFn_fun_finsetSum _ _).trans
  have he : ∀ᵐ z ∂volume,∀ a : ℕ,
      compactOperator (branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne')) hs hε t m u z=
        s.indicator (fun w : ℍ => (cap ε t w:ℂ)*
          phase (branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne')) (2*m) w*
          ((branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne') • w).im:ℂ)^m*
          F (branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne') • w:ℍ)) z :=
    ae_all_iff.mpr (fun a => compactOperator_on_section
      (branch (p:ℝ) (a:ℝ) (by exact_mod_cast hp.ne'))
      (by rw [branch_det]; exact_mod_cast hp) hs hε t m F hper u hu)
  filter_upwards [he] with z hz
  classical
  by_cases hzs : z∈s
  · rw [Set.indicator_of_mem hzs,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [hz a,Set.indicator_of_mem hzs]
    have hn := normalized_branch (show (0:ℝ)<p by exact_mod_cast hp) (a:ℝ) m F z
    simp only [Complex.ofReal_natCast] at hn
    linear_combination (cap ε t z:ℂ)*hn
  · rw [Set.indicator_of_notMem hzs]
    apply Finset.sum_eq_zero
    intro a _
    rw [hz a,Set.indicator_of_notMem hzs]

theorem identity_on_section {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t m : ℕ) (F : ℂ → ℂ) (hper : ∀ z,F (z+1)=F z)
    (u : Space) (hu : u =ᵐ[volume] stripSection ε t m F) :
    compactOperator 1 hs hε t m u =ᵐ[volume]
      s.indicator (fun z : ℍ => (cap ε t z:ℂ)*(z.im:ℂ)^m*F z) := by
  have he := compactOperator_on_section 1 (by simp) hs hε t m F hper u hu
  simpa only [phase_one,one_smul,mul_one] using he

/-- The actual ramified recurrence yields a vanishing compact residual
with no additional functional equation hypothesis. -/
theorem residual_eq_zero (p : ℕ) (hp : 0<p) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t h : ℕ) (δ : ℂ) (a : ℕ → ℂ) (ha : PolynomialBound a)
    (hrow : ∀ n,a (p*n)=δ*(p:ℂ)^h*a n)
    (u : Space) (hu : u =ᵐ[volume] stripSection ε t (h+1) (fourier a)) :
    residual p hp hs hε t (h+1) δ u=0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (average p hp hs hε t (h+1) u)
      (δ • compactOperator 1 hs hε t (h+1) u),
    Lp.coeFn_smul δ (compactOperator 1 hs hε t (h+1) u),
    average_on_section p hp hs hε t (h+1) (fourier a) (periodic a) u hu,
    identity_on_section hs hε t (h+1) (fourier a) (periodic a) u hu,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hsub hsm hav hid hzero
  change (average p hp hs hε t (h+1) u-δ • compactOperator 1 hs hε t (h+1) u:Space) z=(0:Space) z
  rw [hsub,hzero]
  change average p hp hs hε t (h+1) u z-(δ • compactOperator 1 hs hε t (h+1) u:Space) z=0
  rw [hsm]
  change average p hp hs hε t (h+1) u z-δ*compactOperator 1 hs hε t (h+1) u z=0
  rw [hav,hid]
  classical
  by_cases hz : z∈s
  · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz,
      AsymptoticRamifiedFourier.average_of_row a ha hp (δ*(p:ℂ)^h) hrow z.im_pos]
    have hp' : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
    rw [pow_succ]
    field_simp
    ring
  · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]
    ring

#print axioms residual_norm_le
#print axioms average_on_section
#print axioms identity_on_section
#print axioms residual_eq_zero

end AsymptoticRamifiedObservation
