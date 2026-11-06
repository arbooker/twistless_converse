module

public import AsymptoticCompactBranchFormulaV1
public import AsymptoticCertificateFEV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticTwistObservation

open MeasureTheory UpperHalfPlane Set Filter ContinuousLinearMap
open AsymptoticHyperbolicSlash AsymptoticCompactBranch AsymptoticMobiusFold
open AsymptoticCertificateBranches AsymptoticReconstructionBranch

noncomputable def level (N q : ℕ) : ℝ := Nat.lcm N (q^2)

theorem level_pos {N q : ℕ} (hN : 0<N) (hq : 0<q) : 0<level N q := by
  unfold level
  exact_mod_cast Nat.lcm_pos hN (pow_pos hq 2)

noncomputable def reflected (N q : ℕ) (hN : 0<N) (hq : 0<q) (a : ℕ) : GL (Fin 2) ℝ :=
  branch (level N q) 0 ((a:ℝ)/q) (level_pos hN hq).ne'

noncomputable def branchBound (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  (data g hs hε t).folds.card*(data g hs hε t).bound

theorem branchBound_nonneg (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : 0≤branchBound g hs hε t :=
  mul_nonneg (Nat.cast_nonneg _) (data g hs hε t).bound_nonneg

noncomputable def translations (q : ℕ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) : Space →L[ℂ] Space :=
  ∑ a : residues q,compactOperator (translation ((a.val:ℝ)/q)) hs hε t m

noncomputable def reflections (N q : ℕ) (hN : 0<N) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) : Space →L[ℂ] Space :=
  ∑ a : residues q,compactOperator (reflected N q hN hq a.val) hs hε t m

noncomputable def translationBound (q : ℕ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  ∑ a : residues q,branchBound (translation ((a.val:ℝ)/q)) hs hε t

noncomputable def reflectionBound (N q : ℕ) (hN : 0<N) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  ∑ a : residues q,branchBound (reflected N q hN hq a.val) hs hε t

/-- Compact residual of the known Ramanujan functional equation. Every
translation and reflected branch retains its weight-dependent phase. -/
noncomputable def residual (N q : ℕ) (hN : 0<N) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (χ : ℂ) : Space →L[ℂ] Space :=
  translations q hs hε t m-χ • reflections N q hN hq hs hε t m

theorem residual_norm_le (N q : ℕ) (hN : 0<N) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (χ : ℂ) :
    ‖residual N q hN hq hs hε t m χ‖≤
      translationBound q hs hε t+‖χ‖*reflectionBound N q hN hq hs hε t := by
  have hl : ‖translations q hs hε t m‖≤translationBound q hs hε t := by
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun a _ => compactOperator_norm_le (translation ((a.val:ℝ)/q)) hs hε t m)
  have hr : ‖reflections N q hN hq hs hε t m‖≤reflectionBound N q hN hq hs hε t := by
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun a _ => compactOperator_norm_le (reflected N q hN hq a.val) hs hε t m)
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  exact add_le_add hl (mul_le_mul_of_nonneg_left hr (norm_nonneg _))

theorem normalized_translation (r : ℝ) (m : ℕ) (F : ℂ → ℂ) (z : ℍ) :
    phase (translation r) (2*m) z*((translation r • z).im:ℂ)^m*F (translation r • z:ℍ)=
      (z.im:ℂ)^m*F ((z:ℂ)+(r:ℂ)) := by
  have hi : (translation r • z).im=z.im := by
    simpa using congrArg Complex.im (translation_action r z)
  rw [translation_phase,one_mul,hi,translation_action]

theorem normalized_reflection (N q : ℕ) (hN : 0<N) (hq : 0<q) (a m : ℕ)
    (F : ℂ → ℂ) (z : ℍ) :
    phase (reflected N q hN hq a) (2*m) z*((reflected N q hN hq a • z).im:ℂ)^m*
      F (reflected N q hN hq a • z:ℍ)=
      (z.im:ℂ)^m/((Real.sqrt (level N q):ℂ)*(z:ℂ))^(2*m)*
        F (-1/((level N q:ℂ)*(z:ℂ))+(a:ℂ)/q) := by
  have hn := normalized_branch (level_pos hN hq) 0 ((a:ℝ)/q) m (fun w : ℍ => F w) z
  simpa only [reflected,Complex.ofReal_zero,add_zero,branch_action (level_pos hN hq),
    Complex.ofReal_div,Complex.ofReal_natCast] using hn

#print axioms residual_norm_le
#print axioms normalized_translation
#print axioms normalized_reflection

end AsymptoticTwistObservation
