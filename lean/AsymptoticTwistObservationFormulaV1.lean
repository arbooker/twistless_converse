module

public import AsymptoticTwistObservationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticTwistObservation

open MeasureTheory UpperHalfPlane Set Filter
open AsymptoticHyperbolicSlash AsymptoticCompactBranch AsymptoticMobiusFold
open AsymptoticCertificateBranches AsymptoticReconstructionBranch
open AsymptoticWeightedBranches FinitenessAnalyticReconstruction

theorem twist_eq_residues (F : ℂ → ℂ) (q : ℕ) (z : ℂ) :
    twist F q z=∑ a : residues q,F (z+(a.val:ℂ)/q) := by
  unfold twist
  rw [← Finset.sum_attach]
  rfl

theorem translations_on_section (q : ℕ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (u : Space) (hu : u =ᵐ[volume] stripSection ε t m F) :
    translations q hs hε t m u =ᵐ[volume] s.indicator (fun z : ℍ =>
      (cap ε t z:ℂ)*(z.im:ℂ)^m*twist F q z) := by
  rw [translations,_root_.sum_apply]
  apply (Lp.coeFn_fun_finsetSum _ _).trans
  have he : ∀ᵐ z ∂volume,∀ a : residues q,
      compactOperator (translation ((a.val:ℝ)/q)) hs hε t m u z=
        s.indicator (fun w : ℍ => (cap ε t w:ℂ)*phase (translation ((a.val:ℝ)/q)) (2*m) w*
          ((translation ((a.val:ℝ)/q) • w).im:ℂ)^m*F (translation ((a.val:ℝ)/q) • w:ℍ)) z :=
    ae_all_iff.mpr (fun a => compactOperator_on_section (translation ((a.val:ℝ)/q))
      (by rw [translation_det]; norm_num) hs hε t m F hp u hu)
  filter_upwards [he] with z hz
  classical
  by_cases hzs : z∈s
  · rw [Set.indicator_of_mem hzs,twist_eq_residues,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [hz a,Set.indicator_of_mem hzs]
    have hn := normalized_translation ((a.val:ℝ)/q) m F z
    simp only [Complex.ofReal_div,Complex.ofReal_natCast] at hn
    linear_combination (cap ε t z:ℂ)*hn
  · rw [Set.indicator_of_notMem hzs]
    apply Finset.sum_eq_zero
    intro a _
    rw [hz a,Set.indicator_of_notMem hzs]

theorem reflections_on_section (N q : ℕ) (hN : 0<N) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (u : Space) (hu : u =ᵐ[volume] stripSection ε t m F) :
    reflections N q hN hq hs hε t m u =ᵐ[volume] s.indicator (fun z : ℍ =>
      (cap ε t z:ℂ)*(z.im:ℂ)^m/((Real.sqrt (level N q):ℂ)*(z:ℂ))^(2*m)*
        twist F q (-1/((level N q:ℂ)*(z:ℂ)))) := by
  rw [reflections,_root_.sum_apply]
  apply (Lp.coeFn_fun_finsetSum _ _).trans
  have he : ∀ᵐ z ∂volume,∀ a : residues q,
      compactOperator (reflected N q hN hq a.val) hs hε t m u z=
        s.indicator (fun w : ℍ => (cap ε t w:ℂ)*phase (reflected N q hN hq a.val) (2*m) w*
          ((reflected N q hN hq a.val • w).im:ℂ)^m*F (reflected N q hN hq a.val • w:ℍ)) z :=
    ae_all_iff.mpr (fun a => compactOperator_on_section (reflected N q hN hq a.val)
      (by rw [reflected,branch_det]; exact level_pos hN hq) hs hε t m F hp u hu)
  filter_upwards [he] with z hz
  classical
  by_cases hzs : z∈s
  · rw [Set.indicator_of_mem hzs,twist_eq_residues,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [hz a,Set.indicator_of_mem hzs]
    have hn := normalized_reflection N q hN hq a.val m F z
    linear_combination (cap ε t z:ℂ)*hn
  · rw [Set.indicator_of_notMem hzs]
    apply Finset.sum_eq_zero
    intro a _
    rw [hz a,Set.indicator_of_notMem hzs]

/-- The compact observation annihilates exactly the known twist law;
no individual modularity equation is imposed. -/
theorem residual_eq_zero (N q : ℕ) (hN : 0<N) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) (χ : ℂ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (hFE : ∀ z : ℂ,0<z.im → twist F q z=
      χ/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (u : Space) (hu : u =ᵐ[volume] stripSection ε t m F) :
    residual N q hN hq hs hε t m χ u=0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (translations q hs hε t m u) (χ • reflections N q hN hq hs hε t m u),
    Lp.coeFn_smul χ (reflections N q hN hq hs hε t m u),
    translations_on_section q hs hε t m F hp u hu,
    reflections_on_section N q hN hq hs hε t m F hp u hu,Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)]
    with z hsub hsm hl hr hzero
  change (translations q hs hε t m u-χ • reflections N q hN hq hs hε t m u:Space) z=(0:Space) z
  rw [hsub,hzero]
  change translations q hs hε t m u z-(χ • reflections N q hN hq hs hε t m u:Space) z=0
  rw [hsm]
  change translations q hs hε t m u z-χ*reflections N q hN hq hs hε t m u z=0
  rw [hl,hr]
  classical
  by_cases hz : z∈s
  · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz,hFE z z.im_pos]
    simp only [level,Complex.ofReal_natCast]
    ring
  · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]
    ring

#print axioms translations_on_section
#print axioms reflections_on_section
#print axioms residual_eq_zero

end AsymptoticTwistObservation
