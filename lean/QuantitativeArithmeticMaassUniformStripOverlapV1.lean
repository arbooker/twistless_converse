module

public import QuantitativeArithmeticMaassRectangleTransferNormV1
public import QuantitativeMaassParabolicLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane Matrix ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels QuantitativeSpectralObservability
open scoped Topology MatrixGroups
namespace QuantitativeMaass

/-- Two points above height one in the same integral orbit differ by a
translation. Their heights need not be equal in the hypothesis. -/
theorem integral_two_high_points_lowerleft_zero (A : SL(2,ℤ)) (z : ℍ)
    (hz : 1<z.im) (hAz : 1<(A•z:ℍ).im) : A 1 0=0 := by
  by_contra hn
  have hc : (1:ℝ)≤(A 1 0:ℝ)^2 := by
    have hh : (1:ℤ)≤|A 1 0| := by have := abs_pos.mpr hn; omega
    have hh' : (1:ℝ)≤|(A 1 0:ℝ)| := by exact_mod_cast hh
    nlinarith [sq_abs (A 1 0:ℝ)]
  have hdpos := normSq_denom_pos (A : GL (Fin 2) ℝ) z.im_ne_zero
  rw [ModularGroup.im_smul_eq_div_normSq] at hAz
  have hd := (lt_div_iff₀ hdpos).mp hAz
  have hs := c_mul_im_sq_le_normSq_denom (A : GL (Fin 2) ℝ) z
  change ((A 1 0:ℝ)*z.im)^2≤_ at hs
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg z.im)
  rw [mul_pow] at hs
  nlinarith

/-- A width-one strip above height one has at most three projective
integral translates through any point, including boundary overlaps. -/
theorem high_strip_overlap_bound (N : ℕ) (z : ℍ) (S : Finset (gamma N))
    (hS : ∀ g∈S,0≤(g•z:ℍ).re ∧ (g•z:ℍ).re≤1 ∧ 1<(g•z:ℍ).im) :
    S.card≤3 := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨g₀,hg₀⟩ := hne
    let rel : gamma N→gamma N := fun g => g*g₀⁻¹
    let n : gamma N→ℤ := fun g => representative (rel g) 0 0*representative (rel g) 0 1
    have ha (g : gamma N) : representative (rel g)•(g₀•z)=g•z := by
      rw [←integralLabel_action,representative_label]
      change (g*g₀⁻¹)•(g₀•z)=g•z
      simp only [mul_smul,inv_smul_smul]
    have hc (g : gamma N) (hg : g∈S) : representative (rel g) 1 0=0 :=
      integral_two_high_points_lowerleft_zero _ _ (hS g₀ hg₀).2.2
        (by rw [ha]; exact (hS g hg).2.2)
    have hn (g : gamma N) (hg : g∈S) :
        integralLabel (upperSL (n g))=(rel g).val := by
      rw [←integral_upper_triangular_label _ (hc g hg),representative_label]
    have hshift (g : gamma N) (hg : g∈S) : (g•z:ℍ).re=(g₀•z:ℍ).re+n g := by
      rw [←ha g,←integralLabel_action,integral_upper_triangular_label _ (hc g hg)]
      simp only [n,upper_label,translation_re]
    let J : Finset ℤ := Finset.Icc (-1) 1
    let enc : S→J := fun g => ⟨n g.val,by
      have hx := hshift g.val g.property
      have hb := hS g.val g.property
      have hb₀ := hS g₀ hg₀
      have hl : (-1:ℝ)≤(n g.val:ℝ) := by linarith
      have hu : (n g.val:ℝ)≤1 := by linarith
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩⟩
    have hi : Function.Injective enc := by
      intro g h he
      have he' : n g.val=n h.val := congrArg Subtype.val he
      have hh : rel g.val=rel h.val := by
        apply Subtype.ext
        rw [←hn g.val g.property,←hn h.val h.property,he']
      apply Subtype.ext
      exact mul_right_cancel hh
    have hb := Fintype.card_le_of_injective enc hi
    norm_num [Fintype.card_coe,J,Int.card_Icc] at hb ⊢
    exact hb
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.zero_le]

/-- Uniform overlap of the complete terminal strip, independent of any
upper height cutoff and uniform in the congruence level. -/
theorem terminal_strip_overlap_bound (N : ℕ) (a : ℝ) (ha : 0<a)
    (z : ℍ) (S : Finset (gamma N))
    (hS : ∀ g∈S,0≤(g•z:ℍ).re ∧ (g•z:ℍ).re≤1 ∧ a≤(g•z:ℍ).im) :
    S.card≤(2*⌈3/a⌉₊+1)^4+3 := by
  classical
  let L := S.filter (fun g => (g•z:ℍ).im≤1)
  let H := S.filter (fun g => ¬(g•z:ℍ).im≤1)
  have hL : L.card≤(2*⌈3/a⌉₊+1)^4 := by
    have hb := rectangle_overlap_bound N a 1 ha z L (by
      intro g hg
      obtain ⟨hg,hy⟩ := Finset.mem_filter.mp hg
      exact ⟨⟨(hS g hg).1,(hS g hg).2.1⟩,⟨(hS g hg).2.2,hy⟩⟩)
    norm_num only [one_pow,show (2:ℝ)+1=3 by norm_num] at hb
    exact hb
  have hH : H.card≤3 := high_strip_overlap_bound N z H (by
    intro g hg
    obtain ⟨hg,hy⟩ := Finset.mem_filter.mp hg
    exact ⟨(hS g hg).1,(hS g hg).2.1,lt_of_not_ge hy⟩)
  have he : L.card+H.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

/-- The compact restriction norm is bounded independently of the upper
height of a rectangle. -/
theorem rectangle_restriction_uniform_norm (N : ℕ) (a b : ℝ) (ha : 0<a) :
    ‖quotientRestriction N (upperRectangle 0 1 a b)
      (upperRectangle_compact 0 1 a b ha)
      (upperRectangle_compact 0 1 a b ha).measurableSet‖≤
        Real.sqrt (((2*⌈3/a⌉₊+1)^4+3:ℕ):ℝ) := by
  apply quotientRestriction_norm_le_of_overlap
  intro z S hS
  apply terminal_strip_overlap_bound N a ha z S
  intro g hg
  have hz := hS g hg
  exact ⟨hz.1.1,hz.1.2,hz.2.1⟩

/-- Uniform norm bound for the actual cross-quotient transfer with any
bounded multiplier, independent of the rectangle's upper height. -/
theorem rectangle_transfer_uniform_norm (N : ℕ) (a b : ℝ) (ha : 0<a)
    (v : ℍ→ℂ) (hv : AEStronglyMeasurable v (volume.restrict (upperRectangle 0 1 a b)))
    (hbound : ∀ᵐ x ∂volume.restrict (upperRectangle 0 1 a b),‖v x‖≤1) :
    ‖boundedCrossQuotientLocalization N 0 (upperRectangle 0 1 a b)
      (upperRectangle_compact 0 1 a b ha) v hv hbound‖≤
        (((2*⌈3/a⌉₊+1)^4+3:ℕ):ℝ) := by
  let Ω := upperRectangle 0 1 a b
  let hΩ := upperRectangle_compact 0 1 a b ha
  let m := (2*⌈3/a⌉₊+1)^4+3
  let RN := quotientRestriction N Ω hΩ hΩ.measurableSet
  let R0 := quotientRestriction 0 Ω hΩ hΩ.measurableSet
  let V := AsymptoticL2Multiplier.operator v hv hbound
  have hn : ‖RN.adjoint‖≤Real.sqrt (m:ℝ) := by
    rw [adjoint.norm_map]
    exact rectangle_restriction_uniform_norm N a b ha
  have h0 : ‖R0‖≤Real.sqrt (m:ℝ) := rectangle_restriction_uniform_norm 0 a b ha
  have hvn : ‖V‖≤1 := AsymptoticL2Multiplier.operator_norm_le v hv (by norm_num) hbound
  change ‖RN.adjoint.comp (V.comp R0)‖≤(m:ℝ)
  calc
    _ ≤ ‖RN.adjoint‖*‖V.comp R0‖ := opNorm_comp_le _ _
    _ ≤ Real.sqrt (m:ℝ)*(1*Real.sqrt (m:ℝ)) := by
      apply mul_le_mul hn _ (norm_nonneg (V.comp R0)) (Real.sqrt_nonneg _)
      exact (opNorm_comp_le V R0).trans (mul_le_mul hvn h0 (norm_nonneg R0) (by norm_num))
    _ = _ := by rw [one_mul,←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]

#print axioms rectangle_transfer_uniform_norm
#print axioms integral_two_high_points_lowerleft_zero
#print axioms high_strip_overlap_bound
#print axioms terminal_strip_overlap_bound
#print axioms rectangle_restriction_uniform_norm
end QuantitativeMaass
