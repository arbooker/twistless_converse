module

public import QuantitativeSpectralObservabilityCoverV1
public import QuantitativeSpectralModularCoordinateV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticHyperbolicArea
open QuantitativeSpectralFiniteReduction QuantitativeSpectralTerminalReduction
open scoped MatrixGroups Pointwise

/-- An integral determinant-one action sends a height band into the same
upper cutoff once that cutoff exceeds the reciprocal lower height. This
bound is uniform over all integral matrices, not merely a fixed list. -/
theorem integral_height_upper (g : SL(2,ℤ)) {ε H : ℝ} (hε : 0<ε)
    (hH : ε⁻¹ ≤ H) (z : ℍ) (hlo : ε ≤ z.im) (hhi : z.im ≤ H) :
    (g • z).im ≤ H := by
  by_cases hc : g 1 0=0
  · have hd : g 0 0*g 1 1=1 := by
      have hh := g.property
      rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hh
      exact hh
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hd with ⟨_,hd⟩ | ⟨_,hd⟩
    · rw [ModularGroup.im_smul_eq_div_normSq]
      simpa [ModularGroup.denom_apply,hc,hd] using hhi
    · rw [ModularGroup.im_smul_eq_div_normSq]
      simpa [ModularGroup.denom_apply,hc,hd] using hhi
  · have hc' : (1:ℝ) ≤ |(g 1 0:ℝ)| := by exact_mod_cast Int.one_le_abs hc
    have hi := Complex.abs_im_le_norm (denom g z)
    have he : (denom g z).im=(g 1 0:ℝ)*z.im := by
      simp [ModularGroup.denom_apply,Complex.mul_im]
    rw [he,abs_mul,abs_of_pos z.im_pos] at hi
    have hy : z.im ≤ ‖denom g z‖ := by nlinarith [z.im_pos]
    have hsq : z.im^2 ≤ Complex.normSq (denom g z) := by
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ z.im_pos.le (norm_nonneg _)).mpr hy
    rw [ModularGroup.im_smul_eq_div_normSq]
    calc
      _ ≤ z.im/z.im^2 := div_le_div_of_nonneg_left z.im_pos.le (sq_pos_of_pos z.im_pos) hsq
      _ = z.im⁻¹ := by field_simp
      _ ≤ ε⁻¹ := inv_anti₀ hε hlo
      _ ≤ H := hH

/-- A fixed integral reduction into the open cover is already retained by
the matching compact sampler on the entire truncated terminal band. -/
theorem reduced_mem_wideCompactCover (N : ℕ) (g : SL(2,ℤ))
    {ε H : ℝ} (hε : 0<ε) (hH : ε⁻¹ ≤ H) (z : ℍ)
    (hlo : ε ≤ z.im) (hhi : z.im ≤ H)
    (hz : integralLabel g • z ∈ openCover N) :
    integralLabel g • z ∈ wideCompactCover N H := by
  obtain ⟨q,w,hw,he⟩ := mem_iUnion.mp hz
  have he' : w=integralLabel (q.out*g) • z := by
    rw [map_mul,mul_smul]
    rw [←he,smul_inv_smul]
  have hh : w.im ≤ H := by
    rw [he',integralLabel_action]
    exact integral_height_upper (q.out*g) hε hH z hlo hhi
  exact mem_iUnion.mpr ⟨q,w,⟨hw.1.le,hw.2.1.le,hw.2.2.le,hh⟩,he⟩

/-- One fixed finite word family reduces every truncated terminal band into
the actual compact sampler, with no boundary error on retained inputs. -/
theorem finite_terminal_words_retained (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ W : Finset (List SL(2,ℤ)),
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ H : ℝ, ε⁻¹ ≤ H → ∀ z∈terminal ε, z.im ≤ H →
        ∃ l∈W, integralLabel l.prod • z ∈ wideCompactCover N H := by
  obtain ⟨W,hW,hw⟩ := finite_terminal_words N S hS hε
  refine ⟨W,hW,?_⟩
  intro H hH z hz hhi
  obtain ⟨l,hl,hlz⟩ := hw z hz
  exact ⟨l,hl,reduced_mem_wideCompactCover N l.prod hε hH z hz.2.le hhi hlz⟩

#print axioms integral_height_upper
#print axioms reduced_mem_wideCompactCover
#print axioms finite_terminal_words_retained
end QuantitativeSpectralObservability
