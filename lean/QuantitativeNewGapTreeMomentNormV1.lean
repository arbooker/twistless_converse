module

public import QuantitativeNewGapTreeFaithfulV1
public import QuantitativeScalarSpectralMeasureV1
public import QuantitativeCompactMomentUniquenessV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open InnerProductSpace MeasureTheory AsymptoticNestedQuotients AsymptoticQuotientOperators
open AsymptoticRegularTrace AsymptoticPermutationInvariant QuantitativeScalarSpectralMeasure
open scoped lp InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem spectral_square_integral (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (v : E)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, (f x)^2 ∂realMeasure A hA v)=‖AsymptoticFunctionalCalculus.value f A v‖^2 := by
  rw [integral_realMeasure A hA v (fun x => (f x)^2) (by fun_prop),cfc_pow f 2 A hf.continuousOn hA,pow_two]
  have hs : (cfc (p := IsSelfAdjoint) f A).adjoint=cfc (p := IsSelfAdjoint) f A := cfc_predicate f A
  change (⟪v,cfc (p := IsSelfAdjoint) f A (cfc (p := IsSelfAdjoint) f A v)⟫_ℂ).re= _
  rw [← hs,ContinuousLinearMap.adjoint_inner_right,hs]
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) ((cfc (p := IsSelfAdjoint) f A) v)).symm

/-- Compactly supported scalar measures agree once every actual operator
moment agrees. No cyclicity or faithfulness is used at this stage. -/
theorem spectralMeasure_eq_of_moments {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (u : E)
    (B : F →L[ℂ] F) (hB : IsSelfAdjoint B) (v : F)
    (hm : ∀ n : ℕ, (⟪u,(A^n) u⟫_ℂ).re=(⟪v,(B^n) v⟫_ℂ).re) :
    realMeasure A hA u=realMeasure B hB v := by
  apply QuantitativeCompactMomentUniqueness.real_eq_of_moments _ _
    ((spectrum.isCompact A).union (spectrum.isCompact B))
  · exact measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left)
      (realMeasure_compl_spectrum A hA u)
  · exact measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_right)
      (realMeasure_compl_spectrum B hB v)
  · intro n
    rw [moment,moment,hm n]

theorem norm_le_of_excess_value_zero (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (C : ℝ) (hC : 0 ≤ C)
    (hz : AsymptoticFunctionalCalculus.value (fun x => max 0 (|x|-C)) A=0) : ‖A‖ ≤ C := by
  let f : ℝ → ℝ := fun x => max 0 (|x|-C)
  have hf : Continuous f := continuous_const.max (continuous_abs.sub continuous_const)
  change cfc f A=0 at hz
  rw [← cfc_id ℝ A hA]
  apply norm_cfc_le hC
  intro x hx
  have hh := norm_apply_le_norm_cfc f A hx hf.continuousOn hA
  rw [hz,norm_zero] at hh
  have hf0 : f x=0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  have hx' : |x|-C ≤ 0 := by
    change max 0 (|x|-C)=0 at hf0
    exact (le_max_right 0 (|x|-C)).trans_eq hf0
  exact sub_nonpos.mp hx'

/-- Honest transport of a comparison norm bound to the full quotient
operator: spectral functions are equivariant, and zero rooted Gram mass
forces the whole spectral function to vanish. Root moments alone are not
treated as a full-operator estimate. -/
theorem equivariant_norm_le_of_moments {G : Type*} [Group G] (H : Subgroup G)
    (A : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) (hA : IsSelfAdjoint A)
    (he : Equivariant A) (B : E →L[ℂ] E) (hB : IsSelfAdjoint B) (v : E)
    (hm : ∀ n : ℕ, (⟪delta (classOf H 1),(A^n) (delta (classOf H 1))⟫_ℂ).re=
      (⟪v,(B^n) v⟫_ℂ).re) (C : ℝ) (hC : 0 ≤ C) (hBC : ‖B‖ ≤ C) : ‖A‖ ≤ C := by
  let f : ℝ → ℝ := fun x => max 0 (|x|-C)
  have hf : Continuous f := continuous_const.max (continuous_abs.sub continuous_const)
  have hmeasure := spectralMeasure_eq_of_moments A hA (delta (classOf H 1)) B hB v hm
  have hfB : cfc (p := IsSelfAdjoint) f B=0 := by
    calc
      cfc (p := IsSelfAdjoint) f B=cfc (0 : ℝ → ℝ) B := cfc_congr (by
        intro x hx
        have hn : |x| ≤ C := (quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ B hx)).trans hBC
        exact max_eq_left (sub_nonpos.mpr hn))
      _ = 0 := cfc_zero ℝ B
  have hz : AsymptoticFunctionalCalculus.value f A (delta (classOf H 1))=0 := by
    apply norm_eq_zero.mp
    have hh : ‖AsymptoticFunctionalCalculus.value f A (delta (classOf H 1))‖^2=0 := by
      rw [← spectral_square_integral A hA _ f hf,hmeasure,
        spectral_square_integral B hB v f hf]
      change ‖cfc (p := IsSelfAdjoint) f B v‖^2=0
      rw [hfB]
      simp
    nlinarith [norm_nonneg (AsymptoticFunctionalCalculus.value f A (delta (classOf H 1)))]
  have hzero : AsymptoticFunctionalCalculus.value f A=0 := quotient_root_faithful H _
    (fun a => invariant_cfc _ A (he a) hA f hf) hz
  exact norm_le_of_excess_value_zero A hA C hC hzero

#print axioms spectral_square_integral
#print axioms spectralMeasure_eq_of_moments
#print axioms equivariant_norm_le_of_moments

end QuantitativeNewGap
