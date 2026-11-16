module

public import QuantitativeMaassNormalizerGeneratorsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticCompactBranch
open scoped MatrixGroups ENNReal

namespace QuantitativeMaass

abbrev admissibleGeneratorIndex (N : ℕ) (hN : 0<N) :=
  {g : AsymptoticRationalGroup.Group // admissibleNormalizerGenerator N hN g}

/-- A single lower metric constant works for all modulus-one generator
sectors and all vectors in their Hilbert completions. -/
theorem admissible_generatorCompletion_lower (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    ∃ a : ℝ,0<a ∧ ∀ χ : admissibleGeneratorIndex N hN.1 → ℂ,(∀ i,‖χ i‖=1) →
      ∀ f : normalizerCompletion N (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ,
        a*‖f‖^2≤‖normalizerWeightedEmbedding N hε hv (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ f‖^2 := by
  obtain ⟨c,hc,hbound⟩ := admissible_generator_energy_lower N hN hε hv
  let m : ℕ := Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  have hm : 0<(m:ℝ)+1 := by positivity
  refine ⟨c/((m:ℝ)+1),div_pos hc hm,?_⟩
  intro χ hχ f
  have hr (r : normalizerRepresentatives N (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ) :
      c*‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) r.val‖^2≤
        (m:ℝ)*‖weightedQuotientRepresentative N hε hv r.val‖^2 := by
    have hmem := weightedRepresentative_memLp N hε hv r.val
    have hi := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
    have ht : (∫⁻ z,ENNReal.ofReal (‖(cap ε v z:ℂ)*r.val.val z‖^2)
        ∂quotientMeasure 0)≠∞ :=
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2).ne
    have hb := hbound r.val.val r.val.property.1 r.val.property.2.1 (by
      intro g hg z
      rw [r.property ⟨g,hg⟩ z,norm_mul,hχ,one_mul])
    have hb' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ht) hb
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le,
      square_energy_toReal _ r.val.property.2.2,square_energy_toReal _ hmem] at hb'
    simp only [ENNReal.toReal_natCast] at hb'
    exact hb'
  have hclosed : IsClosed {x : AutomorphicSpace N | c*‖x‖^2≤
      (m:ℝ)*‖weightedQuotientEmbedding N hε hv x‖^2} :=
    isClosed_le (continuous_const.mul (continuous_norm.pow 2))
      (continuous_const.mul ((weightedQuotientEmbedding N hε hv).continuous.norm.pow 2))
  have hb : c*‖f‖^2≤(m:ℝ)*‖normalizerWeightedEmbedding N hε hv (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ f‖^2 := by
    apply closure_minimal (t := {x : AutomorphicSpace N | c*‖x‖^2≤
      (m:ℝ)*‖weightedQuotientEmbedding N hε hv x‖^2}) _ hclosed f.property
    rintro x ⟨r,hr',rfl⟩
    rw [mem_ofPred_eq,weightedQuotientEmbedding_representative]
    exact hr ⟨r,hr'⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hm).mpr
  nlinarith [sq_nonneg ‖normalizerWeightedEmbedding N hε hv (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ f‖]

/-- The weighted range is closed directly from elementary generator
sector equations; no separate cusp cover or spectral hypothesis remains. -/
theorem admissible_generatorEmbedding_closed (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (hχ : ∀ i,‖χ i‖=1) :
    Function.Injective (normalizerWeightedEmbedding N hε hv (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ) ∧
      IsClosed (Set.range (normalizerWeightedEmbedding N hε hv (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ)) := by
  obtain ⟨a,ha,hl⟩ := admissible_generatorCompletion_lower N hN hε hv
  apply lower_energy_injective_closed
    (H := normalizerCompletion N (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ)
    (K := Lp ℂ 2 (quotientMeasure 0))
    (normalizerWeightedEmbedding N hε hv (fun i : admissibleGeneratorIndex N hN.1 => i.val) χ) ha
  intro x
  exact hl χ hχ x

#print axioms admissible_generatorCompletion_lower
#print axioms admissible_generatorEmbedding_closed

end QuantitativeMaass
