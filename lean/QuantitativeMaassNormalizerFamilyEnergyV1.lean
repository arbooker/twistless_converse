module

public import QuantitativeMaassNormalizerActionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceWeight
open AsymptoticCompactBranch
open scoped ENNReal

namespace QuantitativeMaass

/-- Moving the weight by a normalizer is exactly inverse pullback of the
function in the actual weighted cylinder norm. -/
theorem normalizer_weighted_pullback_energy (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (g : (quotientNormalizerGroup N))
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    (∫⁻ z,ENNReal.ofReal (weight N ε v (g.val • z))*ENNReal.ofReal (‖f.val z‖^2)
      ∂quotientMeasure N)=
      ∫⁻ z,ENNReal.ofReal (‖(cap ε v z:ℂ)*(quotientNormalizerRepresentative N g⁻¹ f).val z‖^2)
        ∂quotientMeasure 0 := by
  let r := quotientNormalizerRepresentative N g⁻¹ f
  have hr (z : ℍ) : r.val (g.val • z)=f.val z := by
    change f.val (g.val⁻¹ • (g.val • z))=f.val z
    rw [inv_smul_smul]
  have h := OrbitIntegral.lintegral_normalizer volume AsymptoticRationalGroup.measurePreserving
    (gamma N) g.val (fun _ ha => normalizer_conj_mem N g ha)
    (fun _ ha => normalizer_inv_conj_mem N g ha)
    (density N) (density_measurable N) (density_orbit_sum N)
    (fun z => ENNReal.ofReal (weight N ε v z)*ENNReal.ofReal (‖r.val z‖^2))
    ((weight_measurable N ε v).ennreal_ofReal.mul (r.property.1.norm.pow_const 2).ennreal_ofReal)
    (by intro a z; rw [weight_invariant,r.property.2.1])
  rw [weighted_quotient_energy N hε hv r.val r.property.1 r.property.2.1]
  simpa only [hr,quotientMeasure] using h

/-- A finite normalizer cover controls every automorphic representative
by the sum of its transformed cylinder energies. No eigenvector equation
or continuity assumption is used here. -/
theorem normalizer_family_representative_lower {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → (quotientNormalizerGroup N))
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    heightWeightFloor ε v Y*‖AutomorphicL2.denseEmbedding _ _ f‖^2≤
      ∑ i,‖weightedQuotientRepresentative N hε hv
        (quotientNormalizerRepresentative N (g i)⁻¹ f)‖^2 := by
  classical
  let E (i : ι) := ∫⁻ z,ENNReal.ofReal (‖(cap ε v z:ℂ)*
    (quotientNormalizerRepresentative N (g i)⁻¹ f).val z‖^2) ∂quotientMeasure 0
  have hfin (i : ι) : E i≠∞ := by
    have hm := weightedRepresentative_memLp N hε hv (quotientNormalizerRepresentative N (g i)⁻¹ f)
    have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    exact ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2).ne
  have hb : ENNReal.ofReal (heightWeightFloor ε v Y)*
      (∫⁻ z,ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N)≤∑ i,E i := by
    rw [←lintegral_const_mul _ ((f.property.1.norm.pow_const 2).ennreal_ofReal)]
    calc
      _≤∫⁻ z,(∑ i,ENNReal.ofReal (weight N ε v ((g i).val • z)))*
          ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N := by
        apply lintegral_mono
        intro z
        exact mul_le_mul (normalizer_weight_sum_lower N hε hY hv (fun i => (g i).val) hcover z)
          le_rfl zero_le zero_le
      _=∑ i,∫⁻ z,ENNReal.ofReal (weight N ε v ((g i).val • z))*
          ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N := by
        simp_rw [Finset.sum_mul]
        apply lintegral_finsetSum
        intro i _
        exact (((weight_measurable N ε v).comp
          (AsymptoticRationalGroup.measurePreserving (g i).val).measurable).ennreal_ofReal.mul
            (f.property.1.norm.pow_const 2).ennreal_ofReal)
      _=_ := by simp only [normalizer_weighted_pullback_energy N hε hv,E]
  have hs : (∑ i,E i)≠∞ := ENNReal.sum_ne_top.mpr (fun i _ => hfin i)
  have hr := ENNReal.toReal_mono hs hb
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (heightWeightFloor_pos hε hY v).le,
    square_energy_toReal _ f.property.2.2,ENNReal.toReal_sum (fun i _ => hfin i)] at hr
  have he (i : ι) : (E i).toReal=
      ‖weightedQuotientRepresentative N hε hv (quotientNormalizerRepresentative N (g i)⁻¹ f)‖^2 :=
    square_energy_toReal _ (weightedRepresentative_memLp N hε hv
      (quotientNormalizerRepresentative N (g i)⁻¹ f))
  simp_rw [he] at hr
  exact hr

/-- The finite-family estimate holds on the entire Hilbert completion. -/
theorem normalizer_family_completed_lower {ι : Type*} [Fintype ι]
    (N : ℕ) {ε Y : ℝ} (hε : 0<ε) (hY : 0<Y) {v : ℕ} (hv : 1≤v)
    (g : ι → (quotientNormalizerGroup N))
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)
    (x : AutomorphicSpace N) :
    heightWeightFloor ε v Y*‖x‖^2≤
      ∑ i,‖weightedQuotientEmbedding N hε hv (quotientNormalizerPullback N (g i)⁻¹ x)‖^2 := by
  refine (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).induction_on x
    (isClosed_le (continuous_const.mul (continuous_norm.pow 2))
      (continuous_finsetSum _ (fun i _ =>
        ((weightedQuotientEmbedding N hε hv).continuous.comp
          (quotientNormalizerPullback N (g i)⁻¹).continuous).norm.pow 2))) ?_
  intro f
  simp only [quotientNormalizerPullback_representative,weightedQuotientEmbedding_representative]
  exact normalizer_family_representative_lower N hε hY hv g hcover f

#print axioms normalizer_weighted_pullback_energy
#print axioms normalizer_family_representative_lower
#print axioms normalizer_family_completed_lower

end QuantitativeMaass
