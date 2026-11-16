module

public import QuantitativeMaassTimeFilteredTraceV1
public import QuantitativeArithmeticMaassCuspLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace ENNReal SchwartzMap

namespace QuantitativeMaass

/-- A continuous invariant representative identifies the raw compact restriction,
not only the quotient-measure equivalence class. -/
theorem continuous_invariant_raw_restriction (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (v : AutomorphicSpace N) (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ γ : gamma N,∀ z,f (γ•z)=f z)
    (he : v.val=ᵐ[quotientMeasure N]f) :
    (quotientRestriction N K hK hK.measurableSet v : ℍ → ℂ)=ᵐ[volume.restrict K]f := by
  have hm : f∈AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
    ⟨hf.measurable,hinv,(memLp_congr_ae he).mp (Lp.memLp v.val)⟩
  let w : AutomorphicL2.representatives (gamma N) (quotientMeasure N) := ⟨f,hm⟩
  have hw : AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) w=v := by
    apply Subtype.ext
    apply Lp.ext
    exact hm.2.2.coeFn_toLp.trans he.symm
  rw [←hw]
  exact quotientRestriction_representative_ae N K hK hK.measurableSet w

/-- Raw compact Bessel inequality for a continuous invariant Hilbert kernel.
The evaluation formula is transported through actual representatives. -/
theorem continuous_column_raw_bessel {ι : Type*} (N : ℕ)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (c : ℍ → AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun x => inner ℂ (c x) v))
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v) (K : Set ℍ) (hK : IsCompact K) :
    (∑' i,ENNReal.ofReal (‖quotientRestriction N K hK hK.measurableSet (A (v i))‖^2))≤
      ∫⁻ x in K,ENNReal.ofReal (‖c x‖^2) := by
  classical
  have he (i : ι) : ENNReal.ofReal
      (‖quotientRestriction N K hK hK.measurableSet (A (v i))‖^2)=
      ∫⁻ x in K,ENNReal.ofReal (‖inner ℂ (c x) (v i)‖^2) := by
    rw [QuantitativeArithmeticMaassCuspBand.lp_norm_square_lintegral]
    apply lintegral_congr_ae
    filter_upwards [continuous_invariant_raw_restriction N K hK (A (v i)) _
      (hc.inner continuous_const) (fun γ z => by rw [hinv]) (hrep (v i))] with x hx
    rw [hx]
  simp_rw [he]
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  have hm (i : ι) : Measurable (fun x => ENNReal.ofReal (‖inner ℂ (c x) (v i)‖^2)) :=
    ((hc.inner continuous_const).norm.pow 2).measurable.ennreal_ofReal
  rw [←lintegral_finsetSum (μ:=volume.restrict K) s (fun i _ => hm i)]
  apply lintegral_mono
  intro x
  change (∑ i∈s,ENNReal.ofReal (‖inner ℂ (c x) (v i)‖^2))≤ENNReal.ofReal (‖c x‖^2)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [norm_inner_symm] using (hv.sum_inner_products_le (s:=s) (c x))

#print axioms continuous_invariant_raw_restriction
#print axioms continuous_column_raw_bessel

end QuantitativeMaass
