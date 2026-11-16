module

public import QuantitativeMaassRawColumnBesselV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace ENNReal

namespace QuantitativeMaass

/-- Bessel's inequality permits subtraction of every column component
orthogonal to the selected spectral family. -/
theorem centered_column_bessel {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : ι → H) (hv : Orthonormal ℂ v)
    (c m : H) (hm : ∀ i,inner ℂ m (v i)=0) (s : Finset ι) :
    (∑ i∈s,‖inner ℂ c (v i)‖^2)≤‖c-m‖^2 := by
  have hh := hv.sum_inner_products_le (s:=s) (c-m)
  have he (i : ι) : ‖inner ℂ (v i) (c-m)‖=‖inner ℂ c (v i)‖ := by
    rw [norm_inner_symm (v i) (c-m),inner_sub_left,hm,sub_zero]
  simpa only [he] using hh

/-- Exact energy reduction when the removed column is its orthogonal
mean component. -/
theorem centered_column_norm_square {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (c m : H) (hm : (inner ℂ c m).re=‖m‖^2) :
    ‖c-m‖^2=‖c‖^2-‖m‖^2 := by
  rw [norm_sub_sq (𝕜:=ℂ)]
  change ‖c‖^2-2*(inner ℂ c m).re+‖m‖^2=‖c‖^2-‖m‖^2
  rw [hm]
  ring

/-- Actual raw compact Bessel inequality after subtracting any column field
orthogonal to the selected cusp family. A later cusp calculation must supply
the mean field and bound its actual centered norm. -/
theorem continuous_column_raw_centered_bessel {ι : Type*} (N : ℕ)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (c : ℍ → AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun x => inner ℂ (c x) v))
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v) (K : Set ℍ) (hK : IsCompact K)
    (m : ℍ → AutomorphicSpace N) (hm : ∀ x∈K,∀ i,inner ℂ (m x) (v i)=0) :
    (∑' i,ENNReal.ofReal (‖quotientRestriction N K hK hK.measurableSet (A (v i))‖^2))≤
      ∫⁻ x in K,ENNReal.ofReal (‖c x-m x‖^2) := by
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
  have hmeas (i : ι) : Measurable (fun x => ENNReal.ofReal (‖inner ℂ (c x) (v i)‖^2)) :=
    ((hc.inner continuous_const).norm.pow 2).measurable.ennreal_ofReal
  rw [←lintegral_finsetSum (μ:=volume.restrict K) s (fun i _ => hmeas i)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  change (∑ i∈s,ENNReal.ofReal (‖inner ℂ (c x) (v i)‖^2))≤ENNReal.ofReal (‖c x-m x‖^2)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (centered_column_bessel v hv (c x) (m x) (hm x hx) s)

#print axioms centered_column_bessel
#print axioms centered_column_norm_square
#print axioms continuous_column_raw_centered_bessel

end QuantitativeMaass
