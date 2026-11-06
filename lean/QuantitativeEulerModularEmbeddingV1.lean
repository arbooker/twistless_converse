module

public import QuantitativeMaassAutomorphicL2V1
public import AsymptoticClassicalPeterssonMeasureV1
public import AsymptoticHyperbolicSlashV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerModularEmbedding

open MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticClassicalPetersson
open QuantitativeMaass.AutomorphicL2
open scoped ENNReal

/-- Multiplication by an actual amplitude transfers its squared modulus
from the measure to the function, including infinite norm values. -/
theorem eLpNorm_mul_density {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a f : α → ℂ) (ha : Measurable a) (hf : Measurable f) :
    eLpNorm (fun x => a x * f x) 2 μ =
      eLpNorm f 2 (μ.withDensity (fun x => ENNReal.ofReal (‖a x‖^2))) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun x => a x * f x) (μ := μ) (by norm_num : (2:ℝ≥0∞)≠0)
      (by norm_num : (2:ℝ≥0∞)≠∞) (ha.mul hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞)≠0)
      (by norm_num : (2:ℝ≥0∞)≠∞) hf.aestronglyMeasurable,
    lintegral_withDensity_eq_lintegral_mul μ (ha.norm.pow_const 2).ennreal_ofReal (by fun_prop)]
  congr 1
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply,ENNReal.toReal_ofNat,enorm_mul,ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]
  simp only [ENNReal.rpow_two,mul_pow]

variable (N : ℕ) {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : 1 ≤ t)

include hε ht in
theorem eLpNorm_amplitude (f : ℍ → ℂ) (hf : Measurable f)
    (hinv : ∀ g : gamma N, ∀ z, f (g.val • z)=f z) :
    eLpNorm (fun z => amplitude N ε t z * f z) 2 volume =
      eLpNorm f 2 (quotientMeasure N) := by
  rw [eLpNorm_mul_density volume _ f (amplitude_measurable N ε t) hf]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞)≠0)
      (by norm_num : (2:ℝ≥0∞)≠∞) hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞)≠0)
      (by norm_num : (2:ℝ≥0∞)≠∞) hf.aestronglyMeasurable]
  congr 1
  exact AsymptoticOrbitDensity.lintegral_invariant_eq volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (fun z => ENNReal.ofReal (‖amplitude N ε t z‖^2)) (density N)
    ((amplitude_measurable N ε t).norm.pow_const 2).ennreal_ofReal
    (density_measurable N) (AsymptoticCongruenceQuotient.amplitude_ofReal_tsum N hε ht)
    (density_orbit_sum N) (fun z => ‖f z‖ₑ ^ (2:ℝ≥0∞).toReal)
    (by fun_prop) (fun g z => by change ‖f (g.val • z)‖ₑ ^ _ = _; rw [hinv])

include hε ht in
theorem amplitude_memLp (f : representatives (gamma N) (quotientMeasure N)) :
    MemLp (fun z => amplitude N ε t z * f.val z) 2 volume := by
  change eLpNorm (fun z => amplitude N ε t z * f.val z) 2 volume < ∞
  rw [eLpNorm_amplitude N hε ht f.val f.property.1 f.property.2.1]
  exact f.property.2.2

def representativeEmbedding : representatives (gamma N) (quotientMeasure N)
    →ₗ[ℂ] AsymptoticHyperbolicSlash.Space where
  toFun f := (amplitude_memLp N hε ht f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(amplitude_memLp N hε ht (f+g)).coeFn_toLp,
      (amplitude_memLp N hε ht f).coeFn_toLp,(amplitude_memLp N hε ht g).coeFn_toLp,
      Lp.coeFn_add ((amplitude_memLp N hε ht f).toLp _) ((amplitude_memLp N hε ht g).toLp _)]
      with z hfg hf hg ha
    rw [hfg,ha]
    change amplitude N ε t z * (f.val z + g.val z) = _ + _
    rw [hf,hg,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(amplitude_memLp N hε ht (c • f)).coeFn_toLp,
      (amplitude_memLp N hε ht f).coeFn_toLp,
      Lp.coeFn_smul c ((amplitude_memLp N hε ht f).toLp _)] with z hcf hf hs
    simp only [RingHom.id_apply]
    rw [hcf,hs]
    change amplitude N ε t z * (c * f.val z) = c * _
    rw [hf]
    ring

theorem representativeEmbedding_norm (f : representatives (gamma N) (quotientMeasure N)) :
    ‖representativeEmbedding N hε ht f‖ = ‖denseEmbedding (gamma N) (quotientMeasure N) f‖ := by
  change ‖(amplitude_memLp N hε ht f).toLp _‖ = _
  rw [Lp.norm_toLp,embedding_norm]
  congr 1
  exact eLpNorm_amplitude N hε ht f.val f.property.1 f.property.2.1

/-- The genuine full-modular isometry J0, obtained from the orbit-normalized
amplitude. Its range is not asserted to be the weighted new/sign target. -/
def isometry : space (gamma N) (quotientMeasure N) →ₗᵢ[ℂ] AsymptoticHyperbolicSlash.Space :=
  (representativeEmbedding N hε ht).extendOfIsometry
    (denseEmbedding_dense (gamma N) (quotientMeasure N))
    (representativeEmbedding_norm N hε ht)

theorem isometry_apply (f : representatives (gamma N) (quotientMeasure N)) :
    isometry N hε ht (denseEmbedding (gamma N) (quotientMeasure N) f) =
      representativeEmbedding N hε ht f :=
  LinearMap.extendOfIsometry_eq _ _ _ f

theorem isometry_coeFn (f : representatives (gamma N) (quotientMeasure N)) :
    isometry N hε ht (denseEmbedding (gamma N) (quotientMeasure N) f) =ᵐ[volume]
      (fun z => amplitude N ε t z * f.val z) := by
  rw [isometry_apply]
  exact (amplitude_memLp N hε ht f).coeFn_toLp

#print axioms eLpNorm_amplitude
#print axioms representativeEmbedding_norm
#print axioms isometry_coeFn

end QuantitativeEulerModularEmbedding
