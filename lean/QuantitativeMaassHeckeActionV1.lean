module

public import QuantitativeMaassTraceAdjointV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

open MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticClassicalCusp
open AsymptoticCongruenceLabels AsymptoticClassicalDiscriminant AsymptoticAtkinLehner
open scoped BigOperators ENNReal

namespace QuantitativeMaass.HeckeL2

variable (N p : ℕ) [Fact p.Prime] (hN : 0 < N) (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ)*A + (N : ℤ)*B = 1)

def shiftedRepresentative
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AutomorphicL2.representatives (gamma (p*N)) (quotientMeasure (p*N)) :=
  AutomorphicL2.normalizerRepresentative volume AsymptoticRationalGroup.measurePreserving
    (gamma (p*N)) (heckeNormalizerLabel N p (hp p) A B hAB)
    (fun _ ha => heckeNormalizer_conj_mem N p (hp p) A B hAB hN ha)
    (fun _ ha => heckeNormalizer_inv_conj_mem N p (hp p) A B hAB hN ha)
    (density (p*N)) (density_measurable (p*N)) (density_orbit_sum (p*N))
    (liftRepresentative N p hN hpN A B hAB f)

/-- A genuine measurable automorphic representative of the bounded Hecke
operator, obtained by finite coset pushforward. -/
def heckeRepresentative
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) := by
  let := cosetFinite N p hN hpN A B hAB
  let := Fintype.ofFinite (gamma N ⧸ (gamma (p*N)).subgroupOf (gamma N))
  exact (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) •
    AutomorphicL2.traceRepresentative volume AsymptoticRationalGroup.measurePreserving
      (gamma (p*N)) (gamma N) (gamma_le_of_dvd (Nat.dvd_mul_left N p))
      (density N) (density (p*N)) (density_measurable N) (density_measurable (p*N))
      (density_orbit_sum N) (density_orbit_sum (p*N))
      (shiftedRepresentative N p hN hpN A B hAB f)

theorem operator_on_representatives
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (heckeRepresentative N p hN hpN A B hAB f) := by
  let := cosetFinite N p hN hpN A B hAB
  let := Fintype.ofFinite (gamma N ⧸ (gamma (p*N)).subgroupOf (gamma N))
  have hu : normalizer N p hN A B hAB
      (AutomorphicL2.denseEmbedding _ _ (liftRepresentative N p hN hpN A B hAB f)) =
      AutomorphicL2.denseEmbedding _ _ (shiftedRepresentative N p hN hpN A B hAB f) :=
    AutomorphicL2.normalizerIsometry_apply volume AsymptoticRationalGroup.measurePreserving
      (gamma (p*N)) (heckeNormalizerLabel N p (hp p) A B hAB)
      (fun _ ha => heckeNormalizer_conj_mem N p (hp p) A B hAB hN ha)
      (fun _ ha => heckeNormalizer_inv_conj_mem N p (hp p) A B hAB hN ha)
      (density (p*N)) (density_measurable (p*N)) (density_orbit_sum (p*N))
      (liftRepresentative N p hN hpN A B hAB f)
  have ht := AutomorphicL2.coverOperator_adjoint_apply volume AsymptoticRationalGroup.measurePreserving
    (gamma (p*N)) (gamma N) (gamma_le_of_dvd (Nat.dvd_mul_left N p))
    (density N) (density (p*N)) (density_measurable N) (density_measurable (p*N))
    (density_orbit_sum N) (density_orbit_sum (p*N))
    (shiftedRepresentative N p hN hpN A B hAB f)
  change (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) •
    (inclusion N p hN hpN A B hAB).adjoint
      (normalizer N p hN A B hAB (inclusion N p hN hpN A B hAB
        (AutomorphicL2.denseEmbedding _ _ f))) = _
  rw [inclusion_on_representatives, hu]
  exact (congrArg (fun v => (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) • v) ht).trans
    (map_smul (AutomorphicL2.denseEmbedding _ _) _ _).symm

/-- Exact matrix cancellation producing the p upper-triangular branches. -/
theorem normalizer_traceSL (a : ℤ) :
    heckeNormalizerReal N p (hp p) A B hAB *
      SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB a) =
    triangularGL 1 a p (by norm_num) (by exact_mod_cast hp p) := by
  rw [heckeNormalizerReal, mul_assoc, dilation_traceSL]
  simp only [map_inv, inv_mul_cancel_left]

theorem normalizer_traceSL_action (a : ℤ) (z : ℍ) :
    heckeNormalizerLabel N p (hp p) A B hAB •
      (integralLabel (traceSL N p A B hAB a) • z) =
    triangularGL 1 a p (by norm_num) (by exact_mod_cast hp p) • z := by
  rw [← heckeNormalizer_action, integralLabel_action]
  change heckeNormalizerReal N p (hp p) A B hAB •
    (SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB a) • z) = _
  rw [← mul_smul, normalizer_traceSL]

/-- The representative is exactly the familiar normalized p+1 Hecke sum. -/
theorem heckeRepresentative_apply
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) (z : ℍ) :
    (heckeRepresentative N p hN hpN A B hAB f).val z =
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
        (f.val (dilationLabel p (hp p) • z) +
          ∑ a : Fin p, f.val (triangularGL 1 a.val p (by norm_num) (by exact_mod_cast hp p) • z)) := by
  let := cosetFinite N p hN hpN A B hAB
  let := Fintype.ofFinite (gamma N ⧸ (gamma (p*N)).subgroupOf (gamma N))
  change (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
    (∑ q : gamma N ⧸ (gamma (p*N)).subgroupOf (gamma N),
      CosetTrace.value _ (shiftedRepresentative N p hN hpN A B hAB f).val _ q z) = _
  congr 1
  rw [← Equiv.sum_comp (traceCosetEquiv N p hN hpN A B hAB), Fintype.sum_option]
  have hv (a : Option (Fin p)) :
      CosetTrace.value _ (shiftedRepresentative N p hN hpN A B hAB f).val
        (fun h x => (shiftedRepresentative N p hN hpN A B hAB f).property.2.1
          ⟨h.val.val,h.property⟩ x)
        (traceCosetEquiv N p hN hpN A B hAB a) z =
      f.val (heckeNormalizerLabel N p (hp p) A B hAB •
        ((AsymptoticAtkinLehner.traceRepresentative N p A B hAB a).val⁻¹ • z)) := rfl
  simp only [hv]
  rw [show (AsymptoticAtkinLehner.traceRepresentative N p A B hAB none).val⁻¹ • z = z by
    simp [AsymptoticAtkinLehner.traceRepresentative]]
  rw [normalizer_function_eq_dilation]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change f.val (heckeNormalizerLabel N p (hp p) A B hAB •
    (((integralLabel (traceSL N p A B hAB a.val))⁻¹)⁻¹ • z)) = _
  rw [inv_inv, normalizer_traceSL_action]
  simp only [Int.cast_natCast]

#print axioms operator_on_representatives
#print axioms heckeRepresentative_apply

end QuantitativeMaass.HeckeL2
