module

public import QuantitativeMaassHeckeSymmetryV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticClassicalCusp
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace QuantitativeMaass

namespace AutomorphicL2
variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]

theorem denseEmbedding_inner (H : Subgroup G) (ν : Measure α)
    (f g : representatives H ν) :
    ⟪denseEmbedding H ν f, denseEmbedding H ν g⟫_ℂ =
      ∫ x, conj (f.val x) * g.val x ∂ν := by
  change ⟪embedding H ν f, embedding H ν g⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.property.2.2.coeFn_toLp,g.property.2.2.coeFn_toLp] with x hf hg
  change ⟪(f.property.2.2.toLp f.val) x,(g.property.2.2.toLp g.val) x⟫_ℂ = _
  rw [hf,hg]
  simp only [RCLike.inner_apply, mul_comm]
end AutomorphicL2

namespace HeckeL2
variable (N p : ℕ) [Fact p.Prime] (hN : 0 < N) (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ)*A + (N : ℤ)*B = 1)

/-- The small-level representative is literally the same function. -/
def liftRepresentative : AutomorphicL2.representatives (gamma N) (quotientMeasure N) →ₗ[ℂ]
    AutomorphicL2.representatives (gamma (p*N)) (quotientMeasure (p*N)) := by
  let := cosetFinite N p hN hpN A B hAB
  exact AutomorphicL2.coverRepresentative volume AsymptoticRationalGroup.measurePreserving
    (gamma (p*N)) (gamma N) (gamma_le_of_dvd (Nat.dvd_mul_left N p))
    (density N) (density (p*N)) (density_measurable N) (density_measurable (p*N))
    (density_orbit_sum N) (density_orbit_sum (p*N))

theorem inclusion_on_representatives
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    inclusion N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (liftRepresentative N p hN hpN A B hAB f) := by
  let := cosetFinite N p hN hpN A B hAB
  exact AutomorphicL2.coverOperator_apply volume AsymptoticRationalGroup.measurePreserving
    (gamma (p*N)) (gamma N) (gamma_le_of_dvd (Nat.dvd_mul_left N p))
    (density N) (density (p*N)) (density_measurable N) (density_measurable (p*N))
    (density_orbit_sum N) (density_orbit_sum (p*N)) f

/-- An exact quotient-integral formula for the bounded Hecke correspondence
on actual measurable automorphic L² functions. This is the weak
correspondence identity needed before identifying a periodized kernel. -/
theorem operator_pairing
    (f k : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ⟪operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f),
      AutomorphicL2.denseEmbedding _ _ k⟫_ℂ =
    (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
      ∫ z : ℍ, conj (f.val (heckeNormalizerLabel N p (hp p) A B hAB • z)) * k.val z
        ∂quotientMeasure (p*N) := by
  rw [operator, smul_apply, inner_smul_left]
  simp only [Complex.conj_ofReal]
  congr 1
  change ⟪(inclusion N p hN hpN A B hAB).adjoint
    (normalizer N p hN A B hAB (inclusion N p hN hpN A B hAB
      (AutomorphicL2.denseEmbedding _ _ f))), AutomorphicL2.denseEmbedding _ _ k⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_left, inclusion_on_representatives,
    inclusion_on_representatives]
  have hu := AutomorphicL2.normalizerIsometry_apply volume
    AsymptoticRationalGroup.measurePreserving (gamma (p*N))
    (heckeNormalizerLabel N p (hp p) A B hAB)
    (fun _ ha => heckeNormalizer_conj_mem N p (hp p) A B hAB hN ha)
    (fun _ ha => heckeNormalizer_inv_conj_mem N p (hp p) A B hAB hN ha)
    (density (p*N)) (density_measurable (p*N)) (density_orbit_sum (p*N))
    (liftRepresentative N p hN hpN A B hAB f)
  have hh := congrArg (fun v : AutomorphicSpace (p*N) =>
    ⟪v, AutomorphicL2.denseEmbedding _ _ (liftRepresentative N p hN hpN A B hAB k)⟫_ℂ) hu
  apply hh.trans
  exact AutomorphicL2.denseEmbedding_inner _ _ _ _

/-- Automorphy removes the integral factor in the rational normalizer. -/
theorem normalizer_function_eq_dilation
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) (z : ℍ) :
    f.val (heckeNormalizerLabel N p (hp p) A B hAB • z) =
      f.val (AsymptoticCongruenceLabels.dilationLabel p (hp p) • z) := by
  have hm : AsymptoticCongruenceLabels.integralLabel (heckeSL N p A B hAB) ∈ gamma N :=
    ⟨heckeSL N p A B hAB, heckeSL_mem N p A B hAB, rfl⟩
  have hi := f.property.2.1
    ⟨(AsymptoticCongruenceLabels.integralLabel (heckeSL N p A B hAB))⁻¹,
      (gamma N).inv_mem hm⟩ (AsymptoticCongruenceLabels.dilationLabel p (hp p) • z)
  simpa only [heckeNormalizerLabel, mul_smul, map_inv] using hi

/-- The bounded correspondence has the standard dilation/cover weak formula;
in particular its action is independent of the Bezout normalizer choice. -/
theorem operator_pairing_dilation
    (f k : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ⟪operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f),
      AutomorphicL2.denseEmbedding _ _ k⟫_ℂ =
    (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
      ∫ z : ℍ, conj (f.val (AsymptoticCongruenceLabels.dilationLabel p (hp p) • z)) * k.val z
        ∂quotientMeasure (p*N) := by
  rw [operator_pairing]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z =>
    congrArg (fun w : ℂ => conj w * k.val z)
      (normalizer_function_eq_dilation N p A B hAB f z))

#print axioms operator_pairing_dilation
#print axioms AutomorphicL2.denseEmbedding_inner
#print axioms inclusion_on_representatives
#print axioms operator_pairing

end HeckeL2
end QuantitativeMaass
