module

public import QuantitativeNinaMaassFourierSeparationV1
public import QuantitativeNinaMaassEigenRepresentativesV1
public import QuantitativeNinaMaassOldTraceV1
public import QuantitativeNinaMaassSmallPeriodsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticClassicalPetersson
open scoped Topology MatrixGroups

/-!
Literal positive horocycle Fourier integrals on actual continuous cuspidal
Maass representatives. Their injectivity is proved from actual quotient
reflection, unit translations, vanishing cusp constants and Fourier
completeness. These coefficients still depend on height: extracting the
normalized height-independent Bessel amplitudes is a remaining step.
-/

namespace QuantitativeNinaMaass

theorem horocyclePoint_continuous (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => horocyclePoint x y hy) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ))
  have he : (fun x : ℝ => (⟨x, y⟩ : ℂ)) =
      (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) := by
    funext x
    apply Complex.ext <;> simp
  rw [he]
  exact Complex.continuous_ofReal.add continuous_const

theorem horocyclePoint_reflection (x y : ℝ) (hy : 0 < y) :
    J • horocyclePoint x y hy = horocyclePoint (-x) y hy := by
  apply UpperHalfPlane.ext
  rw [coe_J_smul]
  apply Complex.ext <;> simp [horocyclePoint]

theorem representative_unit_periodic (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (y : ℝ) (hy : 0 < y) :
    Function.Periodic (fun x => f.val (horocyclePoint x y hy)) 1 := by
  intro x
  have hi := f.property.2.1
    ⟨integralLabel (upperSL 1), by rw [upper_label]; exact translation_mem N 1⟩
    (horocyclePoint x y hy)
  rw [horocyclePoint_translate] at hi
  simpa only [Int.cast_one] using hi

/-- Physical Hilbert-space reflection has the literal pointwise parity
on a continuous representative; equality is not merely almost everywhere. -/
theorem representative_pointwise_parity (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (s : ℂ)
    (hs : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f) (x y : ℝ) (hy : 0 < y) :
    f.val (horocyclePoint (-x) y hy) = s * f.val (horocyclePoint x y hy) := by
  have he : reflectionRepresentative N f = s • f := by
    apply continuous_representative_unique N (reflectionRepresentative N f) (s • f)
    · exact hf.comp (continuous_const_smul J)
    · exact continuous_const.mul hf
    · rw [← reflectionIsometry_apply, map_smul]
      exact hs
  have hz := congrArg (fun g : AutomorphicL2.representatives (gamma N) (quotientMeasure N) =>
    g.val (horocyclePoint x y hy)) he
  change f.val (J • horocyclePoint x y hy) = s * f.val (horocyclePoint x y hy) at hz
  rwa [horocyclePoint_reflection] at hz

/-- The actual cusp condition supplies the missing zero Fourier integral
at infinity. The common cusp period N is reduced to the genuine period 1. -/
theorem representative_unit_mean_zero (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hc : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (y : ℝ) (hy : 0 < y) :
    unitLineFourierCoeff (fun x => f.val (horocyclePoint x y hy)) 0 = 0 := by
  have hz := localCuspidalSpace_continuous_constant_zero N hN
    (AutomorphicL2.denseEmbedding _ _ f) hc f.val hf f.property.2.1
    f.property.2.2.coeFn_toLp 1 y hy
  simp only [cuspConstant, zeroFourier, cuspProfile, dite_eq_left hy, map_one, one_smul] at hz
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd := periodic_mean_integer_dilate (fun x => f.val (horocyclePoint x y hy))
    (hf.comp (horocyclePoint_continuous y hy)) (representative_unit_periodic N f y hy)
    (N : ℤ) hNZ
  simp only [Int.cast_natCast] at hd
  rw [unitLineFourierCoeff_zero]
  exact hd.symm.trans hz

/-- The positive, height-dependent Fourier integrals of the actual
automorphic function. The index n represents the positive mode n+1. -/
def positiveHorocycleCoefficients {N : ℕ}
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ℕ → {y : ℝ // 0 < y} → ℂ :=
  fun n y => unitLineFourierCoeff (fun x => f.val (horocyclePoint x y.val y.property)) (n + 1)

theorem physical_positive_coefficients_separate (N : ℕ) (hN : 0 < N)
    (f g : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hg : Continuous g.val)
    (hcf : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (hcg : AutomorphicL2.denseEmbedding _ _ g ∈ localCuspidalSpace N hN)
    (s : ℂ)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f)
    (hsg : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ g) =
      s • AutomorphicL2.denseEmbedding _ _ g)
    (he : positiveHorocycleCoefficients f = positiveHorocycleCoefficients g) : f = g := by
  apply Subtype.ext
  funext z
  have hline := continuous_periodic_eq_of_nonnegative_fourier
    (fun x => f.val (horocyclePoint x z.im z.im_pos))
    (fun x => g.val (horocyclePoint x z.im z.im_pos))
    (hf.comp (horocyclePoint_continuous z.im z.im_pos))
    (hg.comp (horocyclePoint_continuous z.im z.im_pos))
    (representative_unit_periodic N f z.im z.im_pos)
    (representative_unit_periodic N g z.im z.im_pos) s
    (fun x => representative_pointwise_parity N f hf s hsf x z.im z.im_pos)
    (fun x => representative_pointwise_parity N g hg s hsg x z.im z.im_pos) (by
      intro n
      cases n with
      | zero => simp only [Nat.cast_zero]; rw [representative_unit_mean_zero N hN f hf hcf,
          representative_unit_mean_zero N hN g hg hcg]
      | succ n => exact congrFun (congrFun he n) ⟨z.im, z.im_pos⟩)
  exact congrFun hline z.re

/-- This type retains the original quotient representatives and the
proved physical cusp and parity conditions; no separation property is a field. -/
def ContinuousCuspParityRepresentatives (N : ℕ) (hN : 0 < N) (s : ℂ) :=
  {f : AutomorphicL2.representatives (gamma N) (quotientMeasure N) //
    Continuous f.val ∧ AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN ∧
      reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
        s • AutomorphicL2.denseEmbedding _ _ f}

theorem positiveHorocycleCoefficients_injective (N : ℕ) (hN : 0 < N) (s : ℂ) :
    Function.Injective (fun f : ContinuousCuspParityRepresentatives N hN s =>
      positiveHorocycleCoefficients f.val) := by
  intro f g he
  apply Subtype.ext
  exact physical_positive_coefficients_separate N hN f.val g.val f.property.1 g.property.1
    f.property.2.1 g.property.2.1 s f.property.2.2 g.property.2.2 he

#print axioms horocyclePoint_continuous
#print axioms horocyclePoint_reflection
#print axioms representative_unit_periodic
#print axioms representative_pointwise_parity
#print axioms representative_unit_mean_zero
#print axioms physical_positive_coefficients_separate
#print axioms positiveHorocycleCoefficients_injective

end QuantitativeNinaMaass
