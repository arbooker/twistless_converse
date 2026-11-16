module

public import QuantitativeMaassPositiveUnitTestV1
public import QuantitativeMaassPositiveTestSeparationV1
public import QuantitativeMaassTestPowerBoundsV1
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass
open scoped Topology ContDiff Distributions

/-!
Positive-height weak equations. All tests are supported strictly above zero;
no regularity or boundary value at zero is imposed. A distribution with
vanishing second derivative is affine. For continuous height profiles this
identification is pointwise, and subtracting a classical primitive transfers
a weak second-order equation to a classical one.
-/

namespace QuantitativeNinaMaass

def positiveTestMass : PositiveSmoothTest →ₗ[ℝ] ℝ where
  toFun φ := ∫ t, φ t
  map_add' φ ψ := integral_add
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport)
  map_smul' c _ := integral_const_mul c _

def positiveTestMoment : PositiveSmoothTest →ₗ[ℝ] ℝ :=
  positiveTestMass.comp (positiveTestPower 1).toLinearMap

theorem positiveTestMass_deriv (φ : PositiveSmoothTest) :
    positiveTestMass (positiveSmoothTestDeriv φ) = 0 := by
  change (∫ t, positiveSmoothTestDeriv φ t) = 0
  apply integral_eq_zero_of_hasDerivAt_of_integrable
    (f := (φ : ℝ → ℝ))
  · intro t
    rw [positiveSmoothTestDeriv_apply]
    exact (φ.contDiff.differentiable (by simp) t).hasDerivAt
  · exact (positiveSmoothTestDeriv φ).continuous.integrable_of_hasCompactSupport
      (positiveSmoothTestDeriv φ).hasCompactSupport
  · exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

theorem positiveTestMoment_deriv (φ : PositiveSmoothTest) :
    positiveTestMoment (positiveSmoothTestDeriv φ) = -positiveTestMass φ := by
  have h := positiveTestMass_deriv (positiveTestPower 1 φ)
  rw [positiveTestPower_one_deriv, map_add] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The affine conclusion is proved for arbitrary real-linear
functionals on the actual positive test space. -/
theorem positiveDistribution_affine {H : Type*} [AddCommGroup H] [Module ℝ H]
    (T : PositiveSmoothTest →ₗ[ℝ] H)
    (hdd : ∀ φ, T (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)) = 0) :
    ∃ u v : H, ∀ φ, T φ = positiveTestMass φ • u + positiveTestMoment φ • v := by
  let C := T (positiveSmoothTestDeriv positiveUnitTest)
  have hd (φ : PositiveSmoothTest) : T (positiveSmoothTestDeriv φ) = positiveTestMass φ • C :=
    positiveDistribution_eq_constant (T.comp positiveSmoothTestDeriv.toLinearMap) hdd φ
  let Q : PositiveSmoothTest →ₗ[ℝ] H := T + positiveTestMoment.smulRight C
  have hQ (φ : PositiveSmoothTest) : Q (positiveSmoothTestDeriv φ) = 0 := by
    change T (positiveSmoothTestDeriv φ) + positiveTestMoment (positiveSmoothTestDeriv φ) • C = 0
    rw [hd, positiveTestMoment_deriv, neg_smul, add_neg_cancel]
  refine ⟨Q positiveUnitTest, -C, ?_⟩
  intro φ
  have h := positiveDistribution_eq_constant Q hQ φ
  change T φ + positiveTestMoment φ • C = positiveTestMass φ • Q positiveUnitTest at h
  rw [smul_neg]
  exact (eq_sub_of_add_eq h).trans (sub_eq_add_neg _ _)

theorem positiveTest_smul_continuous {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H) (hF : ContinuousOn F (Ioi 0)) (φ : PositiveSmoothTest) :
    Continuous (fun t => φ t • F t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t ∈ tsupport φ
  · exact φ.continuous.continuousAt.smul
      ((hF t (φ.tsupport_subset ht)).continuousAt (isOpen_Ioi.mem_nhds (φ.tsupport_subset ht)))
  · have he : (fun t => φ t • F t) =ᶠ[𝓝 t] (fun _ => (0 : H)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with x hx
      change φ x = 0 at hx
      simp only [hx, zero_smul]
    exact continuousAt_const.congr_of_eventuallyEq he

theorem positiveTest_smul_integrable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H) (hF : ContinuousOn F (Ioi 0)) (φ : PositiveSmoothTest) :
    Integrable (fun t => φ t • F t) :=
  (positiveTest_smul_continuous F hF φ).integrable_of_hasCompactSupport
    φ.hasCompactSupport.smul_right

def positiveHeightPairing {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H) (hF : ContinuousOn F (Ioi 0)) : PositiveSmoothTest →ₗ[ℝ] H where
  toFun φ := ∫ t, φ t • F t
  map_add' φ ψ := by
    change (∫ t, (φ t + ψ t) • F t) = _
    simp_rw [add_smul]
    exact integral_add (positiveTest_smul_integrable F hF φ) (positiveTest_smul_integrable F hF ψ)
  map_smul' c φ := by
    change (∫ t, (c * φ t) • F t) = c • ∫ t, φ t • F t
    simp_rw [mul_smul]
    exact integral_smul c _

theorem continuousOn_eq_zero_of_positiveTests {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H) (hF : ContinuousOn F (Ioi 0))
    (hz : ∀ φ : PositiveSmoothTest, (∫ t, φ t • F t) = 0) :
    ∀ t, 0 < t → F t = 0 := by
  have hae : ∀ᵐ t ∂volume, t ∈ Ioi (0 : ℝ) → F t = 0 :=
    isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hF.locallyIntegrableOn measurableSet_Ioi)
      (fun g hg hc hs => hz ⟨g, hg, hc, hs⟩)
  have hr : F =ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun _ => 0) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr hae
  exact Measure.eqOn_open_of_ae_eq hr isOpen_Ioi hF continuous_const.continuousOn

theorem positiveHeightPairing_affine {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (u v : H) (φ : PositiveSmoothTest) :
    (∫ t, φ t • (u + t • v)) = positiveTestMass φ • u + positiveTestMoment φ • v := by
  have hi : Integrable (φ : ℝ → ℝ) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hm : Integrable (positiveTestPower 1 φ : ℝ → ℝ) :=
    (positiveTestPower 1 φ).continuous.integrable_of_hasCompactSupport
    (positiveTestPower 1 φ).hasCompactSupport
  have he (t : ℝ) : φ t • (u + t • v) = φ t • u + positiveTestPower 1 φ t • v := by
    rw [positiveTestPower_apply, pow_one, smul_add, smul_smul]
  simp_rw [he]
  rw [integral_add (hi.smul_const u) (hm.smul_const v), integral_smul_const, integral_smul_const]
  rfl

/-- Weak second derivative zero forces an actual affine height profile,
even when the profile has no continuous extension to height zero. -/
theorem continuousOn_affine_of_weak_second_zero {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H) (hF : ContinuousOn F (Ioi 0))
    (hdd : ∀ φ : PositiveSmoothTest,
      (∫ t, positiveSmoothTestDeriv (positiveSmoothTestDeriv φ) t • F t) = 0) :
    ∃ u v : H, ∀ t, 0 < t → F t = u + t • v := by
  obtain ⟨u, v, h⟩ := positiveDistribution_affine (positiveHeightPairing F hF) hdd
  refine ⟨u, v, ?_⟩
  have hc : Continuous (fun t : ℝ => u + t • v) := continuous_const.add (continuous_id.smul continuous_const)
  have hz := continuousOn_eq_zero_of_positiveTests (fun t => F t - (u + t • v))
    (hF.sub hc.continuousOn) (by
      intro φ
      simp_rw [smul_sub]
      rw [integral_sub (positiveTest_smul_integrable F hF φ)
        (positiveTest_smul_integrable _ hc.continuousOn φ), positiveHeightPairing_affine]
      exact sub_eq_zero.mpr (h φ))
  exact fun t ht => sub_eq_zero.mp (hz t ht)

/-- Integration by parts only differentiates the profile on the support
of the positive test. Neither endpoint of the half-line is used. -/
theorem positiveHeightPairing_deriv {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F G : ℝ → H) (hF : ContinuousOn F (Ioi 0)) (hG : ContinuousOn G (Ioi 0))
    (hd : ∀ t, 0 < t → HasDerivAt F (G t) t) (φ : PositiveSmoothTest) :
    (∫ t, positiveSmoothTestDeriv φ t • F t) = -(∫ t, φ t • G t) := by
  have h := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ (E := H))
    (u := (φ : ℝ → ℝ)) (u' := (positiveSmoothTestDeriv φ : ℝ → ℝ))
    (v := F) (v' := G)
    (fun t _ => by
      rw [positiveSmoothTestDeriv_apply]
      exact (φ.contDiff.differentiable (by simp) t).hasDerivAt)
    (fun t ht => hd t (φ.tsupport_subset ht))
    (positiveTest_smul_integrable G hG φ)
    (positiveTest_smul_integrable F hF (positiveSmoothTestDeriv φ))
    (positiveTest_smul_integrable F hF φ)
  exact (neg_eq_iff_eq_neg).mp h.symm

def positivePrimitive {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : ℝ → H) (t : ℝ) : H := ∫ s in (1 : ℝ)..t, F s

theorem positivePrimitive_hasDerivAt {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H) (hF : ContinuousOn F (Ioi 0)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (positivePrimitive F) (F t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    apply hF.mono
    intro s hs
    exact (lt_min (by norm_num : (0 : ℝ) < 1) ht).trans_le hs.1
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hF t ht
  · exact (hF t ht).continuousAt (isOpen_Ioi.mem_nhds ht)

theorem positivePrimitive_continuousOn {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F : ℝ → H) (hF : ContinuousOn F (Ioi 0)) :
    ContinuousOn (positivePrimitive F) (Ioi 0) :=
  fun t ht => (positivePrimitive_hasDerivAt F hF t ht).continuousAt.continuousWithinAt

/-- A continuous weak solution of F''=H is a classical solution on all
positive heights. The derivative is constructed from two explicit
primitives and the proved affine-distribution theorem. -/
theorem positive_weak_second_regular {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (F G : ℝ → H) (hF : ContinuousOn F (Ioi 0)) (hG : ContinuousOn G (Ioi 0))
    (hw : ∀ φ : PositiveSmoothTest,
      (∫ t, positiveSmoothTestDeriv (positiveSmoothTestDeriv φ) t • F t) =
        ∫ t, φ t • G t) :
    ∃ F' : ℝ → H, ContinuousOn F' (Ioi 0) ∧
      ∀ t, 0 < t → HasDerivAt F (F' t) t ∧ HasDerivAt F' (G t) t := by
  let P := positivePrimitive G
  let Q := positivePrimitive P
  have hP : ContinuousOn P (Ioi 0) := positivePrimitive_continuousOn G hG
  have hQ : ContinuousOn Q (Ioi 0) := positivePrimitive_continuousOn P hP
  have hPd (t : ℝ) (ht : 0 < t) : HasDerivAt P (G t) t :=
    positivePrimitive_hasDerivAt G hG t ht
  have hQd (t : ℝ) (ht : 0 < t) : HasDerivAt Q (P t) t :=
    positivePrimitive_hasDerivAt P hP t ht
  have hQw (φ : PositiveSmoothTest) :
      (∫ t, positiveSmoothTestDeriv (positiveSmoothTestDeriv φ) t • Q t) =
        ∫ t, φ t • G t := by
    rw [positiveHeightPairing_deriv Q P hQ hP hQd,
      positiveHeightPairing_deriv P G hP hG hPd, neg_neg]
  obtain ⟨u, v, he⟩ := continuousOn_affine_of_weak_second_zero
    (fun t => F t - Q t) (hF.sub hQ) (by
      intro φ
      simp_rw [smul_sub]
      rw [integral_sub (positiveTest_smul_integrable F hF _)
        (positiveTest_smul_integrable Q hQ _), hw, hQw, sub_self])
  refine ⟨fun t => P t + v, hP.add continuous_const.continuousOn, ?_⟩
  intro t ht
  refine ⟨?_, (hPd t ht).add_const v⟩
  have hshape : F =ᶠ[𝓝 t] (fun s => Q s + u + s • v) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    have hh := eq_add_of_sub_eq (he s hs)
    simpa only [add_comm, add_left_comm, add_assoc] using hh
  have hd := ((hQd t ht).add_const u).add ((hasDerivAt_id t).smul_const v)
  simp only [one_smul] at hd
  exact hd.congr_of_eventuallyEq hshape

#print axioms positiveTestMass_deriv
#print axioms positiveTestMoment_deriv
#print axioms positiveDistribution_affine
#print axioms positiveTest_smul_continuous
#print axioms positiveTest_smul_integrable
#print axioms continuousOn_eq_zero_of_positiveTests
#print axioms positiveHeightPairing_affine
#print axioms continuousOn_affine_of_weak_second_zero
#print axioms positiveHeightPairing_deriv
#print axioms positivePrimitive_hasDerivAt
#print axioms positivePrimitive_continuousOn
#print axioms positive_weak_second_regular

end QuantitativeNinaMaass
