module

public import QuantitativeArithmeticMaassHighCuspOverlapV1
public import QuantitativeMaassCuspRectangleV1
public import QuantitativeMaassEnergyLocalizationV1
public import QuantitativeMaassFormLocalizationDefectV1
public import QuantitativeMaassQuotientRestrictionBoundV1

/-! Consolidated chapter: QuantitativeArithmeticMaassHighCuspEnergy. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticMaassHighCuspEnergyDensityV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal MatrixGroups

namespace QuantitativeArithmeticMaassHighCuspEnergy
open QuantitativeMaass QuantitativeArithmeticMaassHighCuspOverlap

/-! UNVERIFIED draft. Uniform cusp overlap is used with the actual normalized
quotient density; no energy comparison is assumed. -/

/-- Uniform count on the image of a high compact rectangle in any integral
cusp chart. The bound is independent of both height endpoints. -/
theorem cusp_rectangle_orbit_count (N W : ℕ) (s : SL(2,ℤ))
    (l Y H : ℝ) (hY : 2 ≤ Y) (z : ℍ) :
    (∑' g : gamma N,
      (cuspAction s '' upperRectangle l (l+W) Y H).indicator
        (fun _ => (1:ℝ≥0∞)) (g.val • z)) ≤ (W+1:ℕ) := by
  classical
  let K := upperRectangle l (l+W) Y H
  let L := cuspAction s '' K
  have hYpos : 0 < Y := by linarith
  have hK : IsCompact K := upperRectangle_compact l (l+W) Y H hYpos
  have hL : IsCompact L := hK.image (cuspAction_continuous s)
  let hfinite := compact_orbit_point_finite (G := gamma N) L hL z
  let S := hfinite.toFinset
  have hmember (g : gamma N) (hg : g ∈ S) : g.val • z ∈ L :=
    hfinite.mem_toFinset.mp hg
  have hout (g : gamma N) (hg : g ∉ S) :
      L.indicator (fun _ => (1:ℝ≥0∞)) (g.val • z) = 0 := by
    apply Set.indicator_of_notMem
    exact fun h => hg (hfinite.mem_toFinset.mpr h)
  change (∑' g : gamma N, L.indicator (fun _ => (1:ℝ≥0∞)) (g.val • z)) ≤ _
  rw [tsum_eq_sum hout]
  have he : (∑ g ∈ S, L.indicator (fun _ => (1:ℝ≥0∞)) (g.val • z)) = S.card := by
    calc
      _ = ∑ _g ∈ S, (1:ℝ≥0∞) := Finset.sum_congr rfl
        (fun g hg => Set.indicator_of_mem (hmember g hg) _)
      _ = _ := by simp
  rw [he]
  have hc : S.card ≤ W+1 := by
    apply gamma_cusp_high_strip_card_bound N W S s z l
    intro g hg
    obtain ⟨w, hw, hew⟩ := hmember g hg
    have hp : s⁻¹ • (g.val • z) = w := by
      rw [← hew]
      change s⁻¹ • (s • w) = w
      exact inv_smul_smul s w
    rw [hp]
    exact ⟨hY.trans hw.2.1, hw.1.1, hw.1.2⟩
  exact_mod_cast hc

/-- A nonnegative invariant density on any high cusp rectangle is bounded
by W+1 times its actual quotient integral. This includes energy densities
and does not require that either integral be finite. -/
theorem cusp_rectangle_image_lintegral_le (N W : ℕ) (s : SL(2,ℤ))
    (l Y H : ℝ) (hY : 2 ≤ Y) (F : ℍ → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, F (g.val • z) = F z) :
    (∫⁻ z in cuspAction s '' upperRectangle l (l+W) Y H, F z) ≤
      (W+1:ℕ) * ∫⁻ z, F z ∂quotientMeasure N := by
  classical
  let L := cuspAction s '' upperRectangle l (l+W) Y H
  have hYpos : 0 < Y := by linarith
  have hL : MeasurableSet L :=
    ((upperRectangle_compact l (l+W) Y H hYpos).image (cuspAction_continuous s)).measurableSet
  have hun := lintegral_poincare_unfold volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (L.indicator F) (hF.indicator hL)
  have he (z : ℍ) : (∑' g : gamma N, L.indicator F (g.val • z)) =
      (∑' g : gamma N, L.indicator (fun _ => (1:ℝ≥0∞)) (g.val • z)) * F z := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro g
    by_cases hg : g.val • z ∈ L
    · simp only [Set.indicator_of_mem hg, one_mul, hinv g z]
    · simp only [Set.indicator_of_notMem hg, zero_mul]
  change (∫⁻ z in L, F z) ≤ (W+1:ℕ) * ∫⁻ z, F z ∂volume.withDensity (density N)
  rw [← lintegral_indicator hL F, ← hun]
  change (∫⁻ z, (∑' g : gamma N, L.indicator F (g.val • z))
    ∂volume.withDensity (density N)) ≤ _
  simp_rw [he]
  calc
    _ ≤ ∫⁻ z, (W+1:ℕ) * F z ∂volume.withDensity (density N) := by
      apply lintegral_mono
      intro z
      dsimp only
      gcongr
      exact cusp_rectangle_orbit_count N W s l Y H hY z
    _ = _ := lintegral_const_mul _ hF

/-- Literal cusp pullback version, with hyperbolic measure on the rectangle.
The constant is uniform as its upper height tends to infinity. -/
theorem cusp_rectangle_lintegral_le (N W : ℕ) (s : SL(2,ℤ))
    (l Y H : ℝ) (hY : 2 ≤ Y) (F : ℍ → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, F (g.val • z) = F z) :
    (∫⁻ z in upperRectangle l (l+W) Y H, F (cuspAction s z)) ≤
      (W+1:ℕ) * ∫⁻ z, F z ∂quotientMeasure N := by
  have hYpos : 0 < Y := by linarith
  rw [(cuspAction_restricted_preserving s _
    (upperRectangle_compact l (l+W) Y H hYpos)).lintegral_comp hF]
  exact cusp_rectangle_image_lintegral_le N W s l Y H hY F hF hinv

#print axioms cusp_rectangle_orbit_count
#print axioms cusp_rectangle_image_lintegral_le
#print axioms cusp_rectangle_lintegral_le
end QuantitativeArithmeticMaassHighCuspEnergy
end
end

/-! ## QuantitativeArithmeticMaassHighCuspEnergySeedV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal MatrixGroups Topology ContDiff

namespace QuantitativeArithmeticMaassHighCuspEnergy
open QuantitativeMaass MaassDifferential

/-! UNVERIFIED draft. Specialization to genuine smooth Poincare vectors and
their existing quotientClosedEnergy; no local/global energy bound is an input. -/

/-- The actual energy of a smooth invariant function is invariant. -/
theorem upperEnergy_self_invariant (N : ℕ) (u : Point → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0 < Z.2})
    (hinv : ∀ g : gamma N, ∀ z : ℍ, upperFunction u (g.val • z) = upperFunction u z)
    (g : gamma N) (z : ℍ) : upperEnergy u u (g.val • z) = upperEnergy u u z := by
  have hi : u ∘ integralCuspChart (representative g) =ᶠ[𝓝 (z.re,z.im)] u := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos] with W hW
    change u (integralCuspChart (representative g) W) = u W
    rw [← congruence_pullback_cartesian N u g W hW]
    change upperFunction u (g.val • cartesianLift W) = u W
    rw [hinv, upperFunction_cartesianLift hW]
  have he := hyperbolicEnergy_integralCuspChart (representative g) hu hu (Z := (z.re,z.im)) z.im_pos
  rw [hyperbolicEnergy_congr_left hi, hyperbolicEnergy_congr_right hi] at he
  have hp := congruence_pullback_cartesian N (hyperbolicEnergy u u) g
    (z.re,z.im) z.im_pos
  rw [cartesianLift_positive _ z.im_pos] at hp
  change upperEnergy u u (g.val • z) = _ at hp
  exact hp.trans he.symm

/-- The literal chart energy is the pullback of the hyperbolic energy. -/
theorem upperEnergy_self_cuspAction (s : SL(2,ℤ)) (u : Point → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0 < Z.2}) (z : ℍ) :
    upperEnergy (u ∘ integralCuspChart s) (u ∘ integralCuspChart s) z =
      upperEnergy u u (cuspAction s z) := by
  have he := hyperbolicEnergy_integralCuspChart s hu hu (Z := (z.re,z.im)) z.im_pos
  have hp := upperFunction_integral_action (hyperbolicEnergy u u) s
    (z.re,z.im) z.im_pos
  rw [cartesianLift_positive _ z.im_pos] at hp
  exact he.trans hp.symm

/-- Exact nonnegative integral representation of a smooth Poincare vector's
closed form energy, with integrability supplied by the proved Green identity. -/
theorem poincare_energy_lintegral (N : ℕ) (u : SmoothUpperSeed) :
    (∫⁻ z, ENNReal.ofReal
      (upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re ∂quotientMeasure N) =
      ENNReal.ofReal (quotientClosedEnergy N (poincareEnergySeed N u)
        (poincareEnergySeed N u)).re := by
  rw [poincareClosedEnergy_re_integral]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
    (poincare_green_energy N u.smooth u.smooth u.compact u.compact).1.re
  exact Filter.Eventually.of_forall (fun z => hyperbolicEnergy_self_nonneg _ (z.re,z.im))

/-- Uniform actual cusp-chart energy bound on every finite high band.
The multiplier W+1 does not depend on the upper height. -/
theorem poincare_cusp_energy_lintegral_le (N W : ℕ) (s : SL(2,ℤ))
    (l Y H : ℝ) (hY : 2 ≤ Y) (u : SmoothUpperSeed) :
    (∫⁻ z in upperRectangle l (l+W) Y H, ENNReal.ofReal
      (upperEnergy (congruencePoincareCartesian N u.toFun ∘ integralCuspChart s)
        (congruencePoincareCartesian N u.toFun ∘ integralCuspChart s) z).re) ≤
      (W+1:ℕ) * ENNReal.ofReal
        (quotientClosedEnergy N (poincareEnergySeed N u) (poincareEnergySeed N u)).re := by
  let P := congruencePoincareCartesian N u.toFun
  have hP : ContDiffOn ℝ ∞ P {Z | 0 < Z.2} :=
    congruencePoincareCartesian_smooth N u.smooth u.compact
  have hi : ∀ g : gamma N, ∀ z : ℍ, upperFunction P (g.val • z) = upperFunction P z := by
    intro g z
    simp only [P, congruencePoincareCartesian_represents]
    change poincareSum (G := gamma N) (upperFunction u.toFun) (g • z) = _
    exact poincareSum_invariant _ g z
  have hF : Measurable (fun z => ENNReal.ofReal (upperEnergy P P z).re) :=
    (Complex.continuous_re.comp (upperEnergy_continuous hP hP)).measurable.ennreal_ofReal
  have hFi : ∀ g : gamma N, ∀ z : ℍ,
      ENNReal.ofReal (upperEnergy P P (g.val • z)).re =
        ENNReal.ofReal (upperEnergy P P z).re := by
    intro g z
    rw [upperEnergy_self_invariant N P hP hi g z]
  have hb := cusp_rectangle_lintegral_le N W s l Y H hY
    (fun z => ENNReal.ofReal (upperEnergy P P z).re) hF hFi
  simp_rw [← upperEnergy_self_cuspAction s P hP] at hb
  simpa only [P, poincare_energy_lintegral] using hb

/-- The horizontal part alone is bounded by the same actual closed energy.
Hyperbolic measure cancels the displayed y^2 in the eventual Fubini step. -/
theorem poincare_cusp_horizontal_lintegral_le (N W : ℕ) (s : SL(2,ℤ))
    (l Y H : ℝ) (hY : 2 ≤ Y) (u : SmoothUpperSeed) :
    (∫⁻ z in upperRectangle l (l+W) Y H, ENNReal.ofReal
      (z.im^2 * ‖X (congruencePoincareCartesian N u.toFun ∘ integralCuspChart s)
        (z.re,z.im)‖^2)) ≤
      (W+1:ℕ) * ENNReal.ofReal
        (quotientClosedEnergy N (poincareEnergySeed N u) (poincareEnergySeed N u)).re := by
  apply le_trans _ (poincare_cusp_energy_lintegral_le N W s l Y H hY u)
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  change z.im^2 * _ ≤ (hyperbolicEnergy _ _ (z.re,z.im)).re
  rw [hyperbolicEnergy_self_eq]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg z.im)

#print axioms upperEnergy_self_invariant
#print axioms upperEnergy_self_cuspAction
#print axioms poincare_energy_lintegral
#print axioms poincare_cusp_energy_lintegral_le
#print axioms poincare_cusp_horizontal_lintegral_le
end QuantitativeArithmeticMaassHighCuspEnergy
end
end
