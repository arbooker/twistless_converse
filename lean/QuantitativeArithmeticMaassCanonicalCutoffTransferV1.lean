module

public import QuantitativeArithmeticMaassRectangleGradientV1
public import QuantitativeMaassCompactQuotientRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal ContDiff

namespace QuantitativeMaass

/-- Literal local restriction on a closed cylinder rectangle agrees with
the original cylinder class; the right edge is null. -/
theorem quotientRestriction_cylinder_rectangle (a b : ℝ) (ha : 0<a)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    (quotientRestriction 0 (upperRectangle 0 1 a b) (upperRectangle_compact 0 1 a b ha)
      (upperRectangle_measurable 0 1 a b) (cylinderAutomorphic v) : ℍ → ℂ)
      =ᵐ[volume.restrict (upperRectangle 0 1 a b)] v := by
  rw [←cylinderRepresentative_class v]
  have hh := quotientRestriction_representative_ae 0 (upperRectangle 0 1 a b)
    (upperRectangle_compact 0 1 a b ha) (upperRectangle_measurable 0 1 a b)
    (cylinderRepresentative v)
  filter_upwards [hh,upperRectangle_ae_strip a b ha] with z hz hs
  simpa only [cylinderRepresentative,cylinderFold_self hs] using hz

/-- The sharp cross-quotient transfer is exactly the adjoint of the
unweighted compact restriction that occurs after canonical metric/cap
cancellation. This identifies the operators, not just their formal kernels. -/
theorem compactQuotientRestriction_adjoint_rectangle (N : ℕ)
    {δ : ℝ} (hδ : 0<δ) {v : ℕ} (hv : 1≤v) {R : ℝ} (hR : 0≤R)
    (a b : ℝ) (ha : 0<a) (hheight : δ*Real.exp (-R)≤a)
    (c : Lp ℂ 2 (quotientMeasure 0)) :
    (compactQuotientRestriction N hδ hv R (upperRectangle 0 1 a b)
      (upperRectangle_measurable 0 1 a b)).adjoint c =
    (quotientRestriction N (upperRectangle 0 1 a b) (upperRectangle_compact 0 1 a b ha)
      (upperRectangle_measurable 0 1 a b)).adjoint
      (quotientRestriction 0 (upperRectangle 0 1 a b) (upperRectangle_compact 0 1 a b ha)
        (upperRectangle_measurable 0 1 a b) (cylinderAutomorphic c)) := by
  let S := upperRectangle 0 1 a b
  let hS := upperRectangle_measurable 0 1 a b
  let hK := upperRectangle_compact 0 1 a b ha
  let Q := compactQuotientRestriction N hδ hv R S hS
  let A := quotientRestriction N S hK hS
  let d := quotientRestriction 0 S hK hS (cylinderAutomorphic c)
  change Q.adjoint c=A.adjoint d
  apply ext_inner_right ℂ
  intro f
  rw [adjoint_inner_left,adjoint_inner_left]
  have he : (fun f => inner ℂ c (Q f))=(fun f => inner ℂ d (A f)) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (by fun_prop) (by fun_prop)
    funext g
    dsimp only [Function.comp_apply]
    have hQ := compactQuotientRestriction_representative N hδ hv hR S hS
      (fun z hz => hheight.trans hz.2.1) g
    have hA := quotientRestriction_representative_ae N S hK hS g
    have hd := quotientRestriction_cylinder_rectangle a b ha c
    rw [L2.inner_def,L2.inner_def]
    calc
      _ = ∫ z, S.indicator (fun z => inner ℂ (c z) (g.val z)) z ∂quotientMeasure 0 := by
        apply integral_congr_ae
        filter_upwards [hQ] with z hz
        rw [hz]
        by_cases hm : z∈S
        · simp only [Set.indicator_of_mem hm]
        · simp only [Set.indicator_of_notMem hm,inner_zero_right]
      _ = ∫ z in S, inner ℂ (c z) (g.val z) ∂volume := by
        rw [integral_indicator hS]
        change (∫ z, inner ℂ (c z) (g.val z) ∂(quotientMeasure 0).restrict S)=_
        rw [cylinder_rectangle_measure a b ha]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hA,hd] with z hAz hdz
        rw [hAz,hdz]
  exact congrFun he f

/-- Multiplication by the constant one is the identity on local L2. -/
theorem localMultiplier_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : Lp ℂ 2 μ) :
    AsymptoticL2Multiplier.operator (fun _ => (1:ℂ)) aestronglyMeasurable_const
      (C := 1) (Eventually.of_forall (fun _ => by simp)) f=f := by
  apply Lp.ext
  filter_upwards [AsymptoticL2Multiplier.operator_coeFn (fun _ => (1:ℂ))
    aestronglyMeasurable_const (C := 1) (Eventually.of_forall (fun _ => by simp)) f] with z hz
  simpa only [one_mul] using hz

theorem compactQuotientRestriction_eq_boundedTransfer (N : ℕ)
    {δ : ℝ} (hδ : 0<δ) {v : ℕ} (hv : 1≤v) {R : ℝ} (hR : 0≤R)
    (a b : ℝ) (ha : 0<a) (hheight : δ*Real.exp (-R)≤a)
    (c : Lp ℂ 2 (quotientMeasure 0)) :
    (compactQuotientRestriction N hδ hv R (upperRectangle 0 1 a b)
      (upperRectangle_measurable 0 1 a b)).adjoint c =
    boundedCrossQuotientLocalization N 0 (upperRectangle 0 1 a b)
      (upperRectangle_compact 0 1 a b ha) (fun _ => (1:ℂ)) aestronglyMeasurable_const
      (A := 1) (Eventually.of_forall (fun _ => by simp)) (cylinderAutomorphic c) := by
  rw [compactQuotientRestriction_adjoint_rectangle N hδ hv hR a b ha hheight]
  unfold boundedCrossQuotientLocalization
  simp only [comp_apply,localMultiplier_one]


/-- The canonical column differs from its concrete smooth cross-quotient
transfer by at most the actual cylinder energy in the rectangular collar. -/
theorem compactQuotientRestriction_smoothing_energy (N : ℕ)
    {δ : ℝ} (hδ : 0<δ) {v : ℕ} (hv : 1≤v) {R : ℝ} (hR : 0≤R)
    (a b h : ℝ) (ha : 0<a) (hh : 0<h) (hheight : δ*Real.exp (-R)≤a)
    (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ γ ∈ S, γ • z ∈ upperRectangle 0 1 a b) → S.card ≤ m)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (T : ℝ) (hT : 0≤T) (hs : Function.support F ⊆ Iic (Real.cosh T)) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    let Ω := S \ upperRectangle h (1-h) (a+h) (b-h)
    let u := rectangleSmoothSeed 0 1 a b h ha hh
    let hu : ∀ z ∈ S, ‖upperFunction u.toFun z‖≤1 :=
      fun z _ => (rectangleCutoffFunction_bounds 0 1 a b h z).2
    let Q := compactQuotientRestriction N hδ hv R S hS.measurableSet
    (∫⁻ z, ENNReal.ofReal (‖Q.adjoint (cylinderAbelColumn F hF T hT hs z)-
      crossQuotientLocalization N 0 S hS u hu
        (cylinderAutomorphic (cylinderAbelColumn F hF T hT hs z))‖^2) ∂quotientMeasure 0) ≤
      ENNReal.ofReal (m : ℝ)*∫⁻ x in Ω,
        ENNReal.ofReal (‖cylinderAbelColumn F hF T hT hs x‖^2) ∂volume.restrict S := by
  intro S hS Ω u hu Q
  have hΩ : MeasurableSet Ω := hS.measurableSet.diff (upperRectangle_measurable _ _ _ _)
  have hb : ∀ᵐ z ∂volume.restrict S, ‖upperFunction u.toFun z‖≤1 := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    exact hu z hz
  have hchange : ∀ᵐ z ∂volume.restrict S,
      ‖(1:ℂ)-upperFunction u.toFun z‖≤1 ∧ (z∉Ω → (1:ℂ)=upperFunction u.toFun z) := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    have hh' := rectangleSmoothSeed_collar 0 1 a b h ha hh z
    dsimp only at hh'
    change z ∈ upperRectangle 0 1 a b at hz
    simpa only [zero_add,Set.indicator_of_mem hz] using hh'
  have hbound := cylinderAbelColumn_transfer_collar_energy N F hF T hT hs S hS m hm
    (fun _ => (1:ℂ)) (upperFunction u.toFun) aestronglyMeasurable_const
    (upperFunction_continuous u.smooth).aestronglyMeasurable 1 1 1
    (Eventually.of_forall (fun _ => by simp)) hb Ω hΩ hchange
  have heq (z : ℍ) : Q.adjoint (cylinderAbelColumn F hF T hT hs z)=
      boundedCrossQuotientLocalization N 0 S hS (fun _ => (1:ℂ)) aestronglyMeasurable_const
        (A := 1) (Eventually.of_forall (fun _ => by simp))
        (cylinderAutomorphic (cylinderAbelColumn F hF T hT hs z)) :=
    compactQuotientRestriction_eq_boundedTransfer N hδ hv hR a b ha hheight _
  simp_rw [heq]
  simpa only [one_pow,mul_one,boundedCrossQuotientLocalization_smooth N 0 S hS u hu] using hbound

#print axioms compactQuotientRestriction_smoothing_energy
#print axioms compactQuotientRestriction_adjoint_rectangle
#print axioms compactQuotientRestriction_eq_boundedTransfer

end QuantitativeMaass
