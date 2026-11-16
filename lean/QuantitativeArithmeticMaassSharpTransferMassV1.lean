module

public import QuantitativeArithmeticMaassSharpSmoothTraceV1
public import QuantitativeArithmeticMaassScheduledSharpMassV1
public import QuantitativeArithmeticMaassScheduledFluxBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap ContDiff
namespace QuantitativeMaass

/-- A bounded local multiplier transfers at most the target orbit overlap
 times its local cylinder energy. The upper height is not a norm loss. -/
theorem transferred_column_energy (N : ℕ)
    (F : ℝ→ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (lo hi : ℝ) (hlo : 0<lo)
    (hheight : ∀ x∈K,lo≤x.im ∧ x.im≤hi) (m : ℕ)
    (hm : ∀ z : ℍ,∀ S : Finset (gamma N),(∀ γ∈S,γ•z∈K) → S.card≤m)
    (v : ℍ→ℂ) (hv : AEStronglyMeasurable v (volume.restrict K))
    (hbound : ∀ᵐ x ∂volume.restrict K,‖v x‖≤1) :
    (∫ z,‖boundedCrossQuotientLocalization N 0 K hK v hv hbound
      (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))‖^2 ∂quotientMeasure 0)≤
      (m:ℝ)*(∫ z in K,‖cylinderAbelColumn F hF R hR hs z‖^2) := by
  have hzero : ∀ᵐ x ∂volume.restrict K,‖(0:ℂ)‖≤(0:ℝ) := Eventually.of_forall (fun _ => by simp)
  have hz (u : AutomorphicSpace 0) :
      boundedCrossQuotientLocalization N 0 K hK (fun _ => (0:ℂ)) aestronglyMeasurable_const hzero u=0 := by
    have hm0 : AsymptoticL2Multiplier.operator (fun _ : ℍ => (0:ℂ))
        aestronglyMeasurable_const hzero (quotientRestriction 0 K hK hK.measurableSet u)=0 := by
      apply Lp.ext
      filter_upwards [AsymptoticL2Multiplier.operator_coeFn (fun _ : ℍ => (0:ℂ))
        aestronglyMeasurable_const hzero (quotientRestriction 0 K hK hK.measurableSet u),Lp.coeFn_zero ℂ 2 (volume.restrict K)] with x hx hz
      simp only [zero_mul] at hx
      rw [hx,hz]
      rfl
    change (quotientRestriction N K hK hK.measurableSet).adjoint
      (AsymptoticL2Multiplier.operator (fun _ => (0:ℂ)) aestronglyMeasurable_const hzero
        (quotientRestriction 0 K hK hK.measurableSet u))=0
    rw [hm0,map_zero]
  have hb := transferred_column_collar_real_energy N F hF R hR hs K hK lo hi hlo hheight m hm
    v (fun _ => (0:ℂ)) hv aestronglyMeasurable_const 1 0 1 hbound hzero Set.univ MeasurableSet.univ
    (by filter_upwards [hbound] with x hx; simpa using hx)
  simpa only [hz,sub_zero,one_pow,mul_one,Measure.restrict_univ] using hb


#print axioms transferred_column_energy
end QuantitativeMaass
namespace QuantitativeMaass.Scheduled

/-- Genuine smooth-transfer column mass is O(t epsilon), uniformly in
both the congruence level and the shrinking collar width. -/
theorem cutoffTransfer_sharp_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ B : ℝ,0<B ∧ ∀ ε : ℝ→ℝ,
      (∀ᶠ t in atTop,0<ε t ∧ ε t≤1) →
      Tendsto (fun t => ε t*slowScale t) atTop atTop →
      ∀ᶠ t in atTop,∀ (N : ℕ) (D : ℝ),
      (∫ z,‖cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z))‖^2
        ∂quotientMeasure 0)≤B*(t*ε t) := by
  obtain ⟨B,hB,hbound⟩ := sharp_rectangle_source_mass K hc he hK hm δ (1/2) hδ
  let m := (2*⌈3/δ⌉₊+1)^4+3
  have hmpos : 0<(m:ℝ) := by dsimp [m]; positivity
  refine ⟨(m:ℝ)*B,mul_pos hmpos hB,?_⟩
  intro ε hε hp
  filter_upwards [hbound ε hε hp] with t ht
  intro N D
  let S := cutoffRectangle δ t
  let hS := upperRectangle_compact 0 1 δ (Real.exp (Strong.strongScale t/2)) hδ
  let u := cutoffSeed δ D t hδ
  have hv : ∀ᵐ z ∂volume.restrict S,‖upperFunction u.toFun z‖≤1 :=
    Eventually.of_forall (cutoffSeed_bound δ D t hδ)
  have hmass := transferred_column_energy N (evenCoshLift (time K hc ε t))
    (evenCoshLift_smoothOn _ ((time K hc ε t).smooth ⊤) (time_even K hc he ε t) (time_compact K hc ε t))
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (evenCoshLift_support_of_time_support _ _ (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (time_support K hc ε t)) S hS δ (Real.exp (Strong.strongScale t/2)) hδ
    (fun _ hz => hz.2) m (by
      intro z Γ hΓ
      apply terminal_strip_overlap_bound N δ hδ z Γ
      intro g hg
      exact ⟨(hΓ g hg).1.1,(hΓ g hg).1.2,(hΓ g hg).2.1⟩)
    (upperFunction u.toFun) (upperFunction_continuous u.smooth).aestronglyMeasurable hv
  rw [boundedCrossQuotientLocalization_smooth N 0 S hS u (fun z _ => cutoffSeed_bound δ D t hδ z)] at hmass
  have hrect := ht (Real.exp (Strong.strongScale t/2)) (Real.exp_pos _).le
    (le_of_eq (congrArg Real.exp (by ring)))
  change (∫ z in S,‖column K hc he ε t z‖^2)≤B*(t*ε t) at hrect
  change (∫ z,‖cutoffTransfer N δ D t hδ (cylinderAutomorphic (column K hc he ε t z))‖^2
    ∂quotientMeasure 0)≤(m:ℝ)*(∫ z in S,‖column K hc he ε t z‖^2) at hmass
  exact hmass.trans ((mul_le_mul_of_nonneg_left hrect hmpos.le).trans_eq (by ring))

#print axioms cutoffTransfer_sharp_energy
end QuantitativeMaass.Scheduled
