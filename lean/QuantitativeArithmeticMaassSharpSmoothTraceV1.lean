module

public import QuantitativeArithmeticMaassTransferCenterSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal ContDiff
namespace QuantitativeMaass

/-- The nonnegative collar bound is a finite real energy inequality for
actual full-cylinder transferred columns. -/
theorem transferred_column_collar_real_energy (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (lo hi : ℝ) (hlo : 0<lo)
    (hheight : ∀ x∈K, lo≤x.im ∧ x.im≤hi) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ∈S, γ • z∈K) → S.card≤m)
    (v w : ℍ → ℂ)
    (hv : AEStronglyMeasurable v (volume.restrict K))
    (hw : AEStronglyMeasurable w (volume.restrict K)) (A B C : ℝ)
    (hvB : ∀ᵐ x ∂volume.restrict K, ‖v x‖≤A)
    (hwB : ∀ᵐ x ∂volume.restrict K, ‖w x‖≤B)
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hchange : ∀ᵐ x ∂volume.restrict K, ‖v x-w x‖≤C ∧ (x∉Ω → v x=w x)) :
    let c := fun z => cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z)
    (∫ z, ‖boundedCrossQuotientLocalization N 0 K hK v hv hvB (c z)-
      boundedCrossQuotientLocalization N 0 K hK w hw hwB (c z)‖^2 ∂quotientMeasure 0) ≤
      (m:ℝ)*C^2*(∫ x in Ω, ‖cylinderAbelColumn F hF R hR hs x‖^2 ∂volume.restrict K) := by
  intro c
  have h1 := boundedCrossQuotientLocalization_column_memLp N F hF R hR hs K hK lo hi hlo hheight v hv hvB
  have h2 := boundedCrossQuotientLocalization_column_memLp N F hF R hR hs K hK lo hi hlo hheight w hw hwB
  have hd := (memLp_two_iff_integrable_sq_norm (h1.sub h2).aestronglyMeasurable).mp (h1.sub h2)
  have hiK : Integrable (fun x => ‖cylinderAbelColumn F hF R hR hs x‖^2) (volume.restrict K) :=
    ((cylinderAbelColumn_continuous F hF R hR hs).norm.pow 2).continuousOn.integrableOn_compact hK
  have ho := Integrable.restrict (s := Ω) hiK
  have hb := cylinderAbelColumn_transfer_collar_energy N F hF R hR hs K hK m hm
    v w hv hw A B C hvB hwB Ω hΩ hchange
  simp only [Pi.sub_apply] at hd
  rw [←ofReal_integral_eq_lintegral_ofReal hd (Eventually.of_forall (fun _ => sq_nonneg _)),
    ←ofReal_integral_eq_lintegral_ofReal ho (Eventually.of_forall (fun _ => sq_nonneg _)),
    ←ENNReal.ofReal_mul (by positivity : 0≤(m:ℝ)*C^2)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

/-- A full-cylinder quadratic trace changes by a tunable energy error
when the transfer multiplier is changed only in a spatial collar. -/
theorem transferred_column_collar_trace_error (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (lo hi : ℝ) (hlo : 0<lo)
    (hheight : ∀ x∈K, lo≤x.im ∧ x.im≤hi) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ∈S, γ • z∈K) → S.card≤m)
    (v w : ℍ → ℂ)
    (hv : AEStronglyMeasurable v (volume.restrict K))
    (hw : AEStronglyMeasurable w (volume.restrict K)) (A B C : ℝ)
    (hvB : ∀ᵐ x ∂volume.restrict K, ‖v x‖≤A)
    (hwB : ∀ᵐ x ∂volume.restrict K, ‖w x‖≤B)
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hchange : ∀ᵐ x ∂volume.restrict K, ‖v x-w x‖≤C ∧ (x∉Ω → v x=w x))
    (T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (η : ℝ) (hη : 0<η) :
    let c := fun z => cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z)
    let u := fun z => boundedCrossQuotientLocalization N 0 K hK v hv hvB (c z)
    let d := fun z => boundedCrossQuotientLocalization N 0 K hK w hw hwB (c z)
    |columnLinearTrace (quotientMeasure 0) u T-columnLinearTrace (quotientMeasure 0) d T| ≤
      ‖T‖*(η*(∫ z, ‖d z‖^2 ∂quotientMeasure 0)+(1+η⁻¹)*
        ((m:ℝ)*C^2*(∫ x in Ω, ‖cylinderAbelColumn F hF R hR hs x‖^2 ∂volume.restrict K))) := by
  intro c u d
  have hu := boundedCrossQuotientLocalization_column_memLp N F hF R hR hs K hK lo hi hlo hheight v hv hvB
  have hd := boundedCrossQuotientLocalization_column_memLp N F hF R hR hs K hK lo hi hlo hheight w hw hwB
  have hb := columnLinearTrace_column_perturbation (quotientMeasure 0) u d hu hd T η hη
  have he := transferred_column_collar_real_energy N F hF R hR hs K hK lo hi hlo hheight m hm
    v w hv hw A B C hvB hwB Ω hΩ hchange
  apply hb.trans
  gcongr


/-- The literal canonical restriction may be smoothed inside the global
column trace. The error retains only the energy of the boundary collar. -/
theorem compactQuotientRestriction_smoothing_trace (N : ℕ)
    {δ : ℝ} (hδ : 0<δ) {v : ℕ} (hv : 1≤v) {R : ℝ} (hR : 0≤R)
    (a b h : ℝ) (ha : 0<a) (hh : 0<h) (hheight : δ*Real.exp (-R)≤a)
    (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ γ∈S, γ • z∈upperRectangle 0 1 a b) → S.card≤m)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (T : ℝ) (hT : 0≤T) (hs : Function.support F ⊆ Iic (Real.cosh T))
    (O : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (η : ℝ) (hη : 0<η) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    let Ω := S \ upperRectangle h (1-h) (a+h) (b-h)
    let u := rectangleSmoothSeed 0 1 a b h ha hh
    let hu : ∀ z∈S, ‖upperFunction u.toFun z‖≤1 :=
      fun z _ => (rectangleCutoffFunction_bounds 0 1 a b h z).2
    let Q := compactQuotientRestriction N hδ hv R S hS.measurableSet
    let c := fun z => cylinderAbelColumn F hF T hT hs z
    let d := fun z => crossQuotientLocalization N 0 S hS u hu (cylinderAutomorphic (c z))
    |columnLinearTrace (quotientMeasure 0) (fun z => Q.adjoint (c z)) O-
      columnLinearTrace (quotientMeasure 0) d O| ≤
      ‖O‖*(η*(∫ z, ‖d z‖^2 ∂quotientMeasure 0)+
        (1+η⁻¹)*((m:ℝ)*(∫ x in Ω, ‖c x‖^2 ∂volume.restrict S))) := by
  intro S hS Ω u hu Q c d
  have hΩ : MeasurableSet Ω := hS.measurableSet.diff (upperRectangle_measurable _ _ _ _)
  have hb : ∀ᵐ z ∂volume.restrict S, ‖upperFunction u.toFun z‖≤1 := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    exact hu z hz
  have hchange : ∀ᵐ z ∂volume.restrict S,
      ‖(1:ℂ)-upperFunction u.toFun z‖≤1 ∧ (z∉Ω → (1:ℂ)=upperFunction u.toFun z) := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    have hc := rectangleSmoothSeed_collar 0 1 a b h ha hh z
    dsimp only at hc
    change z∈upperRectangle 0 1 a b at hz
    simpa only [zero_add,Set.indicator_of_mem hz] using hc
  have hbound := transferred_column_collar_trace_error N F hF T hT hs S hS a b ha
    (fun z hz => hz.2) m hm (fun _ => (1:ℂ)) (upperFunction u.toFun)
    aestronglyMeasurable_const (upperFunction_continuous u.smooth).aestronglyMeasurable
    1 1 1 (Eventually.of_forall (fun _ => by simp)) hb Ω hΩ hchange O η hη
  have heq (z : ℍ) : Q.adjoint (c z)=
      boundedCrossQuotientLocalization N 0 S hS (fun _ => (1:ℂ)) aestronglyMeasurable_const
        (A := 1) (Eventually.of_forall (fun _ => by simp)) (cylinderAutomorphic (c z)) :=
    compactQuotientRestriction_eq_boundedTransfer N hδ hv hR a b ha hheight _
  simp_rw [heq]
  simpa only [one_pow,mul_one,boundedCrossQuotientLocalization_smooth N 0 S hS u hu] using hbound

#print axioms compactQuotientRestriction_smoothing_trace

#print axioms transferred_column_collar_real_energy
#print axioms transferred_column_collar_trace_error
end QuantitativeMaass
