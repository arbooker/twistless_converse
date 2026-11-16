module

public import QuantitativeMaassTranslatedTestSmoothV1
public import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

theorem add_logBand_preserving (A B t : ℝ) :
    MeasurePreserving (fun x : ℝ => x+t) (volume.restrict (Icc A B))
      (volume.restrict (Icc (t+A) (t+B))) := by
  have he : (fun x : ℝ => x+t) ⁻¹' Icc (t+A) (t+B)=Icc A B := by
    ext x
    simp only [mem_preimage,mem_Icc]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have h := (measurePreserving_add_right (volume:Measure ℝ) t).restrict_preimage
    (s := Icc (t+A) (t+B)) measurableSet_Icc
  rwa [he] at h

/-- Actual isometric pullback from a translated log-height band. -/
def logBandTranslate (A B t : ℝ) :
    Lp ℂ 2 (volume.restrict (Icc (t+A) (t+B))) →ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict (Icc A B)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x+t) (add_logBand_preserving A B t)

theorem logBandTranslate_ae (A B t : ℝ)
    (f : Lp ℂ 2 (volume.restrict (Icc (t+A) (t+B)))) :
    (logBandTranslate A B t f : ℝ → ℂ)=ᵐ[volume.restrict (Icc A B)] fun x => f (x+t) :=
  Lp.coeFn_compMeasurePreserving f (add_logBand_preserving A B t)

theorem logBandTranslate_test (A B t : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    logBandTranslate A B t (translatedLogTest (t+A) (t+B) ψ hψ t)=
      logTestVector A B ψ hψ := by
  apply Lp.ext
  have hp : (fun x => (translatedLogTest (t+A) (t+B) ψ hψ t : ℝ → ℂ) (x+t))
      =ᵐ[volume.restrict (Icc A B)] fun x => ψ ((x+t)-t) :=
    (add_logBand_preserving A B t).quasiMeasurePreserving.ae
      (translatedLogTest_ae (t+A) (t+B) ψ hψ t)
  filter_upwards [logBandTranslate_ae A B t _,hp,logTestVector_ae A B ψ hψ] with x h1 h2 h3
  simpa only [add_sub_cancel_right] using (h1.trans h2).trans (by simpa only [add_sub_cancel_right] using h3.symm)

/-- Pullback moves translation from the test onto the actual L2 state. -/
theorem logBandTranslate_pairing (A B t : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (f : Lp ℂ 2 (volume.restrict (Icc (t+A) (t+B)))) :
    inner ℂ (logTestVector A B ψ hψ) (logBandTranslate A B t f)=
      inner ℂ (translatedLogTest (t+A) (t+B) ψ hψ t) f := by
  rw [← logBandTranslate_test A B t ψ hψ]
  exact (logBandTranslate A B t).inner_map_map _ _

#print axioms logBandTranslate_ae
#print axioms logBandTranslate_pairing

end QuantitativeMaass
