module

public import QuantitativeMaassLocalHalfDensityV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

theorem localHalfDensity_representative_ae (w A B : ℝ) (hw : 0<w)
    (f : Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B))))
    (F : ℝ → ℂ)
    (hF : (f : ℝ → ℂ)=ᵐ[heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B))] F) :
    (localHalfDensity w A B hw f : ℝ → ℂ)=ᵐ[volume.restrict (Icc A B)]
      fun x => (Real.exp (-x/2):ℂ)*F (Real.exp x) := by
  have hac : volume.restrict (Icc A B) ≪ logBandMeasure w A B :=
    Measure.absolutelyContinuous_of_le_smul (volume_le_logBandMeasure w A B hw)
  have hp0 : (fun x => f (Real.exp x))=ᵐ[logBandMeasure w A B]
      fun x => F (Real.exp x) :=
    (exp_logBand_preserving w A B hw.le).quasiMeasurePreserving.ae hF
  have hp := hac.ae_eq hp0
  filter_upwards [localHalfDensity_ae w A B hw f,hp] with x hx hfx
  exact hx.trans (congrArg ((Real.exp (-x/2):ℂ) * ·) hfx)

/-- The actual half-density change of coordinates preserves the Hilbert
pairing up to the horizontal width. This holds on all local L2 classes. -/
theorem localHalfDensity_inner (w A B : ℝ) (hw : 0<w)
    (f g : Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B)))) :
    inner ℂ f g = (w:ℂ)*inner ℂ (localHalfDensity w A B hw f)
      (localHalfDensity w A B hw g) := by
  rw [L2.inner_def,L2.inner_def,← integral_const_mul]
  have hm := heightMeasure_rectangle_eq w (Real.exp A) (Real.exp B) hw.le (Real.exp_pos A)
  have hi := congrArg (fun μ : Measure ℝ => ∫ y, inner ℂ (f y) (g y) ∂μ) hm
  rw [hi,heightBandMeasure_integral_exp w A B hw.le]
  apply integral_congr_ae
  filter_upwards [localHalfDensity_ae w A B hw f,localHalfDensity_ae w A B hw g] with x hf hg
  rw [hf,hg]
  have hexp : Real.exp (-x/2)*Real.exp (-x/2)=Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpc := congrArg (fun z : ℝ => (z:ℂ)) hexp
  simp only [Complex.ofReal_mul] at hexpc
  simp only [RCLike.inner_apply,Complex.real_smul,Complex.ofReal_mul,
    map_mul,Complex.conj_ofReal]
  rw [← hexpc]
  ring

#print axioms localHalfDensity_representative_ae
#print axioms localHalfDensity_inner

end QuantitativeMaass
