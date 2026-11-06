module

public import AsymptoticCylinderTraceV1
public import AsymptoticRegionL2V1
public import AsymptoticExponentialTraceTailV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open MeasureTheory Set Filter ContinuousLinearMap InnerProductSpace AsymptoticFourierNorm
open AsymptoticDiagonalTrace
open scoped InnerProduct

noncomputable def upperRegion (H : ℝ) : Set Cylinder := {z | H<z.2}

theorem upperRegion_measurable (H : ℝ) : MeasurableSet (upperRegion H) :=
  measurableSet_Ioi.preimage measurable_snd

/-- Restriction to the actual upper cusp, extended by zero. -/
noncomputable def upperProjection (H : ℝ) : Space →L[ℂ] Space :=
  AsymptoticRegionL2.projection measure (upperRegion H) (upperRegion_measurable H)

theorem upperProjection_mode_norm_sq (m t n : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (H : ℝ) :
    ‖upperProjection H (modeLp m t n hs hε)‖^2=
      ∫ y in Ioi H,density m t (scale*(n+1:ℕ)) ε y ∂(volume.restrict (Ioi 0)) := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  calc
    _ = ∫ z,(Ioi H).indicator (density m t (scale*(n+1:ℕ)) ε) z.2 ∂measure := by
      apply integral_congr_ae
      filter_upwards [AsymptoticRegionL2.projection_coeFn measure (upperRegion H) (upperRegion_measurable H)
        (modeLp m t n hs hε),modeLp_coeFn m t n hs hε,height_positive] with z hp hf hz
      change ‖upperProjection H (modeLp m t n hs hε) z‖^2=_
      change upperProjection H (modeLp m t n hs hε) z=
        (upperRegion H).indicator (modeLp m t n hs hε) z at hp
      rw [hp]
      classical
      by_cases hHz : H<z.2
      · rw [indicator_of_mem (show z∈upperRegion H from hHz),hf,
          indicator_of_mem (show z.2∈Ioi H from hHz)]
        exact mode_norm_sq m t n scale hε hz.le
      · rw [indicator_of_notMem (show z∉upperRegion H from hHz),
          indicator_of_notMem (show z.2∉Ioi H from hHz)]
        simp
    _ = ∫ y,(Ioi H).indicator (density m t (scale*(n+1:ℕ)) ε) y ∂(volume.restrict (Ioi 0)) := by
      have hi := integral_prod_mul (μ:=AddCircle.haarAddCircle (T:=1))
        (ν:=volume.restrict (Ioi 0)) (fun _ : AddCircle (1:ℝ) => (1:ℝ))
        ((Ioi H).indicator (density m t (scale*(n+1:ℕ)) ε))
      simpa [measure] using hi
    _ = _ := integral_indicator measurableSet_Ioi

/-- The diagonal upper-cusp mass is the normalized radial tail already
bounded by the rescaling argument. -/
theorem upperProjection_unitMode_norm_sq (m t n : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (H : ℝ) :
    ‖upperProjection H (unitMode m t n hs hε)‖^2=upperMass m t (scale*(n+1:ℕ)) ε H := by
  simp only [unitMode,map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt (beta_nonneg m t hε),upperProjection_mode_norm_sq,upperMass]
  rw [div_eq_mul_inv,mul_comm]

/-- The compression of upper-cusp restriction to the actual weighted
holomorphic Fourier space. -/
noncomputable def upperCompression (m t : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (H : ℝ) :
    holomorphicSpace m t hs hε →L[ℂ] holomorphicSpace m t hs hε :=
  let U := holomorphicSpace m t hs hε
  U.subtypeL.adjoint.comp ((upperProjection H).comp U.subtypeL)

theorem upperProjection_inner (H : ℝ) (f : Space) :
    (⟪upperProjection H f,f⟫_ℂ).re=‖upperProjection H f‖^2 := by
  have ha : (upperProjection H).adjoint=upperProjection H :=
    AsymptoticRegionL2.projection_adjoint _ _ _
  have hi : upperProjection H (upperProjection H f)=upperProjection H f :=
    AsymptoticRegionL2.projection_idempotent _ _ _ f
  have he := (upperProjection H).adjoint_inner_left f (upperProjection H f)
  rw [ha,hi] at he
  rw [he]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) _

theorem upperCompression_diagonal (m t n : ℕ) {scale ε : ℝ}
    (hs : 0<scale) (hε : 0<ε) (H : ℝ) :
    (⟪upperCompression m t hs hε H (fourierBasis m t hs hε n),fourierBasis m t hs hε n⟫_ℂ).re=
      upperMass m t (scale*(n+1:ℕ)) ε H := by
  let U := holomorphicSpace m t hs hε
  have he := U.subtypeL.adjoint_inner_left (fourierBasis m t hs hε n)
    (upperProjection H ((fourierBasis m t hs hε n:U):Space))
  change (⟪U.subtypeL.adjoint (upperProjection H ((fourierBasis m t hs hε n:U):Space)),
    fourierBasis m t hs hε n⟫_ℂ).re=_
  rw [he]
  change (⟪upperProjection H ((fourierBasis m t hs hε n:U):Space),
    ((fourierBasis m t hs hε n:U):Space)⟫_ℂ).re=_
  rw [upperProjection_inner]
  simpa only [fourierBasis_apply,modeInSpace] using upperProjection_unitMode_norm_sq m t n hs hε H

/-- The O(k/H)+O_H(1) bound for the trace of the actual upper-cusp
compression. No abstract sequence or projection identity is assumed. -/
theorem upperCompression_trace_bound (m t : ℕ) {scale ε H : ℝ}
    (hs : 0<scale) (hε : 0<ε) (hH : 0<H) :
    Summable (fun n => (⟪upperCompression m t hs hε H (fourierBasis m t hs hε n),fourierBasis m t hs hε n⟫_ℂ).re) ∧
      trace (fourierBasis m t hs hε) (upperCompression m t hs hε H)≤
        ((m+2*t+1:ℕ):ℝ)*Real.log 2/(scale*H/2)+1/(1-Real.exp (-(scale*H/2))) := by
  simp only [trace,upperCompression_diagonal]
  exact upperMass_summable_bound m t hs hε hH

#print axioms upperProjection_mode_norm_sq
#print axioms upperProjection_unitMode_norm_sq
#print axioms upperCompression_diagonal
#print axioms upperCompression_trace_bound

end AsymptoticCylinder
