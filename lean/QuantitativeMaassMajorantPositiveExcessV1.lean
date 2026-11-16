module

public import QuantitativeMaassCompactFilterExcessV1
public import QuantitativeMaassMajorantRecoveryScheduleV1
public import QuantitativeMaassCompactCenteringScheduleV1
public import QuantitativeMaassMajorantTailScheduleV1
public import QuantitativeMaassMajorantPropagationRadiusV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCertificateOperators
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- All localization remainders vanish for the actual majorant. The
remaining compact finite-filter limit is precisely the canonical cancellation
proved separately; this lemma does not assert that input without proof. -/
theorem originalMajorant_positive_excess_limit {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (W : Submodule ℂ (Lp ℂ 2 (quotientMeasure 0))) [CompleteSpace W]
    (F : ℕ→Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (Q D : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (hF : ∀ n,0≤F n) (Kerr : ℝ) (hKerr : 0≤Kerr)
    (herror : ∀ n,‖F n*W.starProjection-W.starProjection‖≤Real.sqrt (Kerr/(2:ℝ)^n))
    (hpositive : (D*W.starProjection*D.adjoint-D*Q*D.adjoint).IsPositive)
    (δ : ℝ) (hδ : 0<δ) (ν : ℕ) (C : ℝ) (hC : 1≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (hCs : supportRadius K hc≤C)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (hcompact : Tendsto (fun t =>
      let R := C*radius ε t
      let J := ⌈(ν:ℝ)*R+1⌉₊
      let a := movingLowerEdge δ C ε t
      let S := cutoffRectangle a t
      let Pc := AsymptoticRegionL2.projection (quotientMeasure 0) S
        (upperRectangle_compact 0 1 a _ (movingLowerEdge_pos hδ C ε t)).measurableSet
      let L := (terminalInverseWeightBand δ ν J).comp D
      columnLinearTrace (quotientMeasure 0) (fun z => Pc (originalMajorantColumn K hc he ε t z))
        (L*(F (rawBlockHorizon t)-Q)*L.adjoint)/(t*ε t)) atTop (𝓝 0)) :
    Tendsto (fun t => columnLinearTrace (volume.restrict (highStrip δ))
      (cylinderCenteredCappedColumn (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)
        (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)
        (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t)
        (C*radius ε t) (mul_nonneg (zero_le_one.trans hC) (radius_pos ε t).le)
        (originalMajorant_support_enlarged K hc ε t C hCs) δ ν)
      (D*W.starProjection*D.adjoint-D*Q*D.adjoint)/(t*ε t)) atTop (𝓝 0) := by
  let T := D*W.starProjection*D.adjoint-D*Q*D.adjoint
  obtain ⟨B,hB,hoff⟩ := originalMajorantSquare_abel_offdiagonal_bound K he hc
  have hrec := originalMajorant_compact_recovery_limit basis K hc he hK hm ε hε hp hδ ν C hC D Kerr hKerr
  have hcent := inverse_band_centering_cost ε hε hp hδ ν C B hC hB.le T
  have htail := originalMajorant_compact_tail_limit K hc he hK hm ε hε hp ν C hC T
  have hlim := (((hcompact.add hrec).const_mul 2).add hcent).add htail
  simp only [add_zero,mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    exact div_nonneg (columnLinearTrace_nonneg _ _ _ hpositive) (mul_pos ht heps.1).le
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ),half_height_eventually_ge ε hε hp C (zero_le_one.trans hC) hδ,
      hoff ε hε hp] with t heps ht hheight hoff
    let R := C*radius ε t
    let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
    let H := Real.exp (Strong.strongScale t/2-R)
    have hheight' : δ≤H := hheight
    have hb : H*Real.exp R=Real.exp (Strong.strongScale t/2) := by
      dsimp only [H]
      rw [←Real.exp_add]
      congr 1
      ring
    have hbound := RawCommonReconstruction.positive_excess_compact_filter_bound W
      (F (rawBlockHorizon t)) Q D (hF _) (herror _) hpositive basis f
      (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)
      (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t)
      (QuantitativeNinaMaass.originalWindowMajorant_real K he hc ε t)
      R (mul_nonneg (zero_le_one.trans hC) (radius_pos ε t).le)
      (originalMajorant_support_enlarged K hc ε t C hCs) hδ ν H hheight'
      (B*Real.sqrt t*(radius ε t)^2*(ε t)^2) (by positivity) hoff
    dsimp only at hbound ⊢
    rw [hb] at hbound
    have hd := div_le_div_of_nonneg_right hbound (mul_pos ht heps.1).le
    convert hd using 1
    dsimp only [T,R,H,f,movingLowerEdge,cutoffRectangle,
      originalMajorantColumn,cylinderTimeColumn,cylinderAbelColumn]
    simp only [mul_def,comp_assoc]
    ring

#print axioms originalMajorant_positive_excess_limit
end QuantitativeMaass.Scheduled
