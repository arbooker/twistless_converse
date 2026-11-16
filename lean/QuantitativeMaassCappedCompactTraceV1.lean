module

public import QuantitativeMaassCompactInputColumnsV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open AsymptoticCertificateOperators
open scoped SchwartzMap
namespace QuantitativeMaass

/-- The actual capped centered excess is bounded by one compact-input
uncapped centered trace plus its explicit sharp upper-tail error. All column
support and integrability hypotheses are discharged for the concrete packet. -/
theorem centeredCapped_trace_compact_input_bound {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {ε : ℝ} (hε : 0<ε) (m : ℕ) {H : ℝ} (hH : ε≤H)
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) (hT : T.IsPositive) :
    let J := ⌈(m:ℝ)*R+1⌉₊
    let K := terminalInverseWeightBand ε m J
    let P := AsymptoticRegionL2.projection (quotientMeasure 0)
      (upperRectangle 0 1 (ε*Real.exp (-R)) (H*Real.exp R))
      (upperRectangle_compact _ _ _ _ (mul_pos hε (Real.exp_pos _))).measurableSet
    columnLinearTrace (volume.restrict (highStrip ε))
      (cylinderCenteredCappedColumn f hc he R hR hs ε m) T≤
    columnLinearTrace (quotientMeasure 0)
      (fun z => P (cylinderCenteredTimeColumn f hc he R hR hs z))
      (K.comp (T.comp K.adjoint))+
      ‖T‖*(((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*
        (H⁻¹*|(abelProfile (evenCoshLift (timeConvolution f f)) 1).re|)) := by
  intro J K P
  let S := highStrip ε\highStrip H
  have hS : MeasurableSet S := (highStrip_measurable ε).diff (highStrip_measurable H)
  have hsub : highStrip H⊆highStrip ε := fun z hz => ⟨hz.1,hH.trans hz.2⟩
  have hheight (z : ℍ) (hz : z∈S) : ε≤z.im ∧ z.im≤H := by
    refine ⟨hz.1.2,?_⟩
    have hh : ¬H≤z.im := fun hh => hz.2 ⟨hz.1.1,hh⟩
    exact (lt_of_not_ge hh).le
  have hmeasure : (quotientMeasure 0).restrict S=volume.restrict S := by
    rw [translation_quotient_measure,Measure.restrict_restrict hS]
    exact congrArg (fun A : Set ℍ => volume.restrict A)
      (inter_eq_left.mpr (fun z hz => hz.1.1))
  have hret : columnLinearTrace (volume.restrict S)
      (cylinderCenteredCappedColumn f hc he R hR hs ε m) T=
      columnLinearTrace ((quotientMeasure 0).restrict S)
        (fun z => P (cylinderCenteredTimeColumn f hc he R hR hs z))
        (K.comp (T.comp K.adjoint)) := by
    rw [hmeasure]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with z hz
    have hp := cylinderCenteredTimeColumn_height_projection f hc he R hR hs hε H z (hheight z hz)
    change P (cylinderCenteredTimeColumn f hc he R hR hs z)=_ at hp
    rw [hp,cylinderCenteredCappedColumn_terminal f hc he R hR hs hε m z hz.1.2]
    exact congrArg Complex.re (K.adjoint_inner_right _ _)
  have hpos : (K.comp (T.comp K.adjoint)).IsPositive := by
    simpa only [comp_assoc] using hT.conj_adjoint K
  have hle := compact_input_centered_trace_restrict_le f hc he R hR hs
    (mul_pos hε (Real.exp_pos (-R))) (H*Real.exp R) S (K.comp (T.comp K.adjoint)) hpos
  have hsplit := columnLinearTrace_nested_split volume
    (cylinderCenteredCappedColumn f hc he R hR hs ε m)
    (highStrip ε) (highStrip H) (highStrip_measurable H) hsub
    (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs ε m ε hε) T
  rw [hsplit,hret]
  exact add_le_add hle
    (cylinderCenteredCappedColumn_trace_tail basis f hc he hr R hR hs ε m H (hε.trans_le hH) T)

#print axioms centeredCapped_trace_compact_input_bound
end QuantitativeMaass
