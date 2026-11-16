module

public import QuantitativeMaassJointMetricExcessV1
public import QuantitativeMaassPhysicalCylinderFilterV1
public import QuantitativeMaassCappedCompactTraceV1
public import QuantitativeMaassCompactCenteringTraceV1

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticClassicalPetersson
open AsymptoticSectorSigns AsymptoticFiniteBranch AsymptoticCongruenceStrip
open AsymptoticCertificateOperators
open scoped SchwartzMap
namespace QuantitativeMaass.RawCommonReconstruction

/-- Compact localization and centering for a positive source excess,
with the finite-filter substitution performed after localization. -/
theorem positive_excess_compact_filter_bound
    (W : Submodule ℂ (Lp ℂ 2 (quotientMeasure 0))) [CompleteSpace W]
    (F Qcan D : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    (hF : 0≤F) {δ : ℝ} (herror : ‖F*W.starProjection-W.starProjection‖≤δ)
    (hT : (D*W.starProjection*D.adjoint-D*Qcan*D.adjoint).IsPositive)
    {ι : Type*} [Countable ι] (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {ε : ℝ} (hε : 0<ε) (m : ℕ) (H : ℝ) (hH : ε≤H)
    (Coff : ℝ) (hCoff : 0≤Coff)
    (hoff : ∀ d : ℝ,0<d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖≤Coff/Real.sqrt (Real.sinh d)) :
    let T := D*W.starProjection*D.adjoint-D*Qcan*D.adjoint
    let J := ⌈(m:ℝ)*R+1⌉₊
    let K := terminalInverseWeightBand ε m J
    let a := ε*Real.exp (-R)
    let b := H*Real.exp R
    let Pc := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ (mul_pos hε (Real.exp_pos _))).measurableSet
    let c := fun z => Pc (cylinderTimeColumn f hc he R hR hs z)
    let L := K.comp D
    columnLinearTrace (volume.restrict (highStrip ε))
      (cylinderCenteredCappedColumn f hc he R hR hs ε m) T≤
      2*(columnLinearTrace (quotientMeasure 0) c (L*(F-Qcan)*L.adjoint)+
        (3*δ*‖L‖^2)*(∫ z,‖c z‖^2 ∂quotientMeasure 0))+
      2*‖K.comp (T.comp K.adjoint)‖*(max 0 (b*Real.exp R)*
        (Coff*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)))*
        volume.real (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)))+
      ‖T‖*(((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*
        (H⁻¹*|(abelProfile (evenCoshLift (timeConvolution f f)) 1).re|)) := by
  intro T J K a b Pc c L
  have hcap := centeredCapped_trace_compact_input_bound basis f hc he hr R hR hs hε m hH T hT
  have hKT : (K.comp (T.comp K.adjoint)).IsPositive := by
    simpa only [comp_assoc] using hT.conj_adjoint K
  have hcenter := compact_input_centered_trace_uncenter f hc he hr R hR hs
    (mul_pos hε (Real.exp_pos (-R))) b Coff hCoff hoff (K.comp (T.comp K.adjoint)) hKT
  have hcL : MemLp c 2 (quotientMeasure 0) :=
    cylinderTimeColumn_compact_input_memLp f hc he R hR hs (mul_pos hε (Real.exp_pos (-R))) b
  have hfilter := column_source_filter_excess (quotientMeasure 0) c hcL W F Qcan L hF herror
  have halg : K.comp (T.comp K.adjoint)=L*W.starProjection*L.adjoint-L*Qcan*L.adjoint := by
    dsimp only [T,L]
    simp only [mul_def,adjoint_comp,comp_sub,sub_comp,comp_assoc]
  rw [←halg] at hfilter
  have hfinal := hcenter.trans (add_le_add (mul_le_mul_of_nonneg_left hfilter (by norm_num)) le_rfl)
  exact hcap.trans (add_le_add hfinal le_rfl)

/-- The actual positive original-source excess is reduced to compact-input
uncentered finite-filter excess. The canonical subtraction survives; the other
terms explicitly record source recovery, centering and the upper height tail. -/
theorem physical_excess_compact_filter_bound {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (cover : AdmissibleScalarCover N hN) (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)
    {ι : Type*} [Countable ι] (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (H : ℝ) (hH : (AsymptoticReconstructedCount.parameters A P).ε≤H)
    (Coff : ℝ) (hCoff : 0≤Coff)
    (hoff : ∀ d : ℝ,0<d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖≤Coff/Real.sqrt (Real.sinh d))
    (E : Expression) (hE : 0≤holomorphicSum E 0) (Kerr : ℝ) (n : ℕ)
    (herror : let P' := AsymptoticReconstructedCount.parameters A P
      let M := cover.metric P'.epsilon_pos (show 1≤P'.s+3 by omega)
      ‖holomorphicSum E 0*(physicalMetricSource A P e M).starProjection-
        (physicalMetricSource A P e M).starProjection‖^2≤Kerr/(2:ℝ)^n) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let M := cover.metric P'.epsilon_pos (show 1≤P'.s+3 by omega)
    let D := M.change.symm.toContinuousLinearMap
    let Qsrc := (metricCylinderSource A P e M.change).starProjection
    let Qcan := cover.physicalNewSignProjection P'.epsilon_pos (show 1≤P'.s+3 by omega)
      (sectorCharacter N hN.1 e) (sectorCharacter_norm N hN.1 e)
    let T := D*Qsrc*D.adjoint-D*Qcan*D.adjoint
    let J := ⌈((P'.s+3:ℕ):ℝ)*R+1⌉₊
    let K := terminalInverseWeightBand P'.ε (P'.s+3) J
    let a := P'.ε*Real.exp (-R)
    let b := H*Real.exp R
    let Pc := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ (mul_pos P'.epsilon_pos (Real.exp_pos _))).measurableSet
    let c := fun z => Pc (cylinderTimeColumn f hc he R hR hs z)
    let Z := cylinderZeroExtension.toContinuousLinearMap
    let F := Z.adjoint.comp ((holomorphicSum E 0).comp Z)
    let L := K.comp D
    columnLinearTrace (volume.restrict (highStrip P'.ε))
      (cylinderCenteredCappedColumn f hc he R hR hs P'.ε (P'.s+3)) T≤
      2*(columnLinearTrace (quotientMeasure 0) c (L*(F-Qcan)*L.adjoint)+
        (3*Real.sqrt (Kerr/(2:ℝ)^n)*‖L‖^2)*(∫ z,‖c z‖^2 ∂quotientMeasure 0))+
      2*‖K.comp (T.comp K.adjoint)‖*(max 0 (b*Real.exp R)*
        (Coff*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)))*
        volume.real (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)))+
      ‖T‖*(((((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))^2)*
        (H⁻¹*|(abelProfile (evenCoshLift (timeConvolution f f)) 1).re|)) := by
  intro P' M D Qsrc Qcan T J K a b Pc c Z F L
  have hT : T.IsPositive := cover.physical_source_excess_positive A P e
  have hF : 0≤F := nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hE).adjoint_conj Z)
  have herr := physical_filter_cylinder_error A P e M (holomorphicSum E 0)
    (Real.le_sqrt_of_sq_le herror)
  exact positive_excess_compact_filter_bound (metricCylinderSource A P e M.change) F Qcan D hF herr hT
    basis f hc he hr R hR hs P'.epsilon_pos (P'.s+3) H hH Coff hCoff hoff

#print axioms positive_excess_compact_filter_bound
#print axioms physical_excess_compact_filter_bound
end QuantitativeMaass.RawCommonReconstruction
