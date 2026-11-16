module

public import QuantitativeMaassJointMetricPhysicalV1

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns ContinuousLinearMap
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass.RawOriginalWindow

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

/-- The literal combined-parity original window has canonical coefficient
one and an exact positive source-excess column trace. The same concrete scalar cover is used
in the physical count and the regular canonical filter. All packet summability,
source containment and factorization inputs are discharged here. -/
theorem bothWindow_joint_metric_sector_count {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (cover : AdmissibleScalarCover N hN)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)
    {ι κ η : Type*} [Countable ι] [Countable κ]
    (b : HilbertBasis ι ℂ (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε))
    (c : HilbertBasis κ ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (d : HilbertBasis η ℂ (completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e)))
    (t ε : ℝ) (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hlower : ∀ r∈Icc t (t+ε),1≤(cosinePacket f r).re) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let L := (cover.metric P'.epsilon_pos (show 1≤P'.s+3 by omega)).change
    let U := (fullTerminalTranslationIsometry A hN.1 P e).toContinuousLinearMap
    let C := U.comp (fullTerminalColumnOutput A hN.1 P e)
    let D := L.symm.toContinuousLinearMap
    let Qsrc := (RawCommonReconstruction.metricCylinderSource A P e L).starProjection
    let Qcan := cover.physicalNewSignProjection P'.epsilon_pos (show 1≤P'.s+3 by omega)
      (sectorCharacter N hN.1 e) (sectorCharacter_norm N hN.1 e)
    Finite (BothWindowSector A P e t ε) ∧
      (Nat.card (BothWindowSector A P e t ε):ℝ)≤
        hilbertSchmidtEnergy d (completedNewSignTimePacket N hN.1 (sectorCharacter N hN.1 e)
          f (f.smooth ⊤) he hc hr R hR hs)+
        (‖L.toContinuousLinearMap‖^2*‖C‖^2)*
          columnLinearTrace (volume.restrict (AsymptoticCertificateOperators.highStrip P'.ε))
            (cylinderCenteredCappedColumn f hc he R hR hs P'.ε (P'.s+3))
            ((D.comp Qsrc).comp D.adjoint-(D.comp Qcan).comp D.adjoint) := by
  intro P' L U C D Qsrc Qcan
  let χ := sectorCharacter N hN.1 e
  let J := cover.physicalNewSignIsometry P'.epsilon_pos (show 1≤P'.s+3 by omega) χ
    (sectorCharacter_norm N hN.1 e)
  let : CompleteSpace J.toContinuousLinearMap.range :=
    J.isometry.isClosedEmbedding.isClosed_range.completeSpace_coe
  let B := extendedTerminalPacket A P e f hc he hr R hR hs
  let T := completedNewSignTimePacket N hN.1 χ f (f.smooth ⊤) he hc hr R hR hs
  have hJU (x) : J x∈RawCommonReconstruction.metricCylinderSource A P e L :=
    cover.physicalNewSignIsometry_source A P e χ
      (sectorCharacter_norm N hN.1 e) (sectorCharacter_coherent N hN.1 e).1
      (sectorCharacter_coherent N hN.1 e).2 x
  have hBT (x) : similarityOperator L B (J x)=J (T x) :=
    cover.physicalNewSignIsometry_terminal_packet A P e χ (sectorCharacter_norm N hN.1 e)
      (sectorCharacter_coherent N hN.1 e).1 (sectorCharacter_coherent N hN.1 e).2
      f hc he hr R hR hs x
  have hB : Summable (fun i => ‖B (c i)‖^2) :=
    (isometry_extension_energy (fullTerminalTranslationIsometry A hN.1 P e) b c _
      (EulerHilbert.FullTerminal.centeredTerminalPacket_summable A hN.1 P f hc he hr R hR hs b e)).1
  have hT : Summable (fun i => ‖T (d i)‖^2) :=
    (isometric_packet_summable c d J (similarityOperator L B) T hBT
      (similarityOperator_summable c L B hB)).1
  let μ := volume.restrict (AsymptoticCertificateOperators.highStrip P'.ε)
  let col := cylinderCenteredCappedColumn f hc he R hR hs P'.ε (P'.s+3)
  have hcol : MemLp col 2 μ :=
    cylinderCenteredCappedColumn_memLp f hc he hr R hR hs P'.ε (P'.s+3) P'.ε P'.epsilon_pos
  have hsource (p) : L (bothWindowCylinderDatum A P e t ε p)∈
      RawCommonReconstruction.metricCylinderSource A P e L :=
    ⟨_,bothWindowCylinderDatum_source A P e t ε p,rfl⟩
  have hfactor (x) (hx : L x∈RawCommonReconstruction.metricCylinderSource A P e L) :
      B x=C (finiteEnergyColumnOperator μ col hcol x) := by
    rcases hx with ⟨y,hy,hyx⟩
    have hy' : y=x := L.injective hyx
    subst y
    exact RawCommonReconstruction.cylinderSource_terminal_column_factor A P e f hc he hr R hR hs x hy
  have hh := metric_source_column_count c d L B T
    (RawCommonReconstruction.metricCylinderSource A P e L) J hJU hBT
    (bothWindowCylinderDatum A P e t ε) (bothWindowCylinderDatum_independent A P e t ε) hsource
    (fun p => (cosinePacket f (bothWindowParameter A P e t ε p)).re)
    (bothWindowCylinderDatum_eigen A P e t ε f hc he hr R hR hs)
    (fun p => hlower _ (bothWindowParameter_mem A P e t ε p)) hB hT μ col hcol C hfactor
  rw [←isometric_cogram_projection J] at hh
  exact hh

#print axioms bothWindow_joint_metric_sector_count
end QuantitativeMaass.RawOriginalWindow
