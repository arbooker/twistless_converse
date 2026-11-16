module

public import QuantitativeMaassJointScalarCoverV1
public import QuantitativeMaassRawMetricWindowCountV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory ContinuousLinearMap AsymptoticClassicalPetersson AsymptoticSectorSigns
open QuantitativeNewGap
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass.AdmissibleScalarCover

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

variable {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (cover : AdmissibleScalarCover N hN)

def physicalNewSignIsometry {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1) :
    completedNewSignSpace N hN.1 χ→ₗᵢ[ℂ]Lp ℂ 2 (quotientMeasure 0) where
  toLinearMap := ((scalarMetricQuotientEmbedding N (cover.metric hδ hν) hδ hν).comp
    (completedNewSignSpace N hN.1 χ).subtypeL).toLinearMap
  norm_map' x := cover.physical_norm hδ hν χ hχ ⟨x.val,x.property.2.2⟩

def physicalNewSignProjection {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1) :
    Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0) :=
  (cover.physicalNewSignIsometry hδ hν χ hχ).toContinuousLinearMap.comp
    (cover.physicalNewSignIsometry hδ hν χ hχ).toContinuousLinearMap.adjoint

variable {Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val)

include hW hS

theorem physicalNewSignIsometry_terminal (x : completedNewSignSpace N hN.1 χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    cover.physicalNewSignIsometry P'.epsilon_pos (by omega : 1≤P'.s+3) χ hχ x=
      (cover.metric P'.epsilon_pos (by omega : 1≤P'.s+3)).change
        (fullTerminalTranslationIsometry A hN.1 P e (completedNewSignFullTerminalEmbedding A hN.1 P χ e x)) := by
  intro P'
  change (cover.metric P'.epsilon_pos (by omega : 1≤P'.s+3)).change
    (completedNewSignWeightedEmbedding N hN.1 P'.epsilon_pos (by omega : 1≤P'.s+3) χ x)=_
  rw [fullTerminalTranslationIsometry_newSign A hN.1 P χ e hW hS x]

theorem physicalNewSignIsometry_source (x : completedNewSignSpace N hN.1 χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    cover.physicalNewSignIsometry P'.epsilon_pos (by omega : 1≤P'.s+3) χ hχ x∈
      RawCommonReconstruction.metricCylinderSource A P e
        (cover.metric P'.epsilon_pos (by omega : 1≤P'.s+3)).change := by
  intro P'
  refine ⟨_,RawCommonReconstruction.cylinderSource_canonical A P e χ hW hS x,?_⟩
  rfl

theorem physicalNewSignIsometry_terminal_packet
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : completedNewSignSpace N hN.1 χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let L := (cover.metric P'.epsilon_pos (by omega : 1≤P'.s+3)).change
    let J := cover.physicalNewSignIsometry P'.epsilon_pos (by omega : 1≤P'.s+3) χ hχ
    similarityOperator L (RawOriginalWindow.extendedTerminalPacket A P e f hc he hr R hR hs) (J x)=
      J (completedNewSignTimePacket N hN.1 χ f (f.smooth ⊤) he hc hr R hR hs x) := by
  intro P' L J
  let U := (fullTerminalTranslationIsometry A hN.1 P e).toContinuousLinearMap
  have hu (y) : U.adjoint (U y)=y := congrArg (fun T => T y)
    (fullTerminalTranslationIsometry A hN.1 P e).adjoint_comp_self
  have hJ (y : completedNewSignSpace N hN.1 χ) :
      J y=L (U (completedNewSignFullTerminalEmbedding A hN.1 P χ e y)) :=
    cover.physicalNewSignIsometry_terminal A P e χ hχ hW hS y
  rw [hJ,hJ]
  change L (U (EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e
    (U.adjoint (L.symm (L (U (completedNewSignFullTerminalEmbedding A hN.1 P χ e x)))))))=_
  rw [ContinuousLinearEquiv.symm_apply_apply,hu,
    completedNewSignFullTerminalEmbedding_packet A hN.1 P χ e hW hS]

#print axioms physicalNewSignIsometry
#print axioms physicalNewSignIsometry_terminal
#print axioms physicalNewSignIsometry_source
#print axioms physicalNewSignIsometry_terminal_packet
end QuantitativeMaass.AdmissibleScalarCover
