module

public import QuantitativeMaassFullCanonicalPacketV1
public import QuantitativeMaassRawBothParityIndependentV1
public import QuantitativeMaassMetricSourceColumnCountV1

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNewGap
open ContinuousLinearMap
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN→ℂ) : InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)


/-- The scalar metric applied to the genuine finite-energy terminal packet,
then extended to the cylinder. The unrestricted cylinder wave is not asserted
to be Hilbert--Schmidt. -/
def scalarTerminalPacket
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0) :=
  let U := (fullTerminalTranslationIsometry A hN.1 P e).toContinuousLinearMap
  similarityOperator (admissibleScalarMetric N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)).change
    (U.comp ((EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e).comp U.adjoint))

omit [NeZero N] in
theorem scalarTerminalPacket_summable {ι κ : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε))
    (c : HilbertBasis κ ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    Summable (fun i => ‖scalarTerminalPacket A hN P e f hc he hr R hR hs (c i)‖^2) := by
  have ht := EulerHilbert.FullTerminal.centeredTerminalPacket_summable A hN.1 P f hc he hr R hR hs b e
  have hu := (isometry_extension_energy (fullTerminalTranslationIsometry A hN.1 P e) b c _ ht).1
  exact similarityOperator_summable c _ _ hu

/-- The canonical scalar-metric embedding is exactly the image of the same
terminal reconstruction used for the original solutions. -/
theorem scalarMetricNewSignIsometry_terminal
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val)
    (x : completedNewSignSpace N hN.1 χ) :
    scalarMetricNewSignIsometry N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega) χ hχ x=
      (admissibleScalarMetric N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)).change
        (fullTerminalTranslationIsometry A hN.1 P e
          (completedNewSignFullTerminalEmbedding A hN.1 P χ e x)) := by
  change (admissibleScalarMetric N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)).change
    (completedNewSignWeightedEmbedding N hN.1 (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega) χ x)=_
  rw [fullTerminalTranslationIsometry_newSign A hN.1 P χ e hW hS x]

theorem scalarTerminalPacket_newSign
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : completedNewSignSpace N hN.1 χ) :
    scalarTerminalPacket A hN P e f hc he hr R hR hs
      (scalarMetricNewSignIsometry N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega) χ hχ x)=
      scalarMetricNewSignIsometry N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega) χ hχ
        (completedNewSignTimePacket N hN.1 χ f (f.smooth ⊤) he hc hr R hR hs x) := by
  let U := (fullTerminalTranslationIsometry A hN.1 P e).toContinuousLinearMap
  have hu (y) : U.adjoint (U y)=y := congrArg (fun T => T y)
    (fullTerminalTranslationIsometry A hN.1 P e).adjoint_comp_self
  rw [scalarMetricNewSignIsometry_terminal A hN P e χ hχ hW hS,
    scalarMetricNewSignIsometry_terminal A hN P e χ hχ hW hS]
  change (admissibleScalarMetric N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)).change
    (U (EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e
      (U.adjoint ((admissibleScalarMetric N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)).change.symm
        ((admissibleScalarMetric N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)).change
          (U (completedNewSignFullTerminalEmbedding A hN.1 P χ e x)))))))=_
  rw [ContinuousLinearEquiv.symm_apply_apply,hu,
    completedNewSignFullTerminalEmbedding_packet A hN.1 P χ e hW hS]
  rfl

/-- The same finite-energy operator retains the original scalar packet action
on every original solution datum in the chosen root sector. -/
theorem scalarTerminalPacket_original (σ : ℕ) (t ε : ℝ)
    (p : QuantitativeConcreteGoals.maassWindow N σ t ε)
    (hp : RawOriginalWindow.windowSector A P σ t ε p=e)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    let L := (admissibleScalarMetric N hN (AsymptoticReconstructedCount.parameters A P).epsilon_pos (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega)).change
    let u := fullTerminalTranslationIsometry A hN.1 P e (RawOriginalWindow.windowDatum A P σ t ε p)
    scalarTerminalPacket A hN P e f hc he hr R hR hs (L u)=cosinePacket f p.val.1 • L u := by
  intro L u
  apply similarityOperator_eigen
  let U := (fullTerminalTranslationIsometry A hN.1 P e).toContinuousLinearMap
  have hu (y) : U.adjoint (U y)=y := congrArg (fun T => T y)
    (fullTerminalTranslationIsometry A hN.1 P e).adjoint_comp_self
  have hrp := RawOriginalWindow.windowDatum_realizes A P σ t ε p
  rw [hp] at hrp
  change U (EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e
    (U.adjoint (U (RawOriginalWindow.windowDatum A P σ t ε p))))=_
  rw [hu,EulerHilbert.FullTerminal.centeredTerminalPacket_original A hN.1 P f hc he hr R hR hs e
    p.val.1 σ p.property.2.2 _ hrp,map_smul]
  rfl

#print axioms scalarTerminalPacket_summable
#print axioms scalarMetricNewSignIsometry_terminal
#print axioms scalarTerminalPacket_newSign
#print axioms scalarTerminalPacket_original
end QuantitativeMaass
