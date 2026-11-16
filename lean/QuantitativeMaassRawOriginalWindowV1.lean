module

public import QuantitativeMaassRawOriginalSourceContainsV1
public import QuantitativeMaassRawOriginalTerminalProjectionV1
public import QuantitativeMaassEulerConcreteCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns
open scoped BigOperators ContDiff

namespace QuantitativeMaass.RawOriginalWindow

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  [NeZero N] (P : FinitenessGlobalHeight.Parameters A)

section WindowData

variable (σ : ℕ) (t ε : ℝ)

def windowSector (p : QuantitativeConcreteGoals.maassWindow N σ t ε) : Sector N :=
  (RawCommonReconstruction.original_source_contains A P p.val.1 σ p.property.2.2).choose

def windowDatum (p : QuantitativeConcreteGoals.maassWindow N σ t ε) :
    AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε :=
  (RawCommonReconstruction.original_source_contains A P p.val.1 σ p.property.2.2).choose_spec.choose

theorem windowDatum_realizes (p : QuantitativeConcreteGoals.maassWindow N σ t ε) :
    EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P (windowSector A P σ t ε p) (windowDatum A P σ t ε p)=
      originalWindowClass (NeZero.pos N) A (AsymptoticReconstructedCount.parameters A P) σ t ε p :=
  (RawCommonReconstruction.original_source_contains A P p.val.1 σ p.property.2.2).choose_spec.choose_spec.1

theorem windowDatum_mem (p : QuantitativeConcreteGoals.maassWindow N σ t ε) :
    AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
      (windowDatum A P σ t ε p)∈RawCommonReconstruction.originalSourceKernel A P (windowSector A P σ t ε p) :=
  (RawCommonReconstruction.original_source_contains A P p.val.1 σ p.property.2.2).choose_spec.choose_spec.2

theorem windowDatum_fixed (p : QuantitativeConcreteGoals.maassWindow N σ t ε) :
    RawCommonReconstruction.terminalSourceProjection A P (windowSector A P σ t ε p)
      (windowDatum A P σ t ε p)=windowDatum A P σ t ε p :=
  RawCommonReconstruction.terminalSourceProjection_fixes A P _ _ (windowDatum_mem A P σ t ε p)

/-- The actual normalized data remain independent within each finite root
sector, across different spectral parameters. -/
theorem windowDatum_sector_independent (e : Sector N) :
    LinearIndependent ℂ (fun p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
      windowSector A P σ t ε p=e} => windowDatum A P σ t ε p.val) := by
  apply LinearIndependent.of_comp (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e).toLinearMap
  have he (p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
      windowSector A P σ t ε p=e}) :
      EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e (windowDatum A P σ t ε p.val)=
        originalWindowClass (NeZero.pos N) A (AsymptoticReconstructedCount.parameters A P) σ t ε p.val := by
    simpa only [p.property] using windowDatum_realizes A P σ t ε p.val
  simpa only [Function.comp_def,LinearMap.comp_apply,LinearIsometry.coe_toLinearMap,he] using!
    (originalWindowClass_independent (NeZero.pos N) A (AsymptoticReconstructedCount.parameters A P) σ t ε).comp
      (fun p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
        windowSector A P σ t ε p=e} => p.val) Subtype.val_injective


end WindowData

#print axioms windowDatum_mem
#print axioms windowDatum_realizes
#print axioms windowDatum_fixed
#print axioms windowDatum_sector_independent
end QuantitativeMaass.RawOriginalWindow
