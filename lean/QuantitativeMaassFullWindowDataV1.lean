module

public import QuantitativeMaassFullResidualFilterV1
public import QuantitativeMaassEulerConcreteCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns
open scoped BigOperators ContDiff

namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

section WindowData

variable (σ : ℕ) (t ε : ℝ)

def windowSector (p : QuantitativeConcreteGoals.maassWindow N σ t ε) : Sector N :=
  (original_all_filters A hN P p.val.1 σ p.property.2.2).choose

def windowDatum (p : QuantitativeConcreteGoals.maassWindow N σ t ε) :
    AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε :=
  (original_all_filters A hN P p.val.1 σ p.property.2.2).choose_spec.choose

theorem windowDatum_realizes (p : QuantitativeConcreteGoals.maassWindow N σ t ε) :
    physicalIsometry A hN P (windowSector A hN P σ t ε p) (windowDatum A hN P σ t ε p)=
      originalWindowClass hN A (AsymptoticReconstructedCount.parameters A P) σ t ε p :=
  (original_all_filters A hN P p.val.1 σ p.property.2.2).choose_spec.choose_spec.1

theorem windowDatum_fixed (p : QuantitativeConcreteGoals.maassWindow N σ t ε)
    (s : Set UpperHalfPlane) (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    commonResidualFilter A hN P (windowSector A hN P σ t ε p) hs qs d
      (windowDatum A hN P σ t ε p)=windowDatum A hN P σ t ε p :=
  (original_all_filters A hN P p.val.1 σ p.property.2.2).choose_spec.choose_spec.2 s hs qs d

/-- The actual normalized data remain independent within each finite root
sector, across different spectral parameters. -/
theorem windowDatum_sector_independent (e : Sector N) :
    LinearIndependent ℂ (fun p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
      windowSector A hN P σ t ε p=e} => windowDatum A hN P σ t ε p.val) := by
  apply LinearIndependent.of_comp (physicalIsometry A hN P e).toLinearMap
  have he (p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
      windowSector A hN P σ t ε p=e}) :
      physicalIsometry A hN P e (windowDatum A hN P σ t ε p.val)=
        originalWindowClass hN A (AsymptoticReconstructedCount.parameters A P) σ t ε p.val := by
    simpa only [p.property] using windowDatum_realizes A hN P σ t ε p.val
  simpa only [Function.comp_def,LinearMap.comp_apply,LinearIsometry.coe_toLinearMap,he] using!
    (originalWindowClass_independent hN A (AsymptoticReconstructedCount.parameters A P) σ t ε).comp
      (fun p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
        windowSector A hN P σ t ε p=e} => p.val) Subtype.val_injective


end WindowData

#print axioms windowDatum_realizes
#print axioms windowDatum_fixed
#print axioms windowDatum_sector_independent
end QuantitativeMaass.EulerHilbert.FullTerminal
