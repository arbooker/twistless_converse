module

public import QuantitativeMaassRawOriginalProjectionStructureV1
public import QuantitativeMaassRawOriginalWindowOrthogonalV1
public import QuantitativeMaassScalarMetricProjectionV1
public import QuantitativeMaassMetricImageFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticClassicalPetersson MeasureTheory ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeNewGap
namespace QuantitativeMaass

/-- An isometric image of an orthogonal projection is again an orthogonal
projection on the ambient space, even when the isometry is not onto. -/
theorem isometric_projection_conjugate {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : V→ₗᵢ[ℂ]H) (F : V→L[ℂ]V) (hF : IsStarProjection F) :
    IsStarProjection (J.toContinuousLinearMap.comp (F.comp J.toContinuousLinearMap.adjoint)) := by
  let U := J.toContinuousLinearMap
  have hg : U.adjoint.comp U=1 := J.adjoint_comp_self
  have hi : F.comp F=F := hF.isIdempotentElem.eq
  constructor
  · change (U.comp (F.comp U.adjoint)).comp (U.comp (F.comp U.adjoint))=U.comp (F.comp U.adjoint)
    calc
      _ = U.comp (F.comp ((U.adjoint.comp U).comp (F.comp U.adjoint))) := by simp only [comp_assoc]
      _ = U.comp ((F.comp F).comp U.adjoint) := by rw [hg];rfl
      _ = _ := by rw [hi]
  · change (U.comp (F.comp U.adjoint)).adjoint=U.comp (F.comp U.adjoint)
    simp only [adjoint_comp,adjoint_adjoint,hF.isSelfAdjoint.adjoint_eq,comp_assoc]

namespace RawCommonReconstruction
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

/-- All-row original source in the actual quotient-cylinder coordinates. -/
def cylinderSourceProjection : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0) :=
  let U := (fullTerminalTranslationIsometry A (NeZero.pos N) P e).toContinuousLinearMap
  U.comp ((terminalSourceProjection A P e).comp U.adjoint)

theorem cylinderSourceProjection_isProjection : IsStarProjection (cylinderSourceProjection A P e) :=
  isometric_projection_conjugate (fullTerminalTranslationIsometry A (NeZero.pos N) P e)
    (terminalSourceProjection A P e)
    ⟨terminalSourceProjection_idempotent A P e,terminalSourceProjection_selfAdjoint A P e⟩

def cylinderSource : Submodule ℂ (Lp ℂ 2 (quotientMeasure 0)) := (cylinderSourceProjection A P e).range

instance cylinderSource_complete : CompleteSpace (cylinderSource A P e) :=
  (cylinderSourceProjection_isProjection A P e).isIdempotentElem.isClosed_range.completeSpace_coe

theorem cylinderSourceProjection_eq : cylinderSourceProjection A P e=(cylinderSource A P e).starProjection := by
  exact (isStarProjection_iff_eq_starProjection_range.mp
    (cylinderSourceProjection_isProjection A P e)).choose_spec

theorem cylinderSourceProjection_image
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hg : terminalSourceProjection A P e g=g) :
    cylinderSourceProjection A P e (fullTerminalTranslationIsometry A (NeZero.pos N) P e g)=
      fullTerminalTranslationIsometry A (NeZero.pos N) P e g := by
  let U := (fullTerminalTranslationIsometry A (NeZero.pos N) P e).toContinuousLinearMap
  have hh := congrArg (fun T => T g) (fullTerminalTranslationIsometry A (NeZero.pos N) P e).adjoint_comp_self
  change U.adjoint (U g)=g at hh
  change U (terminalSourceProjection A P e (U.adjoint (U g)))=U g
  rw [hh,hg]

theorem cylinderSource_canonical
    (χ : admissibleGeneratorIndex N (NeZero.pos N)→ℂ)
    (hW : χ (frickeGeneratorIndex N (NeZero.pos N))=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N (NeZero.pos N) p)= -delta e p.val)
    (x : completedNewSignSpace N (NeZero.pos N) χ) :
    completedNewSignWeightedEmbedding N (NeZero.pos N)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      (show 1≤(AsymptoticReconstructedCount.parameters A P).s+3 by omega) χ x∈cylinderSource A P e := by
  rw [←fullTerminalTranslationIsometry_newSign A (NeZero.pos N) P χ e hW hS x]
  exact ⟨_,cylinderSourceProjection_image A P e _
    (raw_terminalSourceProjection_canonical A P χ e hW hS x)⟩

theorem cylinderSource_original (σ : ℕ) (t ε : ℝ)
    (p : QuantitativeConcreteGoals.maassWindow N σ t ε)
    (hp : RawOriginalWindow.windowSector A P σ t ε p=e) :
    fullTerminalTranslationIsometry A (NeZero.pos N) P e
      (RawOriginalWindow.windowDatum A P σ t ε p)∈cylinderSource A P e := by
  refine ⟨_,cylinderSourceProjection_image A P e _ ?_⟩
  simpa only [hp] using RawOriginalWindow.windowDatum_fixed A P σ t ε p

/-- The metric image is closed; the source is not assumed to be isometric
under this scalar multiplier. -/
def metricCylinderSource (L : Lp ℂ 2 (quotientMeasure 0)≃L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    Submodule ℂ (Lp ℂ 2 (quotientMeasure 0)) := (cylinderSource A P e).map L.toLinearMap

instance metricCylinderSource_complete
    (L : Lp ℂ 2 (quotientMeasure 0)≃L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    CompleteSpace (metricCylinderSource A P e L) :=
  (metric_image_closed L (cylinderSource A P e)
    (cylinderSourceProjection_isProjection A P e).isIdempotentElem.isClosed_range).completeSpace_coe

theorem metricCylinderSource_canonical (hN : GridAdmissibleGap.Admissible N)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (hW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val)
    (x : completedNewSignSpace N hN.1 χ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    scalarMetricNewSignIsometry N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ hχ x∈
      metricCylinderSource A P e
        (admissibleScalarMetric N hN P'.epsilon_pos (show 1≤P'.s+3 by omega)).change := by
  refine ⟨_,cylinderSource_canonical A P e χ hW hS x,?_⟩
  rfl

#print axioms cylinderSourceProjection_isProjection
#print axioms cylinderSourceProjection_eq
#print axioms cylinderSource_canonical
#print axioms cylinderSource_original
#print axioms metricCylinderSource_complete
#print axioms metricCylinderSource_canonical
end RawCommonReconstruction
#print axioms isometric_projection_conjugate
end QuantitativeMaass
