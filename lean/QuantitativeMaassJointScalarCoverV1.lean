module

public import QuantitativeMaassRegularCanonicalProjectionV1
public import QuantitativeMaassAdmissibleScalarMetricV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane Matrix AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped MatrixGroups ENNReal
namespace QuantitativeMaass

/-- The same concrete finite cover is retained for both physical and regular
metric constructions, rather than forgotten behind a physical-only choice. -/
structure AdmissibleScalarCover (N : ℕ) (hN : GridAdmissibleGap.Admissible N) where
  family : (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)→quotientNormalizerGroup N
  member : ∀ i,(family i).val∈admissibleNormalizerGroup N hN.1
  height : ℝ
  height_pos : 0<height
  covers : ∀ z : ℍ,∃ i,∃ a : gamma N,height≤(a.val • ((family i).val • z)).im

theorem admissibleScalarCover_nonempty (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    Nonempty (AdmissibleScalarCover N hN) := by
  obtain ⟨g,hg,hc,hci,Y,hY,hcover⟩ := admissible_generator_height_cover N hN
  exact ⟨⟨(fun i => ⟨g i,normalizer_mem_of_conjugations N (g i) (hc i) (hci i)⟩),
    hg,Y,hY,hcover⟩⟩

def jointScalarCover (N : ℕ) (hN : GridAdmissibleGap.Admissible N) : AdmissibleScalarCover N hN :=
  Classical.choice (admissibleScalarCover_nonempty N hN)

local instance (N : ℕ) [NeZero N] : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
  Fintype.ofFinite _

namespace AdmissibleScalarCover
variable {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (C : AdmissibleScalarCover N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

def metric : ScalarCylinderMetric N :=
  normalizerCoverScalarMetric N C.family hδ C.height_pos hν C.covers

/-- The chosen concrete cover has the physical norm identity already used
in the coefficient-one original counting argument. -/
theorem physical_norm (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (x : completedGeneratorSpace N hN.1 χ) :
    ‖(C.metric hδ hν).change (weightedQuotientEmbedding N hδ hν x.val)‖=‖x‖ := by
  apply normalizerCoverMetric_completed_norm N C.family hδ C.height_pos hν C.covers x.val
  intro i
  have hsub : admissibleNormalizerGroup N hN.1≤
      (normalizerEigenStabilizer N x.val).map (quotientNormalizerGroup N).subtype := by
    rw [admissibleNormalizerGroup,Subgroup.closure_le]
    intro a ha
    refine ⟨admissibleGeneratorLift N hN.1 ⟨a,ha⟩,?_,rfl⟩
    exact ⟨χ ⟨a,ha⟩,hχ ⟨a,ha⟩,x.property ⟨a,ha⟩⟩
  obtain ⟨a,ha,he⟩ := hsub (C.member i)
  have heq : a=C.family i := Subtype.ext he
  exact heq ▸ ha

def regularProjection (e : AsymptoticSectorSigns.Sector N) (z : ℍ) :=
  CountingMetric.regularCanonicalProjection N C.family hδ C.height_pos hν C.covers hN e z

theorem regularProjection_isProjection (e : AsymptoticSectorSigns.Sector N) (z : ℍ) :
    IsStarProjection (C.regularProjection hδ hν e z) :=
  CountingMetric.regularCanonicalProjection_isProjection N C.family hδ C.height_pos hν C.covers hN C.member e z

/-- The very same scalar metric has the exact finite incidence trace in
the regular model. This specification can safely be used after choosing it. -/
theorem regularProjection_trace (e : AsymptoticSectorSigns.Sector N) :
    AsymptoticRegularTrace.trace MeasureTheory.volume (C.regularProjection hδ hν e)=
      AsymptoticRegularTrace.trace MeasureTheory.volume
        (fun z => (AsymptoticQuotientIncidence.space N hN.1 hδ hν e z).starProjection) :=
  CountingMetric.regularCanonicalProjection_trace N C.family hδ C.height_pos hν C.covers hN e

theorem regularProjection_trace_finite (e : AsymptoticSectorSigns.Sector N) :
    AsymptoticRegularTrace.trace MeasureTheory.volume (C.regularProjection hδ hν e)<∞ :=
  CountingMetric.regularCanonicalProjection_trace_finite N C.family hδ C.height_pos hν C.covers hN e

#print axioms physical_norm
#print axioms regularProjection_isProjection
#print axioms regularProjection_trace
#print axioms regularProjection_trace_finite
end AdmissibleScalarCover
#print axioms admissibleScalarCover_nonempty
end QuantitativeMaass
