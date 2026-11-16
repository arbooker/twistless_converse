module

public import QuantitativeMaassCountingNormalizedSourceV1
public import QuantitativeMaassScalarMetricRegularV1
public import QuantitativeMaassJointScalarCoverV1
public import QuantitativeMaassMetricImageFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Matrix
open scoped MatrixGroups
open UpperHalfPlane ContinuousLinearMap AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticCongruenceWeight AsymptoticSectorSigns QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
namespace QuantitativeMaass

section General
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace V] [CompleteSpace H] in
theorem metric_intertwined_range (R : V→L[ℂ]H) (I : V→ₗᵢ[ℂ]H) (L : H≃L[ℂ]H)
    (h : ∀ v,L (R v)=I v) : R.range=I.toLinearMap.range.map L.symm.toLinearMap := by
  ext w
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨I v,⟨v,rfl⟩,by change L.symm (I v)=R v; rw [←h v,L.symm_apply_apply]⟩
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨v,by change R v=L.symm (I v); rw [←h v,L.symm_apply_apply]⟩

omit [CompleteSpace H] in
theorem metric_intertwined_closed (R : V→L[ℂ]H) (I : V→ₗᵢ[ℂ]H) (L : H≃L[ℂ]H)
    (h : ∀ v,L (R v)=I v) : IsClosed (R.range:Set H) := by
  rw [metric_intertwined_range R I L h]
  exact metric_image_closed L.symm _ I.isometry.isClosedEmbedding.isClosed_range

omit [CompleteSpace V] [CompleteSpace H] in
theorem metric_intertwined_image (R : V→L[ℂ]H) (I : V→ₗᵢ[ℂ]H) (L : H≃L[ℂ]H)
    (h : ∀ v,L (R v)=I v) : R.range.map L.toLinearMap=I.toLinearMap.range := by
  ext w
  constructor
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨v,(h v).symm⟩
  · rintro ⟨v,rfl⟩
    exact ⟨R v,⟨v,rfl⟩,h v⟩
end General

local instance (N : ℕ) [NeZero N] : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _
namespace AdmissibleScalarCover
variable {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (C : AdmissibleScalarCover N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)

def regularCapEmbedding (_C : AdmissibleScalarCover N hN) (e : Sector N) (z : ℍ) : countingSectorSpace N hN.1 e→L[ℂ]Space :=
  (CountingMetric.countingCapLift N hδ hν z).comp (countingSectorSpace N hN.1 e).subtypeL

def regularIsometry (e : Sector N) (z : ℍ) : countingSectorSpace N hN.1 e→ₗᵢ[ℂ]Space :=
  CountingMetric.regularMetricSectorIsometry N C.family hδ C.height_pos hν C.covers hN C.member e z

theorem regular_metric_cap (e : Sector N) (z : ℍ) (f : countingSectorSpace N hN.1 e) :
    (C.metric hδ hν).regularChange z (C.regularCapEmbedding hδ hν e z f)=C.regularIsometry hδ hν e z f := by
  apply lp.ext
  funext a
  rw [ScalarCylinderMetric.regularChange_apply]
  change ((normalizerCoverMetric N C.family δ ν (a • z):ℝ):ℂ)*
    (amplitude N δ ν (a • z)*(((Real.sqrt (weight N δ ν (a • z)):ℝ):ℂ)*f.val (classOf (gamma N) a)))=
    amplitude N δ ν (a • z)*
      (((Real.sqrt (weight N δ ν (a • z))*normalizerCoverMetric N C.family δ ν (a • z):ℝ):ℂ)*f.val (classOf (gamma N) a))
  push_cast
  ring

def regularCapSpace (e : Sector N) (z : ℍ) : Submodule ℂ Space :=
  (C.regularCapEmbedding hδ hν e z).range

theorem regularCapSpace_closed (e : Sector N) (z : ℍ) :
    IsClosed (C.regularCapSpace hδ hν e z:Set Space) :=
  metric_intertwined_closed _ (C.regularIsometry hδ hν e z) ((C.metric hδ hν).regularChange z)
    (C.regular_metric_cap hδ hν e z)

instance regularCapSpace_complete (e : Sector N) (z : ℍ) :
    CompleteSpace (C.regularCapSpace hδ hν e z) :=
  (C.regularCapSpace_closed hδ hν e z).completeSpace_coe

theorem regularCapSpace_metric_image (e : Sector N) (z : ℍ) :
    (C.regularCapSpace hδ hν e z).map ((C.metric hδ hν).regularChange z).toLinearMap=
      (C.regularIsometry hδ hν e z).toLinearMap.range :=
  metric_intertwined_image _ _ _ (C.regular_metric_cap hδ hν e z)

#print axioms regular_metric_cap
#print axioms regularCapSpace_closed
#print axioms regularCapSpace_metric_image
end AdmissibleScalarCover
end QuantitativeMaass
