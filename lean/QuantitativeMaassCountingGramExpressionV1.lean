module

public import QuantitativeMaassCountingSectorExpressionV1
public import QuantitativeMaassAmbientAdjointExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap AsymptoticFiniteBranch AsymptoticSectorSigns QuantitativeNewGap
open AsymptoticCongruenceStrip
namespace QuantitativeMaass.Counting

attribute [local instance] Classical.propDecidable

theorem normalizerOperator_sector (N : ℕ) (hN : 0<N) (i : SectorSignIndex N) :
    normalizerOperator N (sectorNormalizerGroup N hN i)=
      permutationOperator (sectorNormalizer N hN i) := by
  cases i <;> rfl

theorem frickeOperator_selfAdjoint (N : ℕ) (hN : 0<N) :
    IsSelfAdjoint (normalizerOperator N (completedFrickeNormalizer N hN)) := by
  change IsSelfAdjoint (normalizerOperator N (sectorNormalizerGroup N hN none))
  rw [normalizerOperator_sector]
  exact permutationOperator_selfAdjoint _ (sectorNormalizer_involutive N hN none)

theorem coverTraceOperator_selfAdjoint {M N : ℕ} [NeZero N] (hMN : M∣N) :
    IsSelfAdjoint (coverTraceOperator hMN) := by
  have hc : IsSelfAdjoint (((gamma N).subgroupOf (gamma M)).index:ℂ) := by
    change star (_:ℂ)=_
    simp
  exact hc.smul (isSelfAdjoint_starProjection _)

theorem signFactor_projection (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    signFactor N hN e i=(sectorSignConstraint N hN e i).starProjection := by
  apply ContinuousLinearMap.ext
  intro f
  change signFactor N hN e i f=(permutationSignSpace
    (sectorNormalizer N hN i) (sectorNormalizerSign e i)).starProjection f
  rw [permutationSignSpace_projection _
    (sectorNormalizer_involutive N hN i) _ (sectorNormalizerSign_sq e i)]
  simp only [signFactor,normalizerOperator_sector,smul_apply,add_apply]
  rfl

theorem oldPair_selfAdjoint {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) : IsSelfAdjoint (oldPair hN hMN) := by
  have hB := coverTraceOperator_selfAdjoint hMN
  exact hB.add (ambient_conjugate_selfAdjoint _ _ hB (frickeOperator_selfAdjoint N hN))

theorem simpleNewFilter_selfAdjoint {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) (p m : ℕ) :
    IsSelfAdjoint (simpleNewFilter hN hMN p m) := by
  have hhalf : IsSelfAdjoint (1/2:ℂ) := by change star (1/2:ℂ)=_; simp
  have hc : IsSelfAdjoint (((((p:ℝ)+1)⁻¹:ℝ):ℂ)) := Complex.conj_ofReal _
  have hI : IsSelfAdjoint (1 : Space N→L[ℂ]Space N) := by
    change (1 : _→L[ℂ]_).adjoint=1
    exact ContinuousLinearMap.adjoint_one
  unfold simpleNewFilter
  apply clm_selfAdjoint_pow
  apply clm_selfAdjoint_sub
  · exact hI
  · exact hhalf.smul (hc.smul (oldPair_selfAdjoint hN hMN))

theorem repeatedTwoNewFilter_selfAdjoint {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) :
    IsSelfAdjoint (repeatedTwoNewFilter hN hMN) := by
  let B := coverTraceOperator hMN-1
  let W := normalizerOperator N (completedFrickeNormalizer N hN)
  let U := B+W.comp (B.comp W)
  have hI : IsSelfAdjoint (1 : Space N→L[ℂ]Space N) := by
    change (1 : _→L[ℂ]_).adjoint=1
    exact ContinuousLinearMap.adjoint_one
  have hB : IsSelfAdjoint B := by
    change IsSelfAdjoint (coverTraceOperator hMN-1)
    apply clm_selfAdjoint_sub
    · exact coverTraceOperator_selfAdjoint hMN
    · exact hI
  have hU : IsSelfAdjoint U :=
    hB.add (ambient_conjugate_selfAdjoint _ _ hB (frickeOperator_selfAdjoint N hN))
  have htwo : IsSelfAdjoint (2:ℂ) := by change star (2:ℂ)=_; simp
  have hc : IsSelfAdjoint (1/24:ℂ) := by change star (1/24:ℂ)=_; simp
  exact hc.smul ((clm_selfAdjoint_sub _ _
    (clm_selfAdjoint_sub _ _ (clm_selfAdjoint_pow U hU 4)
      (htwo.smul (clm_selfAdjoint_pow U hU 3))) (clm_selfAdjoint_pow U hU 2)).add (htwo.smul hU))

theorem localNewFilter_selfAdjoint (N : ℕ) [NeZero N] (hN : 0<N)
    (m : ℕ) (p : ↥N.primeFactors) :
    IsSelfAdjoint (localNewFilter N hN m p) := by
  classical
  unfold localNewFilter
  split
  · exact repeatedTwoNewFilter_selfAdjoint hN _
  · exact simpleNewFilter_selfAdjoint hN _ _ _

theorem signFactor_selfAdjoint (N : ℕ) (hN : 0<N)
    (e : Sector N) (i : SectorSignIndex N) :
    IsSelfAdjoint (signFactor N hN e i) := by
  rw [signFactor_projection]
  exact isSelfAdjoint_starProjection _


theorem ambientSectorAdjointExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) :
    Realizes (gamma N) (ambientSectorAdjointExpression N hN e m)
      (sectorNewFilter N hN e m).adjoint := by
  have hs := Realizes.list_prod _ _ (ambientSignFactorExpression_realizes N hN e)
    (Finset.univ : Finset (SectorSignIndex N)).toList.reverse
  have hn := Realizes.list_prod _ _ (ambientLocalNewExpression_realizes N hN m)
    (Finset.univ : Finset ↥N.primeFactors).toList.reverse
  have hh := hs.mul hn
  unfold sectorNewFilter
  rw [adjoint_comp,totalNewFilter,signProduct,
    orderedProduct_adjoint _ (signFactor_selfAdjoint N hN e),
    orderedProduct_adjoint _ (localNewFilter_selfAdjoint N hN m)]
  exact hh

theorem ambientSectorGramExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) :
    Realizes (gamma N) (ambientSectorGramExpression N hN e m)
      ((sectorNewFilter N hN e m).adjoint.comp (sectorNewFilter N hN e m)) :=
  (ambientSectorAdjointExpression_realizes N hN e m).mul
    (ambientSectorNewExpression_realizes N hN e m)

theorem ambientSectorGramExpression_root (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) (x : UpperHalfPlane) :
    (((sectorNewFilter N hN e m).adjoint.comp (sectorNewFilter N hN e m))
      (AsymptoticRegularTrace.delta (AsymptoticNestedQuotients.classOf (gamma N) 1)))
      (AsymptoticNestedQuotients.classOf (gamma N) 1)=
    ((ambientSectorGramExpression N hN e m).map
      (fun b => if b.label∈gamma N then b.coefficient x else 0)).sum :=
  (ambientSectorGramExpression_realizes N hN e m).root_coefficient x

#print axioms normalizerOperator_sector
#print axioms frickeOperator_selfAdjoint
#print axioms coverTraceOperator_selfAdjoint
#print axioms signFactor_projection
#print axioms oldPair_selfAdjoint
#print axioms simpleNewFilter_selfAdjoint
#print axioms repeatedTwoNewFilter_selfAdjoint
#print axioms localNewFilter_selfAdjoint
#print axioms signFactor_selfAdjoint
#print axioms ambientSectorAdjointExpression_realizes
#print axioms ambientSectorGramExpression_realizes
#print axioms ambientSectorGramExpression_root
end QuantitativeMaass.Counting
