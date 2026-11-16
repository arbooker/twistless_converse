module

public import QuantitativeMaassAmbientSectorExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticFiniteBranch AsymptoticSectorSigns QuantitativeNinaMaass QuantitativeNewGap
namespace QuantitativeMaass

/-- Adjoint identities stated directly for bounded Hilbert-space operators. -/
theorem clm_selfAdjoint_sub {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H→L[ℂ]H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A-B) := by
  change (A-B).adjoint=A-B
  rw [map_sub,hA.adjoint_eq,hB.adjoint_eq]

theorem clm_adjoint_pow {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H→L[ℂ]H) (m : ℕ) : (A^m).adjoint=A.adjoint^m := by
  induction m with
  | zero => simp only [pow_zero,adjoint_one]
  | succ m ih =>
    rw [pow_succ' A m,mul_def,adjoint_comp,ih,←mul_def,←pow_succ]

theorem clm_selfAdjoint_pow {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H→L[ℂ]H) (hA : IsSelfAdjoint A) (m : ℕ) : IsSelfAdjoint (A^m) := by
  change (A^m).adjoint=A^m
  rw [clm_adjoint_pow,hA.adjoint_eq]

theorem ambient_cover_trace_selfAdjoint {M N : ℕ} [NeZero N] (hMN : M∣N) :
    IsSelfAdjoint ((levelCover hMN).comp (levelTrace hMN)) := by
  change ((levelCover hMN).comp (levelCover hMN).adjoint).adjoint = _
  rw [adjoint_comp,adjoint_adjoint]
  rfl

theorem ambient_conjugate_selfAdjoint {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A W : H→L[ℂ]H) (hA : IsSelfAdjoint A) (hW : IsSelfAdjoint W) :
    IsSelfAdjoint (W.comp (A.comp W)) := by
  change (W.comp (A.comp W)).adjoint = _
  simp only [adjoint_comp,hA.adjoint_eq,hW.adjoint_eq,comp_assoc]

theorem ambientDivisorOldPair_selfAdjoint {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) : IsSelfAdjoint (ambientDivisorOldPair hN hMN) := by
  have hB := ambient_cover_trace_selfAdjoint hMN
  exact hB.add (ambient_conjugate_selfAdjoint _ _ hB (frickeIsometry_selfAdjoint N hN))

theorem ambientSimpleNewFilter_selfAdjoint {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) (p m : ℕ) :
    IsSelfAdjoint (ambientSimpleNewFilter hN hMN p m) := by
  have hhalf : IsSelfAdjoint (1/2:ℂ) := by change star (1/2:ℂ)=_; simp
  have hc : IsSelfAdjoint (((((p:ℝ)+1)⁻¹:ℝ):ℂ)) := Complex.conj_ofReal _
  have hI : IsSelfAdjoint (1 : AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := by
    change (1 : _→L[ℂ]_).adjoint=1
    exact ContinuousLinearMap.adjoint_one
  unfold ambientSimpleNewFilter
  apply clm_selfAdjoint_pow
  apply clm_selfAdjoint_sub
  · exact hI
  · exact hhalf.smul (hc.smul (ambientDivisorOldPair_selfAdjoint hN hMN))

theorem ambientRepeatedTwoNewFilter_selfAdjoint {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) :
    IsSelfAdjoint (ambientRepeatedTwoNewFilter hN hMN) := by
  let B := (levelCover hMN).comp (levelTrace hMN)-1
  let W := (frickeIsometry N hN).toContinuousLinearMap
  let U := B+W.comp (B.comp W)
  have hI : IsSelfAdjoint (1 : AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := by
    change (1 : _→L[ℂ]_).adjoint=1
    exact ContinuousLinearMap.adjoint_one
  have hB : IsSelfAdjoint B := by
    change IsSelfAdjoint ((levelCover hMN).comp (levelTrace hMN)-1)
    apply clm_selfAdjoint_sub
    · exact ambient_cover_trace_selfAdjoint hMN
    · exact hI
  have hU : IsSelfAdjoint U :=
    hB.add (ambient_conjugate_selfAdjoint _ _ hB (frickeIsometry_selfAdjoint N hN))
  have htwo : IsSelfAdjoint (2:ℂ) := by change star (2:ℂ)=_; simp
  have hc : IsSelfAdjoint (1/24:ℂ) := by change star (1/24:ℂ)=_; simp
  exact hc.smul ((clm_selfAdjoint_sub _ _
    (clm_selfAdjoint_sub _ _ (clm_selfAdjoint_pow U hU 4)
      (htwo.smul (clm_selfAdjoint_pow U hU 3))) (clm_selfAdjoint_pow U hU 2)).add (htwo.smul hU))

theorem ambientLocalNewFilter_selfAdjoint (N : ℕ) [NeZero N] (hN : 0<N)
    (m : ℕ) (p : ↥N.primeFactors) :
    IsSelfAdjoint (ambientAdmissibleLocalNewFilter N hN m p) := by
  classical
  unfold ambientAdmissibleLocalNewFilter
  split
  · exact ambientRepeatedTwoNewFilter_selfAdjoint hN _
  · exact ambientSimpleNewFilter_selfAdjoint hN _ _ _

theorem ambientSignFactor_selfAdjoint (N : ℕ) (hN : 0<N)
    (e : Sector N) (i : SectorSignIndex N) :
    IsSelfAdjoint (ambientSectorSignFactor N hN e i) := by
  rw [ambientSectorSignFactor_projection]
  exact isSelfAdjoint_starProjection _

/-- Reverse the factors when taking the adjoint; the factors need not commute. -/
theorem orderedProduct_adjoint {H I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : I→H→L[ℂ]H) (hA : ∀ i,IsSelfAdjoint (A i)) (L : List I) :
    ((L.map A).prod).adjoint = ((L.reverse.map A).prod) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.prod_cons,List.reverse_cons,List.map_append,
      List.prod_append]
    change ((A i).comp (L.map A).prod).adjoint = _
    rw [adjoint_comp,ih,(hA i).adjoint_eq]
    rfl

/-- A finite rational expression for the adjoint of the actual new/sign filter. -/
def ambientSectorAdjointExpression (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) : Expression :=
  composeExpression
    (orderedProductExpression (ambientSignFactorExpression N hN e)
      (Finset.univ : Finset (SectorSignIndex N)).toList.reverse)
    (orderedProductExpression (ambientLocalNewExpression N hN m)
      (Finset.univ : Finset ↥N.primeFactors).toList.reverse)

theorem ambientSectorAdjointExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) :
    QuotientRealizes N (ambientSectorAdjointExpression N hN e m)
      (ambientSectorNewFilter N hN e m).adjoint := by
  have hs := QuotientRealizes.list_prod _ _ (ambientSignFactorExpression_realizes N hN e)
    (Finset.univ : Finset (SectorSignIndex N)).toList.reverse
  have hn := QuotientRealizes.list_prod _ _ (ambientLocalNewExpression_realizes N hN m)
    (Finset.univ : Finset ↥N.primeFactors).toList.reverse
  have hh := hs.mul hn
  unfold ambientSectorNewFilter
  change QuotientRealizes N _
    ((ambientAdmissibleTotalNewFilter N hN m).comp (ambientSectorSignProduct N hN e)).adjoint
  rw [adjoint_comp,ambientAdmissibleTotalNewFilter,ambientSectorSignProduct,
    orderedProduct_adjoint _ (ambientSignFactor_selfAdjoint N hN e),
    orderedProduct_adjoint _ (ambientLocalNewFilter_selfAdjoint N hN m)]
  exact hh

/-- The Gram operator retains the original factor order and its reversed adjoint. -/
def ambientSectorGramExpression (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) : Expression :=
  composeExpression (ambientSectorAdjointExpression N hN e m)
    (ambientSectorNewExpression N hN e m)

theorem ambientSectorGramExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) :
    QuotientRealizes N (ambientSectorGramExpression N hN e m)
      ((ambientSectorNewFilter N hN e m).adjoint.comp (ambientSectorNewFilter N hN e m)) :=
  (ambientSectorAdjointExpression_realizes N hN e m).mul
    (ambientSectorNewExpression_realizes N hN e m)

#print axioms ambientDivisorOldPair_selfAdjoint
#print axioms ambientSimpleNewFilter_selfAdjoint
#print axioms ambientRepeatedTwoNewFilter_selfAdjoint
#print axioms ambientSectorAdjointExpression_realizes
#print axioms ambientSectorGramExpression_realizes

end QuantitativeMaass
