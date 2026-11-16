module

public import QuantitativeMaassDyadicTraceOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeNinaMaass

namespace QuantitativeMaass

/-- The actual closed cuspidal trace-new/sign space, using bounded
normalizer equations on the quotient Hilbert space. -/
def completedNewSignSpace (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) : Submodule ℂ (AutomorphicSpace N) :=
  localCuspidalSpace N hN ⊓ (newSpace N hN ⊓ completedGeneratorSpace N hN χ)

theorem completedNewSignSpace_closed (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    IsClosed (completedNewSignSpace N hN χ : Set (AutomorphicSpace N)) := by
  have hn : IsClosed (newSpace N hN : Set (AutomorphicSpace N)) := by
    simp only [newSpace,newTraceKernel,Submodule.coe_iInf,Submodule.coe_inf]
    exact isClosed_iInter (fun p => (levelTrace (Nat.div_dvd_of_dvd p.property.2)).isClosed_ker.inter
      ((levelTrace (Nat.div_dvd_of_dvd p.property.2)).comp
        (frickeIsometry N hN).toContinuousLinearMap).isClosed_ker)
  exact (localCuspidalSpace_closed N hN).inter (hn.inter (completedGeneratorSpace_closed N hN χ))

instance completedNewSignSpace_complete (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) : CompleteSpace (completedNewSignSpace N hN χ) :=
  (completedNewSignSpace_closed N hN χ).completeSpace_coe

def completedNewSignWeightedEmbedding (N : ℕ) [NeZero N] (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    completedNewSignSpace N hN χ →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (weightedQuotientEmbedding N hε hv).comp (completedNewSignSpace N hN χ).subtypeL

/-- The same positive constant controls every actual new/sign sector,
without a Laplace eigenvalue or any extra metric hypothesis. -/
theorem completedNewSignWeightedEmbedding_lower (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    ∃ a : ℝ,0<a ∧ ∀ χ : admissibleGeneratorIndex N hN.1 → ℂ,(∀ i,‖χ i‖=1) →
      ∀ x : completedNewSignSpace N hN.1 χ,
        a*‖x‖^2≤‖completedNewSignWeightedEmbedding N hN.1 hε hv χ x‖^2 := by
  obtain ⟨a,ha,hl⟩ := completedGeneratorSpace_energy_lower N hN hε hv
  refine ⟨a,ha,?_⟩
  intro χ hχ x
  exact hl χ hχ ⟨x.val,x.property.2.2⟩

theorem completedNewSignWeightedEmbedding_closed (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (hχ : ∀ i,‖χ i‖=1) :
    Function.Injective (completedNewSignWeightedEmbedding N hN.1 hε hv χ) ∧
      IsClosed (Set.range (completedNewSignWeightedEmbedding N hN.1 hε hv χ)) := by
  obtain ⟨a,ha,hl⟩ := completedNewSignWeightedEmbedding_lower N hN hε hv
  apply lower_energy_injective_closed
    (H := completedNewSignSpace N hN.1 χ) (K := Lp ℂ 2 (quotientMeasure 0))
    (completedNewSignWeightedEmbedding N hN.1 hε hv χ) ha
  intro x
  exact hl χ hχ x

/-- Concrete continuous linear equivalence from the canonical new/sign
space onto its closed weighted range. -/
def completedNewSignWeightedEquiv (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (hχ : ∀ i,‖χ i‖=1) :
    completedNewSignSpace N hN.1 χ ≃L[ℂ] (completedNewSignWeightedEmbedding N hN.1 hε hv χ).range :=
  ContinuousLinearMap.equivRange
    (E := completedNewSignSpace N hN.1 χ) (F := Lp ℂ 2 (quotientMeasure 0))
    (f := completedNewSignWeightedEmbedding N hN.1 hε hv χ)
    (completedNewSignWeightedEmbedding_closed N hN hε hv χ hχ).1
    (completedNewSignWeightedEmbedding_closed N hN hε hv χ hχ).2

theorem completedNewSignWeightedEquiv_apply (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (hχ : ∀ i,‖χ i‖=1)
    (x : completedNewSignSpace N hN.1 χ) :
    (completedNewSignWeightedEquiv N hN hε hv χ hχ x : Lp ℂ 2 (quotientMeasure 0))=
      weightedQuotientEmbedding N hε hv x.val := rfl

#print axioms completedNewSignSpace_closed
#print axioms completedNewSignWeightedEmbedding_lower
#print axioms completedNewSignWeightedEmbedding_closed
#print axioms completedNewSignWeightedEquiv
#print axioms completedNewSignWeightedEquiv_apply

end QuantitativeMaass
