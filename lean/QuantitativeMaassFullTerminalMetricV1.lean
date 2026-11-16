module

public import QuantitativeMaassFullTerminalEmbeddingV1
public import QuantitativeMaassCompletedNewSignMetricV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticSectorSigns QuantitativeNewGap

namespace QuantitativeMaass

theorem completedNewSignFullTerminalEmbedding_lower {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N] :
    ∃ a : ℝ,0<a ∧ ∀ (χ : admissibleGeneratorIndex N hN.1 → ℂ) (e : Sector N),
      (∀ i,‖χ i‖=1) → χ (frickeGeneratorIndex N hN.1)=sign e.1 →
      (∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val) →
      ∀ x : completedNewSignSpace N hN.1 χ,
        a*‖x‖^2≤‖completedNewSignFullTerminalEmbedding A hN.1 P χ e x‖^2 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  obtain ⟨a,ha,hl⟩ := completedNewSignWeightedEmbedding_lower N hN P'.epsilon_pos
    (show 1≤P'.s+3 by omega)
  refine ⟨a,ha,?_⟩
  intro χ e hχ hw hs x
  rw [completedNewSignFullTerminalEmbedding_norm A hN.1 P χ e hw hs]
  exact hl χ hχ x

theorem completedNewSignFullTerminalEmbedding_closed {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (e : Sector N) (hχ : ∀ i,‖χ i‖=1)
    (hχW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val) :
    Function.Injective (completedNewSignFullTerminalEmbedding A hN.1 P χ e) ∧
      IsClosed (Set.range (completedNewSignFullTerminalEmbedding A hN.1 P χ e)) := by
  obtain ⟨a,ha,hl⟩ := completedNewSignFullTerminalEmbedding_lower A hN P
  apply lower_energy_injective_closed
    (H := completedNewSignSpace N hN.1 χ)
    (K := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (completedNewSignFullTerminalEmbedding A hN.1 P χ e) ha
  intro x
  exact hl χ e hχ hχW hχS x

/-- A proved metric change on the actual counting Hilbert space restores
the canonical new/sign norm exactly. -/
theorem exists_completedNewSignFullTerminalMetric {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (e : Sector N) (hχ : ∀ i,‖χ i‖=1)
    (hχW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val) :
    ∃ L : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε ≃L[ℂ]
        AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε,
      ∀ x : completedNewSignSpace N hN.1 χ,
        ‖L (completedNewSignFullTerminalEmbedding A hN.1 P χ e x)‖=‖x‖ := by
  obtain ⟨a,ha,hl⟩ := completedNewSignFullTerminalEmbedding_lower A hN P
  apply exists_targetMetric_of_lower_bound
    (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (V := completedNewSignSpace N hN.1 χ)
    (completedNewSignFullTerminalEmbedding A hN.1 P χ e) ha
  intro x
  exact hl χ e hχ hχW hχS x

#print axioms completedNewSignFullTerminalEmbedding_lower
#print axioms completedNewSignFullTerminalEmbedding_closed
#print axioms exists_completedNewSignFullTerminalMetric

end QuantitativeMaass
