module

public import QuantitativeMaassCompletedTerminalEmbeddingV1
public import QuantitativeMaassCompletedNewSignMetricV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticSectorSigns QuantitativeNewGap

namespace QuantitativeMaass

theorem completedNewSignTerminalEmbedding_lower {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N] :
    ∃ a : ℝ,0<a ∧ ∀ (χ : admissibleGeneratorIndex N hN.1 → ℂ) (e : Sector N),
      (∀ i,‖χ i‖=1) → χ (frickeGeneratorIndex N hN.1)=sign e.1 →
      (∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val) →
      ∀ x : completedNewSignSpace N hN.1 χ,
        a*‖x‖^2≤‖completedNewSignTerminalEmbedding A hN.1 P χ e x‖^2 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  obtain ⟨a,ha,hl⟩ := completedNewSignWeightedEmbedding_lower N hN P'.epsilon_pos
    (show 1≤P'.s+3 by omega)
  refine ⟨a,ha,?_⟩
  intro χ e hχ hw hs x
  rw [completedNewSignTerminalEmbedding_norm A hN.1 P χ e hw hs]
  exact hl χ hχ x

theorem completedNewSignTerminalEmbedding_closed {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (e : Sector N) (hχ : ∀ i,‖χ i‖=1)
    (hχW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val) :
    Function.Injective (completedNewSignTerminalEmbedding A hN.1 P χ e) ∧
      IsClosed (Set.range (completedNewSignTerminalEmbedding A hN.1 P χ e)) := by
  obtain ⟨a,ha,hl⟩ := completedNewSignTerminalEmbedding_lower A hN P
  apply lower_energy_injective_closed
    (H := completedNewSignSpace N hN.1 χ)
    (K := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)
    (completedNewSignTerminalEmbedding A hN.1 P χ e) ha
  intro x
  exact hl χ e hχ hχW hχS x

/-- A proved metric change on the actual counting Hilbert space restores
the canonical new/sign norm exactly. -/
theorem exists_completedNewSignTerminalMetric {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (e : Sector N) (hχ : ∀ i,‖χ i‖=1)
    (hχW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val) :
    ∃ L : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε ≃L[ℂ]
        terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε,
      ∀ x : completedNewSignSpace N hN.1 χ,
        ‖L (completedNewSignTerminalEmbedding A hN.1 P χ e x)‖=‖x‖ := by
  obtain ⟨a,ha,hl⟩ := completedNewSignTerminalEmbedding_lower A hN P
  apply exists_targetMetric_of_lower_bound
    (H := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)
    (V := completedNewSignSpace N hN.1 χ)
    (completedNewSignTerminalEmbedding A hN.1 P χ e) ha
  intro x
  exact hl χ e hχ hχW hχS x

#print axioms completedNewSignTerminalEmbedding_lower
#print axioms completedNewSignTerminalEmbedding_closed
#print axioms exists_completedNewSignTerminalMetric

end QuantitativeMaass
