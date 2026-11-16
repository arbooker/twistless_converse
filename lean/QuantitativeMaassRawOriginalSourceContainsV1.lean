module

public import QuantitativeMaassRawOriginalSourceKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- Every original Euler solution has one coherent normalized terminal datum
in the closed source kernel. No spectral or automorphy assumption is added. -/
theorem original_source_contains (r : ℝ) (σ : ℕ) {b : ℕ→ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e g=
        principalEulerWeightedLp (NeZero.pos N) A (AsymptoticReconstructedCount.parameters A P) r σ hb ∧
      AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε g∈
        originalSourceKernel A P e := by
  obtain ⟨e,g,hg,hrows⟩ := EulerHilbert.FullTerminal.original_all_observation_rows A (NeZero.pos N) P r σ hb
  refine ⟨e,g,hg,terminal_unit_ambient A P g,?_⟩
  intro row s hs
  change AsymptoticFiniteBranch.holomorphicSum _ 0
    (physicalExact A P (NeZero.pos N) e
      (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε g))=0
  rw [physicalExact_ambient_terminal]
  exact hrows row s hs

#print axioms original_source_contains
end QuantitativeMaass.RawCommonReconstruction
