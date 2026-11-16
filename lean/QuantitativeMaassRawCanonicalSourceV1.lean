module

public import QuantitativeMaassCanonicalRamifiedResidualV1
public import QuantitativeMaassRawOriginalSourceKernelV1
public import QuantitativeMaassFullCanonicalResidualV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeNewGap
open AsymptoticFiniteBranch AsymptoticCompactObservationCount
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (χ : admissibleGeneratorIndex N (NeZero.pos N)→ℂ) (e : Sector N)
    (hW : χ (frickeGeneratorIndex N (NeZero.pos N))=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N (NeZero.pos N) p)= -delta e p.val)

include hW hS

/-- The canonical completed new/sign image satisfies every original row,
including ramified rows obtained from newness by continuous approximation. -/
theorem canonical_original_rows (x : completedNewSignSpace N (NeZero.pos N) χ)
    (row : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s) :
    holomorphicSum (rowExpression (NeZero.pos N) row e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3)) 0
      (EulerHilbert.FullTerminal.physicalIsometry A (NeZero.pos N) P e
        (completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x))=0 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hrow : rowOperator (NeZero.pos N) row e hs P'.epsilon_pos (P'.s+3) 0
      (EulerHilbert.normalized A (NeZero.pos N) P e
        (completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x))=0 := by
    rw [completedNewSignFullTerminalEmbedding_normalized A (NeZero.pos N) P χ e hW hS]
    cases row with
    | twist q hq =>
      exact completedNewSign_weighted_residual N (NeZero.pos N) χ e hW hS
        P'.epsilon_pos (by omega : 1≤P'.s+3) q hq hs x.val x.property
    | ramified p hp hpN =>
      exact completedNewSign_weighted_ramified_residual N (NeZero.pos N) χ e hW hS
        P'.epsilon_pos (by omega : 1≤P'.s+3) p hp hpN hs x.val x.property
  exact (congrArg (fun T => T (EulerHilbert.normalized A (NeZero.pos N) P e
    (completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x)))
    (cylinder_rowExpression (NeZero.pos N) row e hs P'.epsilon_pos (P'.s+3) 0)).trans hrow

theorem canonical_source_mem (x : completedNewSignSpace N (NeZero.pos N) χ) :
    AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
      (completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x)∈originalSourceKernel A P e := by
  refine ⟨terminal_unit_ambient A P _,?_⟩
  intro row s hs
  change holomorphicSum _ 0 (physicalExact A P (NeZero.pos N) e
    (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
      (completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x)))=0
  rw [physicalExact_ambient_terminal]
  exact canonical_original_rows A P χ e hW hS x row hs

theorem originalSourceProjection_canonical (x : completedNewSignSpace N (NeZero.pos N) χ) :
    originalSourceProjection A P e
      (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
        (completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x))=
      AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
        (completedNewSignFullTerminalEmbedding A (NeZero.pos N) P χ e x) :=
  Submodule.starProjection_eq_self_iff.mpr (canonical_source_mem A P χ e hW hS x)

#print axioms canonical_original_rows
#print axioms canonical_source_mem
#print axioms originalSourceProjection_canonical
end QuantitativeMaass.RawCommonReconstruction
