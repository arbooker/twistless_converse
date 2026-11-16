module

public import QuantitativeMaassScalarTerminalPacketV1
public import QuantitativeMaassFullExcessColumnV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory ContinuousLinearMap AsymptoticSectorSigns AsymptoticClassicalPetersson
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass.RawCommonReconstruction

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)

/-- The all-row cylinder source lies in the actual terminal reconstruction
range, so its orthogonal range projection is the identity on this source. -/
theorem cylinderSource_in_terminal_range
    (x : Lp ℂ 2 (quotientMeasure 0)) (hx : x∈cylinderSource A P e) :
    let U := (fullTerminalTranslationIsometry A (NeZero.pos N) P e).toContinuousLinearMap
    U (U.adjoint x)=x := by
  intro U
  rcases hx with ⟨y,rfl⟩
  have hu (z) : U.adjoint (U z)=z := congrArg (fun T => T z)
    (fullTerminalTranslationIsometry A (NeZero.pos N) P e).adjoint_comp_self
  change U (U.adjoint (U (terminalSourceProjection A P e (U.adjoint y))))=
    U (terminalSourceProjection A P e (U.adjoint y))
  rw [hu]

/-- The extended finite terminal packet factors through the actual centered
columns on every vector in the all-row original source. -/
theorem cylinderSource_terminal_column_factor
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : Lp ℂ 2 (quotientMeasure 0)) (hx : x∈cylinderSource A P e) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := (fullTerminalTranslationIsometry A (NeZero.pos N) P e).toContinuousLinearMap
    U (EulerHilbert.FullTerminal.centeredTerminalPacket A (NeZero.pos N) P f hc he hr R hR hs e
      (U.adjoint x))=
      U (fullTerminalColumnOutput A (NeZero.pos N) P e
        (finiteEnergyColumnOperator (volume.restrict (AsymptoticCertificateOperators.highStrip P'.ε))
          (cylinderCenteredCappedColumn f hc he R hR hs P'.ε (P'.s+3))
          (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs P'.ε (P'.s+3) P'.ε P'.epsilon_pos) x)) := by
  intro P' U
  have hu := cylinderSource_in_terminal_range A P e x hx
  change U (fullTerminalColumnOutput A (NeZero.pos N) P e
    (finiteEnergyColumnOperator (volume.restrict (AsymptoticCertificateOperators.highStrip P'.ε))
      (cylinderCenteredCappedColumn f hc he R hR hs P'.ε (P'.s+3))
      (cylinderCenteredCappedColumn_memLp f hc he hr R hR hs P'.ε (P'.s+3) P'.ε P'.epsilon_pos)
      (U (U.adjoint x))))=_
  rw [hu]

#print axioms cylinderSource_in_terminal_range
#print axioms cylinderSource_terminal_column_factor
end QuantitativeMaass.RawCommonReconstruction
