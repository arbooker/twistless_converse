module

public import QuantitativeMaassCanonicalParitySpaceV1
public import QuantitativeMaassCanonicalResidualV1
public import QuantitativeMaassCompletedTerminalMetricV1
public import QuantitativeMaassCompletedTerminalPacketV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticSectorSigns QuantitativeNewGap
open scoped SchwartzMap ContDiff

namespace QuantitativeMaass

def completedNewSignParityTerminalEmbedding {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N) (η : ℝ) :
    completedNewSignParitySpace N hN χ η→L[ℂ]
      terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε :=
  (completedNewSignTerminalEmbedding A hN P χ e).comp
    (completedNewSignParityInclusion N hN χ η).toContinuousLinearMap

theorem completedNewSignParityTerminalEmbedding_lower {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N] :
    ∃ a : ℝ,0<a ∧ ∀ (χ : admissibleGeneratorIndex N hN.1→ℂ) (e : Sector N) (η : ℝ),
      (∀ i,‖χ i‖=1) → χ (frickeGeneratorIndex N hN.1)=sign e.1 →
      (∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val) →
      ∀ x : completedNewSignParitySpace N hN.1 χ η,
        a*‖x‖^2≤‖completedNewSignParityTerminalEmbedding A hN.1 P χ e η x‖^2 := by
  obtain ⟨a,ha,hl⟩ := completedNewSignTerminalEmbedding_lower A hN P
  refine ⟨a,ha,?_⟩
  intro χ e η hχ hW hS x
  exact hl χ e hχ hW hS (completedNewSignParityInclusion N hN.1 χ η x)

theorem completedNewSignParityTerminalEmbedding_packet {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N) (η : ℝ)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : completedNewSignParitySpace N hN χ η) :
    EulerHilbert.Nonzero.centeredTerminalPacket A hN P f hc he hr R hR hs e
      (completedNewSignParityTerminalEmbedding A hN P χ e η x)=
      completedNewSignParityTerminalEmbedding A hN P χ e η
        (completedNewSignParityTimePacket N hN χ η f hc he hr R hR hs x) :=
  completedNewSignTerminalEmbedding_packet A hN P χ e hW hS f hc he hr R hR hs
    (completedNewSignParityInclusion N hN χ η x)

theorem completedNewSignParityTerminalEmbedding_filter {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (e : Sector N) (η : ℝ)
    (hW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    {s : Set UpperHalfPlane} (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ)
    (x : completedNewSignParitySpace N hN χ η) :
    EulerHilbert.Nonzero.residualFilter A hN P e hs qs d
      (completedNewSignParityTerminalEmbedding A hN P χ e η x)=
        completedNewSignParityTerminalEmbedding A hN P χ e η x :=
  completedNewSignTerminalEmbedding_filter A hN P χ e hW hS hs qs d
    (completedNewSignParityInclusion N hN χ η x)

#print axioms completedNewSignParityTerminalEmbedding_lower
#print axioms completedNewSignParityTerminalEmbedding_packet
#print axioms completedNewSignParityTerminalEmbedding_filter

end QuantitativeMaass
