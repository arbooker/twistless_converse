module

public import QuantitativeMaassNonzeroTerminalPacketV1
public import QuantitativeMaassNonzeroWindowCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns
open scoped SchwartzMap ContDiff

namespace QuantitativeMaass.EulerHilbert.Nonzero

/-- Actual original-window counting from the constructed centered terminal
packet. Square summability and spectral action are discharged; the only
packet input is the explicit scalar lower bound on the requested interval. -/
theorem originalWindow_count_terminal_packet {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε))
    (σ : ℕ) (t ε : ℝ)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hlower : ∀ r∈Icc t (t+ε),1≤(cosinePacket f r).re) :
    (QuantitativeConcreteGoals.maassWindow N σ t ε).Finite ∧
      ((QuantitativeConcreteGoals.maassWindow N σ t ε).ncard : ℝ) ≤
        ∑ e : Sector N,hilbertSchmidtEnergy basis
          (centeredTerminalPacket A hN P f hc he hr R hR hs e) := by
  classical
  let W := QuantitativeConcreteGoals.maassWindow N σ t ε
  let sector : W → Sector N := windowSector A hN P σ t ε
  let V (e : Sector N) := {p : W // sector p=e}
  let B (e : Sector N) := centeredTerminalPacket A hN P f hc he hr R hR hs e
  have hcB (e : Sector N) : Finite (V e) ∧
      (Nat.card (V e):ℝ)≤hilbertSchmidtEnergy basis (B e) := by
    apply independent_eigenfamily_finite basis (B e)
      (fun p : V e => windowDatum A hN P σ t ε p.val)
      (windowDatum_sector_independent A hN P σ t ε e)
      (fun p => (cosinePacket f p.val.val.1).re)
    · intro p
      have hg := windowDatum_realizes A hN P σ t ε p.val
      change physicalIsometry A hN P (sector p.val) _=_ at hg
      rw [p.property] at hg
      have hh := centeredTerminalPacket_original A hN P f hc he hr R hR hs e
        p.val.val.1 σ p.val.property.2.2 (windowDatum A hN P σ t ε p.val) hg
      rw [cosinePacket_real f hr p.val.val.1]
      exact hh
    · intro p
      exact hlower p.val.val.1 p.val.property.2.1
    · exact centeredTerminalPacket_summable A hN P f hc he hr R hR hs basis e
  let : ∀ e : Sector N,Finite (V e) := fun e => (hcB e).1
  let : Finite W := Finite.of_equiv (Σ e : Sector N,V e) (Equiv.sigmaFiberEquiv sector)
  refine ⟨Set.toFinite _,?_⟩
  have hcard : Nat.card W=∑ e : Sector N,Nat.card (V e) := by
    rw [←Nat.card_congr (Equiv.sigmaFiberEquiv sector),Nat.card_sigma]
  change (W.ncard:ℝ)≤∑ e : Sector N,hilbertSchmidtEnergy basis (B e)
  rw [←Nat.card_coe_set_eq,hcard,Nat.cast_sum]
  exact Finset.sum_le_sum (fun e _ => (hcB e).2)

#print axioms originalWindow_count_terminal_packet

end QuantitativeMaass.EulerHilbert.Nonzero
