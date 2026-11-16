module

public import QuantitativeMaassFullParityEmbeddingV1
public import QuantitativeMaassFullResidualFilterV1
public import QuantitativeMaassFullParityOrthogonalV1
public import QuantitativeMaassOrthogonalExcessCountV1
public import QuantitativeMaassHilbertSchmidtIdealV1
public import QuantitativeMaassCompletedTerminalPacketV1
public import QuantitativeMaassCompletedTerminalMetricV1
public import QuantitativeMaassWeightedTargetProjectionV1
public import QuantitativeMaassEmbeddingTargetCountV1
public import QuantitativeMaassTerminalPacketCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns QuantitativeNewGap
open scoped SchwartzMap ContDiff

namespace QuantitativeMaass

local instance (ε : ℝ) : NormedAddCommGroup (AsymptoticCylinderTerminal.Space ε) := inferInstance
local instance (ε : ℝ) : InnerProductSpace ℂ (AsymptoticCylinderTerminal.Space ε) := inferInstance
local instance (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ) :
    NormedAddCommGroup (completedNewSignParitySpace N hN χ η) := inferInstance
local instance (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ) :
    InnerProductSpace ℂ (completedNewSignParitySpace N hN χ η) := inferInstance

/-- The original fixed-parity Euler count uses the unmodified common twist
filter. Exact orthogonality removes the opposite canonical parity from the
excess; no approximation to a parity residual filter is required. -/
theorem originalWindow_fullTerminal_sector_count_orthogonal_excess {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (η : ℝ) (hηsq : η^2=1) (χ : admissibleGeneratorIndex N hN.1 → ℂ) (e : Sector N) (hχ : ∀ i,‖χ i‖=1)
    (hχW : χ (frickeGeneratorIndex N hN.1)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN.1 p)= -delta e p.val)
    {ι κ : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε))
    (c : HilbertBasis κ ℂ (completedNewSignParitySpace N hN.1 χ η)) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Set UpperHalfPlane) (hsObs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) (σ : ℕ) (_hη : η=(-1:ℝ)^σ) (t ε : ℝ)
      (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
      (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
      (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R),
      (∀ r∈Icc t (t+ε),1≤(cosinePacket f r).re) →
      let V := {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
        EulerHilbert.FullTerminal.windowSector A hN.1 P σ t ε p=e}
      let B := (EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e).comp
        (EulerHilbert.FullTerminal.commonResidualFilter A hN.1 P e hsObs qs d)
      Finite V ∧ (Nat.card V:ℝ)≤
        hilbertSchmidtEnergy c (completedNewSignParityTimePacket N hN.1 χ η f hc he hr R hR hs)+
        C*hilbertSchmidtEnergy basis (B.comp
          (1-embeddingGramProjection (V := completedNewSignParitySpace N hN.1 χ η)
            (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
            (completedNewSignParityFullTerminalEmbedding A hN.1 P χ e η)-
          embeddingGramProjection (V := completedNewSignParitySpace N hN.1 χ (-η))
            (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
            (completedNewSignParityFullTerminalEmbedding A hN.1 P χ e (-η)))) := by
  obtain ⟨a,ha,hl⟩ := completedNewSignParityFullTerminalEmbedding_lower A hN P
  have hK (x : completedNewSignParitySpace N hN.1 χ η) :
      a*‖x‖^2≤‖completedNewSignParityFullTerminalEmbedding A hN.1 P χ e η x‖^2 := hl χ e η hχ hχW hχS x
  let Kopp := completedNewSignParityFullTerminalEmbedding A hN.1 P χ e (-η)
  have hopp (x : completedNewSignParitySpace N hN.1 χ (-η)) :
      a*‖x‖^2≤‖Kopp x‖^2 := hl χ e (-η) hχ hχW hχS x
  have hclosed := lower_energy_injective_closed
    (H := completedNewSignParitySpace N hN.1 χ (-η))
    (K := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) Kopp ha hopp
  let W := Kopp.range
  let : CompleteSpace W := hclosed.2.completeSpace_coe
  have hKW (x : completedNewSignParitySpace N hN.1 χ η) :
      completedNewSignParityFullTerminalEmbedding A hN.1 P χ e η x∈Wᗮ := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro y hy
    obtain ⟨z,rfl⟩ := hy
    exact completedParityFullTerminal_opposite_inner_zero A hN.1 P χ e η hηsq hχW hχS x z
  have hp : W.starProjection=embeddingGramProjection
      (V := completedNewSignParitySpace N hN.1 χ (-η))
      (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) Kopp :=
    embedding_projection_gram_formula Kopp ha hopp
  have hgeneral := exists_embedding_target_count_orthogonal
    (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (V := completedNewSignParitySpace N hN.1 χ η)
    (completedNewSignParityFullTerminalEmbedding A hN.1 P χ e η) ha hK basis c W hKW
  obtain ⟨C,hC,hcount⟩ := hgeneral
  refine ⟨C,hC,?_⟩
  intro s hsObs qs d σ hη t ε f hc he hr R hR hs hlower
  let V := {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
    EulerHilbert.FullTerminal.windowSector A hN.1 P σ t ε p=e}
  let B := (EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e).comp
        (EulerHilbert.FullTerminal.commonResidualFilter A hN.1 P e hsObs qs d)
  let D := completedNewSignParityTimePacket N hN.1 χ η f hc he hr R hR hs
  have hBD (x : completedNewSignParitySpace N hN.1 χ η) : B (completedNewSignParityFullTerminalEmbedding A hN.1 P χ e η x)=
      completedNewSignParityFullTerminalEmbedding A hN.1 P χ e η (D x) := by
    change EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e
      (EulerHilbert.FullTerminal.commonResidualFilter A hN.1 P e hsObs qs d
        (completedNewSignParityFullTerminalEmbedding A hN.1 P χ e η x))=_
    rw [completedNewSignParityFullTerminalEmbedding_filter A hN.1 P χ e η hχW hχS]
    exact completedNewSignParityFullTerminalEmbedding_packet A hN.1 P χ e η hχW hχS f hc he hr R hR hs x
  have hact (p : V) : B (EulerHilbert.FullTerminal.windowDatum A hN.1 P σ t ε p.val)=
      ((cosinePacket f p.val.val.1).re:ℂ) • EulerHilbert.FullTerminal.windowDatum A hN.1 P σ t ε p.val := by
    have hfix := EulerHilbert.FullTerminal.windowDatum_fixed A hN.1 P σ t ε p.val s hsObs qs d
    rw [p.property] at hfix
    change EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e
      (EulerHilbert.FullTerminal.commonResidualFilter A hN.1 P e hsObs qs d
        (EulerHilbert.FullTerminal.windowDatum A hN.1 P σ t ε p.val))=_
    rw [hfix]
    have hg := EulerHilbert.FullTerminal.windowDatum_realizes A hN.1 P σ t ε p.val
    rw [p.property] at hg
    have hh := EulerHilbert.FullTerminal.centeredTerminalPacket_original A hN.1 P f hc he hr R hR hs e
      p.val.val.1 σ p.val.property.2.2 (EulerHilbert.FullTerminal.windowDatum A hN.1 P σ t ε p.val) hg
    rw [cosinePacket_real f hr p.val.val.1]
    exact hh
  have hBW (y : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
      (hy : y∈W) : B y∈W := by
    obtain ⟨x,rfl⟩ := hy
    refine ⟨completedNewSignParityTimePacket N hN.1 χ (-η) f hc he hr R hR hs x,?_⟩
    change _=EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e
      (EulerHilbert.FullTerminal.commonResidualFilter A hN.1 P e hsObs qs d (Kopp x))
    rw [completedNewSignParityFullTerminalEmbedding_filter A hN.1 P χ e (-η) hχW hχS]
    exact (completedNewSignParityFullTerminalEmbedding_packet A hN.1 P χ e (-η) hχW hχS f hc he hr R hR hs x).symm
  have hvW (p : V) : EulerHilbert.FullTerminal.windowDatum A hN.1 P σ t ε p.val∈Wᗮ := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro y hy
    obtain ⟨z,rfl⟩ := hy
    subst η
    exact fullWindowDatum_opposite_target_inner_zero A hN.1 P σ t ε p.val e p.property χ hχW hχS z
  have hcounted := hcount B D hBD hBW V
    (fun p : V => EulerHilbert.FullTerminal.windowDatum A hN.1 P σ t ε p.val)
    (EulerHilbert.FullTerminal.windowDatum_sector_independent A hN.1 P σ t ε e) hvW
    (fun p => (cosinePacket f p.val.val.1).re) hact
    (fun p => hlower p.val.val.1 p.val.property.2.1)
    ((right_comp_energy_bound basis
      (EulerHilbert.FullTerminal.centeredTerminalPacket A hN.1 P f hc he hr R hR hs e)
      (EulerHilbert.FullTerminal.commonResidualFilter A hN.1 P e hsObs qs d)
      (EulerHilbert.FullTerminal.centeredTerminalPacket_summable A hN.1 P f hc he hr R hR hs basis e)).1)
  rw [hp] at hcounted
  exact hcounted

#print axioms originalWindow_fullTerminal_sector_count_orthogonal_excess

end QuantitativeMaass
