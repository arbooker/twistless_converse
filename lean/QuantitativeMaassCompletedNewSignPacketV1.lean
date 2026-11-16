module

public import QuantitativeMaassInvariantPacketSpaceV1
public import QuantitativeMaassNormalizerPacketV1
public import QuantitativeMaassCompletedNewSignSpaceV1
public import QuantitativeMaassWeightedPacketIntertwiningV1
public import QuantitativeMaassLVCuspidalProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeNinaMaass
open AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem actualNewSpace_closed (N : ℕ) [NeZero N] (hN : 0<N) :
    IsClosed (newSpace N hN : Set (AutomorphicSpace N)) := by
  simp only [newSpace,newTraceKernel,Submodule.coe_iInf,Submodule.coe_inf]
  exact isClosed_iInter (fun p => (levelTrace (Nat.div_dvd_of_dvd p.property.2)).isClosed_ker.inter
    ((levelTrace (Nat.div_dvd_of_dvd p.property.2)).comp
      (frickeIsometry N hN).toContinuousLinearMap).isClosed_ker)

theorem actualNewSpace_resolvent (N : ℕ) [NeZero N] (hN : 0<N)
    (x : AutomorphicSpace N) (hx : x∈newSpace N hN) :
    friedrichsResolvent N x∈newSpace N hN := by
  simp only [newSpace,Submodule.mem_iInf] at hx ⊢
  intro p
  have hp : 0<N/p.val := Nat.div_pos (Nat.le_of_dvd hN p.property.2) p.property.1.pos
  let : NeZero (N/p.val) := ⟨hp.ne'⟩
  have ht := hx p
  have ht1 : levelTrace (Nat.div_dvd_of_dvd p.property.2) x=0 := ht.1
  have ht2 : levelTrace (Nat.div_dvd_of_dvd p.property.2) (frickeIsometry N hN x)=0 := ht.2
  constructor
  · change levelTrace (Nat.div_dvd_of_dvd p.property.2) (friedrichsResolvent N x)=0
    rw [←levelTrace_resolvent,ht1,map_zero]
  · change levelTrace (Nat.div_dvd_of_dvd p.property.2)
      (frickeIsometry N hN (friedrichsResolvent N x))=0
    rw [←fricke_resolvent,←levelTrace_resolvent,ht2,map_zero]

/-- The actual simultaneous trace-new space is preserved by every
integrable shifted wave packet. -/
theorem actualNewSpace_timePacket (N : ℕ) [NeZero N] (hN : 0<N)
    (f : ℝ → ℂ) (hf : Wave.ShiftedWaveWeight f)
    (x : AutomorphicSpace N) (hx : x∈newSpace N hN) :
    Wave.shiftedQuotientWavePacket N f hf x∈newSpace N hN := by
  let : CompleteSpace (newSpace N hN) := (actualNewSpace_closed N hN).completeSpace_coe
  exact resolventInvariantSpace_timePacket N (newSpace N hN) (actualNewSpace_resolvent N hN) f hf x hx

theorem completedNewSignSpace_timePacket (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : AutomorphicSpace N) (hx : x∈completedNewSignSpace N hN χ) :
    Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc) x∈
      completedNewSignSpace N hN χ :=
  ⟨shiftedQuotientWavePacket_mem_localCuspidalSpace N hN f _ x hx.1,
    actualNewSpace_timePacket N hN f _ x hx.2.1,
    completedGeneratorSpace_timePacket N hN χ f hf he hc hr R hR hs x hx.2.2⟩

/-- The actual restricted spectral operator on the closed new/sign space. -/
def completedNewSignTimePacket (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    completedNewSignSpace N hN χ →L[ℂ] completedNewSignSpace N hN χ :=
  ((Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f hf hc)).comp
    (completedNewSignSpace N hN χ).subtypeL).codRestrict (completedNewSignSpace N hN χ)
      (fun x => completedNewSignSpace_timePacket N hN χ f hf he hc hr R hR hs x.val x.property)

/-- The target restriction and weighted intertwining are both proved for
the concrete operators appearing in the upper-count argument. -/
theorem completedNewSignTimePacket_intertwining (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) (x : completedNewSignSpace N hN χ) :
    cylinderCappedTimePacket f hf he hc hr R hR hs ε hε v
      (completedNewSignWeightedEmbedding N hN hε hv χ x)=
      completedNewSignWeightedEmbedding N hN hε hv χ
        (completedNewSignTimePacket N hN χ f hf he hc hr R hR hs x) :=
  weightedQuotientEmbedding_timePacket N f hf he hc hr R hR hs hε hv x.val

#print axioms actualNewSpace_closed
#print axioms actualNewSpace_resolvent
#print axioms actualNewSpace_timePacket
#print axioms completedNewSignSpace_timePacket
#print axioms completedNewSignTimePacket_intertwining

end QuantitativeMaass
