module

public import QuantitativeMaassLocalAtkinTraceV1
public import QuantitativeMaassNormalizerBandV1
public import QuantitativeMaassCuspidalNewPacketV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass QuantitativeNewGap
namespace QuantitativeMaass

/-- Each actual local Atkin involution preserves both trace equations at
every prime, including repeated-prime constraints at other primes. -/
theorem completedLocalAtkin_newTraceKernel (N : ℕ) [NeZero N] (hN : 0<N)
    (p : SimplePrime N) (q : ℕ) (hq : q.Prime) (hqN : q∣N)
    (x : AutomorphicSpace N) (hx : x∈newTraceKernel hN (Nat.div_dvd_of_dvd hqN)) :
    quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x∈
      newTraceKernel hN (Nat.div_dvd_of_dvd hqN) := by
  let U := quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p)
  have hc := DFunLike.congr_fun (completedLocalAtkin_fricke_commute N hN p) x
  change U (frickeIsometry N hN x)=frickeIsometry N hN (U x) at hc
  change levelTrace (Nat.div_dvd_of_dvd hqN) x=0 ∧
    levelTrace (Nat.div_dvd_of_dvd hqN) (frickeIsometry N hN x)=0 at hx
  change levelTrace (Nat.div_dvd_of_dvd hqN) (U x)=0 ∧
    levelTrace (Nat.div_dvd_of_dvd hqN) (frickeIsometry N hN (U x))=0
  rw [←hc]
  dsimp only [U]
  by_cases hpq : p.val=q
  · subst q
    constructor
    · rw [completedLocalAtkin_own_trace,hx.2,map_zero]
    · rw [completedLocalAtkin_own_trace,frickeIsometry_involutive,hx.1,map_zero]
  · constructor
    · rw [completedLocalAtkin_other_trace N hN p q hq hqN hpq,hx.1,map_zero]
    · rw [completedLocalAtkin_other_trace N hN p q hq hqN hpq,hx.2,map_zero]

/-- Actual all-prime newspace preservation, with every defining trace
constraint discharged by arithmetic normalizer identities. -/
theorem completedLocalAtkin_newSpace (N : ℕ) [NeZero N] (hN : 0<N)
    (p : SimplePrime N) (x : AutomorphicSpace N) (hx : x∈newSpace N hN) :
    quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x∈newSpace N hN := by
  simp only [newSpace,Submodule.mem_iInf] at hx ⊢
  intro q
  exact completedLocalAtkin_newTraceKernel N hN p q.val q.property.1 q.property.2 x (hx q)

theorem completedLocalAtkin_cuspidalNewSpace (N : ℕ) [NeZero N] (hN : 0<N)
    (p : SimplePrime N) (x : AutomorphicSpace N) (hx : x∈completedCuspidalNewSpace N hN) :
    quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x∈completedCuspidalNewSpace N hN :=
  ⟨quotientNormalizerPullback_mem_cuspidal N hN _ x hx.1,completedLocalAtkin_newSpace N hN p x hx.2⟩

/-- The actual local Atkin and cuspidal-new orthogonal projections commute. -/
theorem completedLocalAtkin_cuspidalNew_commute (N : ℕ) [NeZero N] (hN : 0<N)
    (p : SimplePrime N) :
    Commute (completedCuspidalNewSpace N hN).starProjection
      (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p)).toContinuousLinearMap :=
  invariantSpace_projection_commute _ _ (completedLocalAtkin_selfAdjoint N hN p)
    (completedLocalAtkin_cuspidalNewSpace N hN p)

#print axioms completedLocalAtkin_newTraceKernel
#print axioms completedLocalAtkin_newSpace
#print axioms completedLocalAtkin_cuspidalNewSpace
#print axioms completedLocalAtkin_cuspidalNew_commute
end QuantitativeMaass
