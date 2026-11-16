module

public import QuantitativeArithmeticRepeatedTwoBandsV1
public import QuantitativeMaassInvariantPacketSpaceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
@[expose] public noncomputable section

open QuantitativeMaass QuantitativeNinaMaass
open QuantitativeArithmeticRepeatedTwoProjector
open scoped InnerProductSpace

namespace QuantitativeArithmeticCrossPrimeBands

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance


/-- An invariant subspace for a self-adjoint operator has a projection
commuting with the projection onto its kernel. -/
theorem kernel_projection_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (K : Submodule ℂ E)
    (hK : ∀ x∈K,A x∈K) : Commute A.ker.starProjection K.starProjection := by
  have hc := invariantSpace_projection_commute K A hA hK
  apply invariantSpace_projection_commute A.ker K.starProjection
    (isSelfAdjoint_starProjection K)
  intro x hx
  change A (K.starProjection x)=0
  have he := DFunLike.congr_fun hc.eq x
  change K.starProjection (A x)=A (K.starProjection x) at he
  change A x=0 at hx
  rw [hx,map_zero] at he
  exact he.symm

section Gram
variable {M N : ℕ} [NeZero M] [NeZero N] {hM : 0<M} {hN : 0<N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M∣N) (a b σ : ℝ)

def traceMap := (S.traceParityBandMap T hMN a b σ).toContinuousLinearMap

def coverMap := (S.coverParityBandMap T hMN a b σ).toContinuousLinearMap

def frickeMap := (T.frickeParityBandMap a b σ).toContinuousLinearMap

theorem trace_adjoint : (traceMap S T hMN a b σ).adjoint=coverMap S T hMN a b σ := by
  have hc : (coverMap S T hMN a b σ).adjoint=traceMap S T hMN a b σ := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (S.traceBandMap_pairing T hMN a b x.val y.val).symm
  exact (congrArg ContinuousLinearMap.adjoint hc).symm.trans
    (ContinuousLinearMap.adjoint_adjoint _)

theorem fricke_selfAdjoint : IsSelfAdjoint (frickeMap T a b σ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (frickeIsometry_selfAdjoint N hN) (x.val.val : AutomorphicSpace N)
      (y.val.val : AutomorphicSpace N)

/-- Unnormalized Gram sum works at both simple and repeated primes. -/
def traceGram : T.parityBand a b σ →L[ℂ] T.parityBand a b σ :=
  (traceMap S T hMN a b σ).adjoint.comp (traceMap S T hMN a b σ)+
    ((traceMap S T hMN a b σ).comp (frickeMap T a b σ)).adjoint.comp
      ((traceMap S T hMN a b σ).comp (frickeMap T a b σ))

theorem traceGram_selfAdjoint : IsSelfAdjoint (traceGram S T hMN a b σ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [traceGram,map_add,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem traceGram_kernel : (traceGram S T hMN a b σ).ker=
    S.traceNewParityBand T hMN a b σ := by
  rw [traceGram,sum_gram_kernel]
  rfl

theorem traceGram_apply (x : T.parityBand a b σ) :
    traceGram S T hMN a b σ x =
      S.coverParityBandMap T hMN a b σ (S.traceParityBandMap T hMN a b σ x)+
      T.frickeParityBandMap a b σ (S.coverParityBandMap T hMN a b σ
        (S.traceParityBandMap T hMN a b σ (T.frickeParityBandMap a b σ x))) := by
  simp only [traceGram,ContinuousLinearMap.adjoint_comp,trace_adjoint,
    (fricke_selfAdjoint T a b σ).adjoint_eq,add_apply,ContinuousLinearMap.comp_apply]
  rfl

end Gram

/-- The other prime's two trace equations are preserved by the ordinary
cover-trace composition, without any prime-exponent restriction. -/
theorem cover_trace_cross_new (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0<M) (hp : 0<p) (hq : q.Prime) (hc : p.Coprime q)
    (S : CuspEnergySpectrum (q*M) (Nat.mul_pos hq.pos hM))
    (T : CuspEnergySpectrum (p*(q*M)) (Nat.mul_pos hp (Nat.mul_pos hq.pos hM)))
    (a b σ : ℝ) (x : T.parityBand a b σ)
    (hx : (x.val.val : AutomorphicSpace (p*(q*M))) ∈
      newTraceKernel (Nat.mul_pos hp (Nat.mul_pos hq.pos hM))
        (show p*M∣p*(q*M) from ⟨q,by ring⟩)) :
    ((S.coverParityBandMap T (Nat.dvd_mul_left (q*M) p) a b σ
      (S.traceParityBandMap T (Nat.dvd_mul_left (q*M) p) a b σ x)).val.val :
        AutomorphicSpace (p*(q*M))) ∈
      newTraceKernel (Nat.mul_pos hp (Nat.mul_pos hq.pos hM))
        (show p*M∣p*(q*M) from ⟨q,by ring⟩) := by
  have ht := levelTrace_cross_new M p q hM hp hq.pos
    (x.val.val : AutomorphicSpace (p*(q*M))) hx
  exact (CuspEnergySpectrum.coverBandMap_cross_new M p q hM hp hq hc S T a b
    (S.traceParityBandMap T (Nat.dvd_mul_left (q*M) p) a b σ x).val ht).1

/-- Local new projections at distinct primes commute on the full cusp
parity band, including when either prime divides M. -/
theorem local_new_projections_commute (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0<M) (hp : p.Prime) (hq : q.Prime) (hc : p.Coprime q)
    (S : CuspEnergySpectrum (q*M) (Nat.mul_pos hq.pos hM))
    (R : CuspEnergySpectrum (p*M) (Nat.mul_pos hp.pos hM))
    (T : CuspEnergySpectrum (p*(q*M)) (Nat.mul_pos hp.pos (Nat.mul_pos hq.pos hM)))
    (a b σ : ℝ) :
    Commute (S.traceNewParityBand T (Nat.dvd_mul_left (q*M) p) a b σ).starProjection
      (R.traceNewParityBand T (show p*M∣p*(q*M) from ⟨q,by ring⟩) a b σ).starProjection := by
  let dp := Nat.dvd_mul_left (q*M) p
  have dq : p*M∣p*(q*M) := ⟨q,by ring⟩
  let K := R.traceNewParityBand T dq a b σ
  have hi : ∀ x∈K,traceGram S T dp a b σ x∈K := by
    intro x hx
    have hx' := (R.mem_traceNewParityBand T dq a b σ x).mp hx
    have hf := newTraceKernel_fricke _ dq _ hx'
    have ho := cover_trace_cross_new M p q hM hp.pos hq hc S T a b σ x hx'
    have ho' := cover_trace_cross_new M p q hM hp.pos hq hc S T a b σ
      (T.frickeParityBandMap a b σ x) hf
    apply (R.mem_traceNewParityBand T dq a b σ _).mpr
    rw [traceGram_apply]
    exact (newTraceKernel _ dq).add_mem ho (newTraceKernel_fricke _ dq _ ho')
  have hh := kernel_projection_commute (traceGram S T dp a b σ)
    (traceGram_selfAdjoint S T dp a b σ) K hi
  simpa only [traceGram_kernel,K,dp] using hh

#print axioms kernel_projection_commute
#print axioms trace_adjoint
#print axioms traceGram_selfAdjoint
#print axioms traceGram_kernel
#print axioms cover_trace_cross_new
#print axioms local_new_projections_commute

end QuantitativeArithmeticCrossPrimeBands
