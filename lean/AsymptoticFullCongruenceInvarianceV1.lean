module

public import AsymptoticFreshCongruenceVanishingV1
public import AsymptoticCongruenceGeneratorsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceDefect

open UpperHalfPlane Matrix AsymptoticOrbitDecode AsymptoticCongruenceLabels
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups

theorem exhaustion_zero_iff (γ : SL(2,ℤ)) (K : CompactExhaustion ℍ)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    (∀ j,operator γ (K.isCompact j) hε t x v=0) ↔
      ∀ g : AsymptoticRationalGroup.Group,decode ε t x v (integralLabel γ*g)=decode ε t x v g := by
  constructor
  · intro h g
    obtain ⟨j,hj⟩ := K.exists_superset_of_isCompact (isCompact_singleton (x:=g • x))
    have he := congrArg (fun u : Space => u g) (h j)
    rw [operator_decode,ite_eq_left (hj (Set.mem_singleton _))] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (cap_ne_zero hε t (g • x)))
  · intro h j
    exact (all_compact_zero_iff γ hε t x v).mpr h (K j) (K.isCompact j)

#print axioms exhaustion_zero_iff

end AsymptoticCongruenceDefect

namespace AsymptoticRegularObservation

open UpperHalfPlane Matrix MeasureTheory AsymptoticOrbitDecode AsymptoticCongruenceLabels
open AsymptoticCompactObservationCount (Row)
open AsymptoticSectorSigns FinitenessCertificate FinitenessGlobalHeight
open scoped MatrixGroups

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The full original equation kernel has decoded Gamma0(N) invariance
almost everywhere, derived from fresh-prime rank loss. This is an actual
regular-kernel conclusion, not an added modular-invariance hypothesis. -/
theorem globalKernel_ae_congruence_invariant (hN : 0<N) (P : Parameters A)
    (r : ℕ → Row N) (hcover : ∀ q : ℕ,∀ hq : 0<q,∃ j,r j=.twist q hq)
    (K : CompactExhaustion ℍ) (e : Sector N) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ∀ᵐ x ∂volume,∀ γ∈CongruenceSubgroup.Gamma0 N,
      ∀ v∈globalKernelSpace A hN P r K e x,∀ g : AsymptoticRationalGroup.Group,
        decode P'.ε (P'.s+4) x v (integralLabel γ*g)=decode P'.ε (P'.s+4) x v g := by
  let : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let : Countable SL(2,ℤ) :=
    Function.Injective.countable (f:=fun γ : SL(2,ℤ) => γ.val) Subtype.val_injective
  apply ae_all_iff.mpr
  intro γ
  by_cases hγ : γ∈CongruenceSubgroup.Gamma0 N
  · by_cases h10 : γ 1 0=0
    · obtain ⟨u,hu⟩ := triangular_label γ h10
      apply Filter.Eventually.of_forall
      intro x _ v _ g
      rw [hu]
      exact decode_periodic _ _ x v g u
    · have hk := ae_all_iff.mpr (fun j =>
        ae_compact_congruence_of_nontriangular A hN P r hcover K e γ hγ h10 (K.isCompact j))
      filter_upwards [hk] with x hx _ v hv
      exact (AsymptoticCongruenceDefect.exhaustion_zero_iff γ K
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4) x v).mp (fun j => hx j v hv)
  · exact Filter.Eventually.of_forall (fun _ h => (hγ h).elim)

#print axioms globalKernel_ae_congruence_invariant

end AsymptoticRegularObservation
