module

public import AsymptoticGeneratorDetectionV1
public import AsymptoticFreshGlobalRankV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceDefect

open UpperHalfPlane Matrix MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceLabels AsymptoticRegularBranchFamily AsymptoticFreshCompactDefects
open AsymptoticOrbitDecode AsymptoticRegularTrace AsymptoticRationalBranches
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch (cap)
open scoped MatrixGroups Classical

noncomputable def branch (γ : SL(2,ℤ)) : Branch := ⟨rationalGL γ,rationalGL_positive γ⟩

/-- The actual weighted compact observation of a congruence relation. -/
noncomputable def operator (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  compact (branch γ) hs hε t x-compact identityBranch hs hε t x

noncomputable def bound (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  AsymptoticRegularBranchFamily.bound (branch γ) hs hε t+
    AsymptoticRegularBranchFamily.bound identityBranch hs hε t

theorem operator_norm_le (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : ‖operator γ hs hε t x‖≤bound γ hs hε t :=
  (norm_sub_le _ _).trans (add_le_add (compact_norm_le (branch γ) hs hε t x)
    (compact_norm_le identityBranch hs hε t x))

theorem operator_regular (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    (∀ g h,Measurable (fun x => matrix (operator γ hs hε t x) g h)) ∧
      Covariant (operator γ hs hε t) :=
  ⟨matrix_sub_measurable _ _ (compact_matrix_measurable (branch γ) hs hε t)
    (compact_matrix_measurable identityBranch hs hε t),
    covariant_sub _ _ (compact_covariant (branch γ) hs hε t) (compact_covariant identityBranch hs hε t)⟩

theorem operator_decode (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) (g : AsymptoticRationalGroup.Group) :
    operator γ hs hε t x v g=
      if g • x∈s then (cap ε t (g • x):ℂ)*
        (decode ε t x v (integralLabel γ*g)-decode ε t x v g) else 0 := by
  change compact (branch γ) hs hε t x v g-compact identityBranch hs hε t x v g=_
  rw [compact_decode,compact_decode,identityBranch_label,one_mul]
  have he : ofMatrix (branch γ).matrix (branch γ).positive=integralLabel γ := rfl
  rw [he]
  by_cases hg : g • x∈s
  · simp only [ite_eq_left hg]
    ring
  · simp only [ite_eq_right hg,sub_self]

theorem all_compact_zero_iff (γ : SL(2,ℤ)) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    (∀ s : Set ℍ,∀ hs : IsCompact s,operator γ hs hε t x v=0) ↔
      ∀ g : AsymptoticRationalGroup.Group,decode ε t x v (integralLabel γ*g)=decode ε t x v g := by
  constructor
  · intro h g
    have he := congrArg (fun u : Space => u g) (h {g • x} isCompact_singleton)
    rw [operator_decode,ite_eq_left (Set.mem_singleton _)] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (cap_ne_zero hε t (g • x)))
  · intro h s hs
    apply lp.ext
    funext g
    rw [operator_decode,h g,sub_self,mul_zero]
    simp

/-- Individual fresh-prime defects detect this compact congruence
observation inside any current kernel satisfying the untwisted law. -/
theorem global_individual_le_remaining (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (hd : γ 1 0∣(q:ℤ)-γ 0 0)
    (w : ℂ) (K : CompactExhaustion ℍ) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ)
    (U : Submodule ℂ Space) [CompleteSpace U]
    (hW : ∀ v∈U,∀ s : Set ℍ,∀ hs : IsCompact s,
      AsymptoticRegularObservationRows.twist N 1 hN Nat.zero_lt_one w hs hε t x v=0)
    {s : Set ℍ} (hs : IsCompact s) :
    AsymptoticCornerKernel.globalRemaining U (fun j => AsymptoticObservationStack.stack
      (AsymptoticFreshRank.observed N q hN hq w (K.isCompact j) hε t (fun _ => U.starProjection) x))≤
      AsymptoticCornerKernel.remaining U (operator γ hs hε t x) := by
  intro v hv
  have hv := (AsymptoticFreshRank.global_individual_mem_iff N q hN hq w K hε t
    U U.starProjection x v).mp hv
  refine ⟨hv.1,?_⟩
  have hinv := AsymptoticDecodedCongruence.generator_invariant_of_dvd N q hN hq γ hγ hd
    w hε t x v (hW v hv.1) (fun i s hs => by
      simpa only [U.starProjection_eq_self_iff.mpr hv.1] using hv.2 s hs i)
  exact (all_compact_zero_iff γ hε t x v).mpr hinv s hs

#print axioms operator_norm_le
#print axioms operator_regular
#print axioms operator_decode
#print axioms all_compact_zero_iff
#print axioms global_individual_le_remaining

end AsymptoticCongruenceDefect
