module

public import AsymptoticFrickeNormalizerV1
public import AsymptoticCoprimeCongruenceIndexV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels AsymptoticFreshMatrices

/-- The second old overgroup, obtained from the literal lower-level
group by the global Fricke involution. -/
noncomputable def frickeOldGroup (N d : ℕ) (hN : 0<N) : Subgroup AsymptoticRationalGroup.Group :=
  (gamma d).map (MulAut.conj (frickeLabel N hN)).toMonoidHom

theorem gamma_le_frickeOldGroup {N d : ℕ} (hN : 0<N) (hd : d∣N) :
    gamma N≤frickeOldGroup N d hN := by
  rw [← gamma_map_fricke N hN]
  exact Subgroup.map_mono (gamma_le_of_dvd hd)

theorem frickeOldGroup_index (N d : ℕ) (hN : 0<N) :
    (gamma N).relIndex (frickeOldGroup N d hN)=(gamma N).relIndex (gamma d) := by
  change (gamma N).relIndex ((gamma d).map (MulAut.conj (frickeLabel N hN)).toMonoidHom)=_
  conv_lhs => rw [← gamma_map_fricke N hN]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (frickeLabel N hN)).injective

noncomputable instance frickeOldGroup_quotient_finite (N d : ℕ) (hN : 0<N) :
    Finite (frickeOldGroup N d hN ⧸ (gamma N).subgroupOf (frickeOldGroup N d hN)) := by
  apply Subgroup.index_ne_zero_iff_finite.mp
  change (gamma N).relIndex (frickeOldGroup N d hN)≠0
  rw [frickeOldGroup_index]
  let : NeZero N := ⟨hN.ne'⟩
  let := gamma_finite_relIndex N d
  exact Subgroup.relIndex_ne_zero

theorem repeated_frickeOldGroup_index (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M) :
    (gamma (q*M)).relIndex (frickeOldGroup (q*M) M (Nat.mul_pos hq hM))=q := by
  rw [frickeOldGroup_index]
  exact AsymptoticRamifiedCosets.projective_index M q hM hq hqM

theorem coprime_frickeOldGroup_index (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hc : p.Coprime M) :
    (gamma (p*M)).relIndex (frickeOldGroup (p*M) M (Nat.mul_pos hp.pos hM))=p+1 := by
  rw [frickeOldGroup_index]
  exact AsymptoticRamifiedCosets.projective_index_coprime M p hM hp hc

#print axioms gamma_le_frickeOldGroup
#print axioms frickeOldGroup_index
#print axioms repeated_frickeOldGroup_index
#print axioms coprime_frickeOldGroup_index

end AsymptoticCongruenceStrip

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticRegularTrace
open scoped lp

noncomputable def frickeSpace {N d : ℕ} (hN : 0<N) (hd : d∣N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  space N (frickeOldGroup N d hN) (gamma_le_frickeOldGroup hN hd) hε ht z

noncomputable instance frickeSpace_complete {N d : ℕ} (hN : 0<N) (hd : d∣N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) : CompleteSpace (frickeSpace hN hd hε ht z) :=
  inferInstanceAs (CompleteSpace (space N (frickeOldGroup N d hN) (gamma_le_frickeOldGroup hN hd) hε ht z))

theorem frickeSpace_trace {N d : ℕ} (hN : 0<N) (hd : d∣N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    (trace volume (fun z => (frickeSpace hN hd hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal/
        ((gamma N).relIndex (gamma d):ℝ) := by
  change (trace volume (fun z => (space N (frickeOldGroup N d hN)
    (gamma_le_frickeOldGroup hN hd) hε ht z).starProjection)).toReal=_
  rw [projection_trace_toReal]
  rw [show ((gamma N).subgroupOf (frickeOldGroup N d hN)).index=
    (gamma N).relIndex (gamma d) from frickeOldGroup_index N d hN]

#print axioms frickeSpace_trace

end AsymptoticCongruenceOldSpace
