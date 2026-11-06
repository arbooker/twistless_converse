module

public import AsymptoticFreshRankV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularBranchFamily

open UpperHalfPlane ContinuousLinearMap AsymptoticRegularCompactBranch
open AsymptoticCompactBranch (coefficient)

/-- Compact observations are compatible under restriction, even when
their finite folding certificates have different sizes. -/
theorem compact_restrict (b : Branch) {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u)
    (hsub : s⊆u) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner s x).comp (compact b hu hε t x)=compact b hs hε t x := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext a
  change AsymptoticOrbitDiagonal.corner s x (compact b hu hε t x f) a=_
  rw [AsymptoticOrbitDiagonal.corner_apply]
  simp only [compact,operator_selected]
  by_cases ha : a • x∈s
  · rw [ite_eq_left ha,coefficient,coefficient,Set.indicator_of_mem (hsub ha),Set.indicator_of_mem ha]
  · rw [ite_eq_right ha,coefficient,Set.indicator_of_notMem ha,zero_mul]

theorem family_restrict {ι : Type*} [Fintype ι] (b : ι → Branch) (c : ι → ℂ)
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u) (hsub : s⊆u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner s x).comp (family b c hu hε t x)=family b c hs hε t x := by
  simp only [family,comp_finsetSum,comp_smul,compact_restrict _ hs hu hsub hε t x]

#print axioms compact_restrict
#print axioms family_restrict

end AsymptoticRegularBranchFamily

namespace AsymptoticFreshRank

open AsymptoticFreshCompactDefects AsymptoticRegularBranchFamily
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactFamilyTranslation AsymptoticIntegralSubgroup
open AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticCornerKernel AsymptoticMixing UpperHalfPlane ContinuousLinearMap

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
variable (w : ℂ) {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u) (hsub : s⊆u)
variable {ε : ℝ} (hε : 0<ε) (t : ℕ)

include hsub

theorem row_restrict (i : Fin (q-1)) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner (shifted (parameter q i) s) x).comp
      (AsymptoticFreshCompactDefects.row N q hN hq w hu hε t i x)=
      AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x := by
  have hshift : shifted (parameter q i) s⊆shifted (parameter q i) u := Set.image_mono hsub
  simp only [AsymptoticFreshCompactDefects.row,comp_sub,comp_smul,
    compact_restrict _ (shifted_compact (parameter q i) hs)
      (shifted_compact (parameter q i) hu) hshift hε t x]

omit hq in
theorem twist_restrict (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner s x).comp
      (twist N q hN (Fact.out : q.Prime).pos w hu hε t x)=
      twist N q hN (Fact.out : q.Prime).pos w hs hε t x :=
  family_restrict _ _ hs hu hsub hε t x

theorem individual_ker_le (R : Space →L[ℂ] Space) (x : ℍ) :
    (stack (observed N q hN hq w hu hε t (fun _ => R) x)).ker≤
      (stack (observed N q hN hq w hs hε t (fun _ => R) x)).ker := by
  intro f hf
  apply (stack_eq_zero_iff _ f).mpr
  have hf := (stack_eq_zero_iff _ f).mp hf
  intro i
  change AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x (R f)=0
  rw [← row_restrict N q hN hq w hs hu hsub hε t i x]
  change AsymptoticOrbitDiagonal.corner _ x
    (observed N q hN hq w hu hε t (fun _ => R) x i f)=0
  rw [hf i,map_zero]

omit hq in
theorem twist_ker_le (R : Space →L[ℂ] Space) (x : ℍ) :
    ((twist N q hN (Fact.out : q.Prime).pos w hu hε t x).comp R).ker≤
      ((twist N q hN (Fact.out : q.Prime).pos w hs hε t x).comp R).ker := by
  intro f hf
  change twist N q hN (Fact.out : q.Prime).pos w hs hε t x (R f)=0
  rw [← twist_restrict N q hN w hs hu hsub hε t x]
  change AsymptoticOrbitDiagonal.corner s x
    (((twist N q hN (Fact.out : q.Prime).pos w hu hε t x).comp R) f)=0
  rw [show ((twist N q hN (Fact.out : q.Prime).pos w hu hε t x).comp R) f=0 from hf,map_zero]

#print axioms row_restrict
#print axioms twist_restrict
#print axioms individual_ker_le
#print axioms twist_ker_le

end AsymptoticFreshRank
