module

public import AsymptoticDecodedCongruenceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticDecodedCongruence

open Matrix AsymptoticCongruenceLabels AsymptoticFreshCRT AsymptoticOrbitDecode
open AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open UpperHalfPlane
open scoped MatrixGroups

/-- The first-entry congruence detects the original Gamma0 matrix,
with its entries and translating integer obtained from divisibility. -/
theorem generator_invariant_of_dvd (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N)
    (hd : γ 1 0∣(q:ℤ)-γ 0 0)
    (w : ℂ) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space)
    (hW : ∀ s : Set ℍ,∀ hs : IsCompact s,twist N 1 hN Nat.zero_lt_one w hs hε t x f=0)
    (hrows : ∀ i : Fin (q-1),∀ s : Set ℍ,∀ hs : IsCompact s,
      AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x f=0) :
    ∀ g : AsymptoticRationalGroup.Group,decode ε t x f (integralLabel γ*g)=decode ε t x f g := by
  have hc : (N:ℤ)∣γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  obtain ⟨c,hc⟩ := hc
  obtain ⟨u,hu⟩ := hd
  have he : γ.val=!![γ 0 0,γ 0 1;(N:ℤ)*c,γ 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc]
  apply decoded_generator_invariant N q hN hq γ (γ 0 0) (γ 0 1) c (γ 1 1) u he _
    w hε t x f hW hrows
  rw [← hc]
  linarith

/-- A fixed unit class in any common nonzero modulus supplies the
correct congruence for every sufficiently large fresh prime. This
derives detection from the original compact equations, without assuming
an individual modular-invariance equation. -/
theorem generator_class (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 N) (L : ℕ) [NeZero L]
    (hL : (γ 1 0).natAbs∣L) :
    ∃ r : ℕ,r<L ∧ r.Coprime L ∧
      ∀ q : ℕ,∀ hqp : q.Prime,∀ hq : ¬q∣N,
      (q:ZMod L)=(r:ZMod L) →
      ∀ w : ℂ,∀ ε : ℝ,∀ hε : 0<ε,∀ t : ℕ,∀ x : ℍ,∀ f : Space,
      (∀ s : Set ℍ,∀ hs : IsCompact s,twist N 1 hN Nat.zero_lt_one w hs hε t x f=0) →
      (letI : Fact q.Prime := ⟨hqp⟩
        ∀ i : Fin (q-1),∀ s : Set ℍ,∀ hs : IsCompact s,
          AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x f=0) →
      ∀ g : AsymptoticRationalGroup.Group,decode ε t x f (integralLabel γ*g)=decode ε t x f g := by
  obtain ⟨r,hr,hcop,hres⟩ := generator_residue γ (γ 1 0).natAbs L Int.natAbs_dvd_self hL
  refine ⟨r,hr,hcop,?_⟩
  intro q hqp hq hqr w ε hε t x f hW hrows
  let : Fact q.Prime := ⟨hqp⟩
  have hd := residue_descends (γ 1 0).natAbs L r q (γ 0 0) hL hres hqr
  exact generator_invariant_of_dvd N q hN hq γ hγ (Int.natAbs_dvd.mp hd) w hε t x f hW hrows

#print axioms generator_invariant_of_dvd
#print axioms generator_class

end AsymptoticDecodedCongruence
