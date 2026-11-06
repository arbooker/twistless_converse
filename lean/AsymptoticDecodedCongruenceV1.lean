module

public import AsymptoticCongruenceLabelsV1
public import AsymptoticFreshDecodedRelationsV1
public import AsymptoticDecodedObservationsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticDecodedCongruence

open Matrix AsymptoticRationalGroup AsymptoticIntegralSubgroup AsymptoticFreshMatrices
open AsymptoticCongruenceLabels AsymptoticFreshCRT AsymptoticOrbitDecode
open AsymptoticFreshDecodedRelations AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open UpperHalfPlane
open scoped MatrixGroups

/-- Left invariance of a decoded function defines an actual subgroup
of the same rational projective group as the orbit representation. -/
def invariantSubgroup (F : AsymptoticRationalGroup.Group → ℂ) : Subgroup AsymptoticRationalGroup.Group where
  carrier := {a | ∀ g,F (a*g)=F g}
  one_mem' := by intro g; rw [one_mul]
  mul_mem' := by
    intro a b ha hb g
    rw [mul_assoc,ha,hb]
  inv_mem' := by
    intro a ha g
    have he := ha (a⁻¹*g)
    rw [mul_inv_cancel_left] at he
    exact he.symm

theorem lower_invariant (N : ℕ) (hN : 0<N) (F : AsymptoticRationalGroup.Group → ℂ) (w : ℂ)
    (hp : ∀ n : ℤ,translationLabel (n:ℚ)∈invariantSubgroup F)
    (hw : ∀ g,w*F (frickeLabel N hN*g)=F g) (u : ℤ) :
    integralLabel (lowerSL N u)∈invariantSubgroup F := by
  intro g
  calc
    F (integralLabel (lowerSL N u)*g)=w*F (frickeLabel N hN*(integralLabel (lowerSL N u)*g)) := (hw _).symm
    _ = w*F (translationLabel (-(u:ℚ))*(frickeLabel N hN*g)) := by rw [← mul_assoc,fricke_lower,mul_assoc]
    _ = w*F (frickeLabel N hN*g) := by
      rw [← Int.cast_neg]
      rw [hp (-u) _]
    _ = F g := hw g

theorem invariance_of_reduction (N q : ℕ) (hN : 0<N) (γ : SL(2,ℤ))
    (a b c t u v : ℤ) (h : (q:ℤ)*c=(N:ℤ)*a*b+1)
    (he : lower N v * upper t * γ.val * upper u=canonicalEntries N q a b c)
    (F : AsymptoticRationalGroup.Group → ℂ) (w : ℂ)
    (hp : ∀ n : ℤ,translationLabel (n:ℚ)∈invariantSubgroup F)
    (hw : ∀ g,w*F (frickeLabel N hN*g)=F g)
    (hc : canonicalLabel N q a b c h∈invariantSubgroup F) :
    integralLabel γ∈invariantSubgroup F := by
  rw [← reduction_labels N q γ a b c t u v h he] at hc
  have hl := (invariantSubgroup F).mul_mem (lower_invariant N hN F w hp hw v) (hp t)
  exact ((invariantSubgroup F).mul_mem_cancel_left hl).mp
    (((invariantSubgroup F).mul_mem_cancel_right (hp u)).mp hc)

/-- On an actual counting vector, the untwisted compact equation and
all individual fresh-prime compact defects detect a matrix whose first
entry can be translated to q. Periodicity and weights are discharged
by the checked decoding formulas. -/
theorem decoded_generator_invariant (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)
    (γ : SL(2,ℤ)) (a₀ b₀ c₀ d₀ t₀ : ℤ)
    (hγ : γ.val=!![a₀,b₀;(N:ℤ)*c₀,d₀]) (hqeq : a₀+(N:ℤ)*c₀*t₀=(q:ℤ))
    (w : ℂ) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space)
    (hW : ∀ s : Set ℍ,∀ hs : IsCompact s,twist N 1 hN Nat.zero_lt_one w hs hε t x f=0)
    (hrows : ∀ i : Fin (q-1),∀ s : Set ℍ,∀ hs : IsCompact s,
      AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x f=0) :
    ∀ g : AsymptoticRationalGroup.Group,decode ε t x f (integralLabel γ*g)=decode ε t x f g := by
  have hdet : a₀*d₀-(N:ℤ)*c₀*b₀=1 := by
    have hd := γ.property
    rw [hγ,Matrix.det_fin_two] at hd
    change a₀*d₀-b₀*((N:ℤ)*c₀)=1 at hd
    nlinarith [hd]
  obtain ⟨a,b,c,u,v,ha,haq,hb,hbq,hc,he⟩ :=
    canonical_reduction N q (Fact.out : q.Prime).one_lt a₀ b₀ c₀ d₀ t₀ hdet hqeq
  have hw := (all_compact_untwisted_zero_iff N hN w hε t x f).mp hW
  exact invariance_of_reduction N q hN γ a b c t₀ u v hc
    (by simpa only [hγ] using he) (decode ε t x f) w
    (fun n g => decode_periodic ε t x f g n) hw
    (canonical_relation N q hN hq w hε t x f a b c ha haq hb hbq hc hrows hw)

#print axioms lower_invariant
#print axioms invariance_of_reduction
#print axioms decoded_generator_invariant

end AsymptoticDecodedCongruence
