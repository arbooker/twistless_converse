module

public import AsymptoticQuotientProductBoundV1
public import AsymptoticLocalOldGroupsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticLocalCongruence

open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticRegularTrace
open AsymptoticQuotientOperators
open scoped lp

theorem single_prime_meet_complement (N p : ℕ) (hN : 0<N) :
    projectiveOutside N {p}⊓projectiveOutside N ({p}:Set ℕ)ᶜ≤gamma N := by
  rw [projectiveOutside_disjoint N hN disjoint_compl_right]

theorem other_prime_le_complement (N p q : ℕ) (hpq : q≠p) :
    projectiveOutside N {q}≤projectiveOutside N ({p}:Set ℕ)ᶜ := by
  apply projectiveOutside_mono
  intro r hr
  have hrq : r=q := Set.mem_singleton_iff.mp hr
  simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,hrq] using hpq

/-- Concrete prime separation factors the full coset operator product.
The groups and their intersection are the literal rational congruence
groups; no abstract local-independence assumption is supplied. -/
theorem prime_word_norm_sq (N : ℕ) (hN : 0<N)
    (B : ℕ → ℓ²(Classes (gamma N),ℂ) →L[ℂ] ℓ²(Classes (gamma N),ℂ))
    (hs : ∀ p,Supported (gamma_le_projectiveOutside N hN {p}) (B p))
    (he : ∀ p,Equivariant (B p)) (ps : List ℕ) (hp : ps.Nodup) :
    ‖word B ps (delta (classOf (gamma N) 1))‖^2=
      (ps.map (fun p => ‖B p (delta (classOf (gamma N) 1))‖^2)).prod :=
  word_norm_sq (fun p => projectiveOutside N {p})
    (fun p => projectiveOutside N ({p}:Set ℕ)ᶜ)
    (fun p => gamma_le_projectiveOutside N hN {p})
    (fun p => gamma_le_projectiveOutside N hN ({p}:Set ℕ)ᶜ)
    (fun p => single_prime_meet_complement N p hN)
    (fun p q hpq => other_prime_le_complement N p q hpq) B hs he ps hp

/-- The product upper bound for any common corner of the concrete local
prime-supported projections. It remains valid without their commutation. -/
theorem prime_common_corner_diagonal_le (N : ℕ) (hN : 0<N)
    (V : ℕ → Submodule ℂ ℓ²(Classes (gamma N),ℂ)) [∀ p,CompleteSpace (V p)]
    (hs : ∀ p,Supported (gamma_le_projectiveOutside N hN {p}) (V p).starProjection)
    (he : ∀ p,Equivariant (V p).starProjection)
    (U : Submodule ℂ ℓ²(Classes (gamma N),ℂ)) [CompleteSpace U]
    (ps : List ℕ) (hp : ps.Nodup) (hUV : ∀ p∈ps,U≤V p) :
    (matrix U.starProjection (classOf (gamma N) 1) (classOf (gamma N) 1)).re≤
      (ps.map (fun p => (matrix (V p).starProjection (classOf (gamma N) 1)
        (classOf (gamma N) 1)).re)).prod :=
  common_corner_diagonal_le (fun p => projectiveOutside N {p})
    (fun p => projectiveOutside N ({p}:Set ℕ)ᶜ)
    (fun p => gamma_le_projectiveOutside N hN {p})
    (fun p => gamma_le_projectiveOutside N hN ({p}:Set ℕ)ᶜ)
    (fun p => single_prime_meet_complement N p hN)
    (fun p q hpq => other_prime_le_complement N p q hpq) V hs he U ps hp hUV

#print axioms single_prime_meet_complement
#print axioms other_prime_le_complement
#print axioms prime_word_norm_sq
#print axioms prime_common_corner_diagonal_le

end AsymptoticLocalCongruence
