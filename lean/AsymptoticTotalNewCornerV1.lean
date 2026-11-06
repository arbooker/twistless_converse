module

public import AsymptoticPrimeNewOperatorsV1
public import AsymptoticPrimeProductBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public section

namespace AsymptoticTotalNewCorner

open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticQuotientOperators
open AsymptoticLocalCongruence AsymptoticPolarIsometry AsymptoticRegularTrace
open AsymptoticSectorSigns UpperHalfPlane
open scoped lp

noncomputable instance countingTop_complete (N : ℕ) :
    CompleteSpace (⊤ : Submodule ℂ ℓ²(Classes (gamma N),ℂ)) := by
  change CompleteSpace (Set.univ : Set ℓ²(Classes (gamma N),ℂ))
  exact completeSpace_coe_iff_isComplete.mpr isComplete_univ

/-- Local new corner at a fixed level; primes away from the level impose
no condition. This gives one family on a single counting Hilbert space. -/
noncomputable def localSpace (N : ℕ) (hN : 0<N) (p : ℕ) :
    Submodule ℂ ℓ²(Classes (gamma N),ℂ) := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  exact if hp : p.Prime ∧ p∣N then
    newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hp.2))
      (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hp.2)) else ⊤

noncomputable instance localSpace_complete (N : ℕ) (hN : 0<N) (p : ℕ) :
    CompleteSpace (localSpace N hN p) := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  by_cases hp : p.Prime ∧ p∣N
  · have he : localSpace N hN p=newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hp.2))
        (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hp.2)) := by
      simp only [localSpace,dite_eq_left hp]
    exact he.symm ▸ (inferInstance : CompleteSpace
      (newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hp.2))
        (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hp.2))))
  · have he : localSpace N hN p=⊤ := by simp only [localSpace,dite_eq_right hp]
    exact he.symm ▸ countingTop_complete N

theorem localSpace_mul_eq (M p : ℕ) (hM : 0<M) (hp : p.Prime) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    localSpace (p*M) (Nat.mul_pos hp.pos hM) p=
      newSpace (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p)) := by
  classical
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  simp only [localSpace,dite_eq_left (show p.Prime ∧ p∣p*M from ⟨hp,Nat.dvd_mul_right p M⟩),
    Nat.mul_div_cancel_left M hp.pos]

theorem localSpace_supported (N : ℕ) (hN : 0<N) (p : ℕ) :
    Supported (gamma_le_projectiveOutside N hN {p}) (localSpace N hN p).starProjection := by
  classical
  by_cases hp : p.Prime ∧ p∣N
  · obtain ⟨hp,⟨M,rfl⟩⟩ := hp
    have hM : 0<M := by nlinarith
    let : NeZero (p*M) := ⟨hN.ne'⟩
    rw [starProjection_congr _ _ (localSpace_mul_eq M p hM hp)]
    exact prime_new_supported M p hM hp
  · have he : localSpace N hN p=⊤ := by simp only [localSpace,dite_eq_right hp]
    rw [starProjection_congr _ _ he,Submodule.starProjection_top]
    exact AsymptoticPartitionSupport.supported_one
      (forget (gamma_le_projectiveOutside N hN {p}))

theorem localSpace_equivariant (N : ℕ) (hN : 0<N) (p : ℕ) :
    Equivariant (localSpace N hN p).starProjection := by
  classical
  by_cases hp : p.Prime ∧ p∣N
  · obtain ⟨hp,⟨M,rfl⟩⟩ := hp
    have hM : 0<M := by nlinarith
    let : NeZero (p*M) := ⟨hN.ne'⟩
    rw [starProjection_congr _ _ (localSpace_mul_eq M p hM hp)]
    exact newSpace_equivariant _ _
  · have he : localSpace N hN p=⊤ := by simp only [localSpace,dite_eq_right hp]
    rw [starProjection_congr _ _ he,Submodule.starProjection_top]
    exact equivariant_one

/-- The common new corner in counting coordinates, including level one. -/
noncomputable def space (N : ℕ) (hN : 0<N) : Submodule ℂ ℓ²(Classes (gamma N),ℂ) :=
  ⨅ p : ℕ,localSpace N hN p

noncomputable instance space_complete (N : ℕ) (hN : 0<N) : CompleteSpace (space N hN) := by
  have hc : IsClosed (space N hN : Set ℓ²(Classes (gamma N),ℂ)) := by
    simp only [space,Submodule.coe_iInf]
    exact isClosed_iInter (fun p => (completeSpace_coe_iff_isComplete.mp
      (inferInstance : CompleteSpace (localSpace N hN p))).isClosed)
  exact completeSpace_coe_iff_isComplete.mpr hc.isComplete

theorem space_le_local (N : ℕ) (hN : 0<N) (p : ℕ) : space N hN≤localSpace N hN p := iInf_le _ p

theorem incidence_induction_mem (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e : Sector N) (x : ℍ) (f : ℓ²(Classes (gamma N),ℂ))
    (hf : AsymptoticCongruenceQuotient.induction N hε ht x f∈
      AsymptoticQuotientIncidence.space N hN hε ht e x) : f∈space N hN := by
  classical
  rw [space,Submodule.mem_iInf]
  intro p
  by_cases hp : p.Prime ∧ p∣N
  · obtain ⟨hp,⟨M,rfl⟩⟩ := hp
    have hM : 0<M := by nlinarith
    let : NeZero (p*M) := ⟨hN.ne'⟩
    rw [localSpace_mul_eq M p hM hp]
    exact incidence_induction_mem_prime_new M p hM hp hε ht e x f hf
  · simp only [localSpace,dite_eq_right hp,Submodule.mem_top]

/-- The common corner has at most the product of the actual prime-local
rooted coefficients. The empty product covers level one. -/
theorem diagonal_le_product (N : ℕ) (hN : 0<N) :
    (matrix (space N hN).starProjection (classOf (gamma N) 1) (classOf (gamma N) 1)).re≤
      ((N.primeFactors.toList).map (fun p =>
        (matrix (localSpace N hN p).starProjection (classOf (gamma N) 1) (classOf (gamma N) 1)).re)).prod :=
  prime_common_corner_diagonal_le N hN (localSpace N hN) (localSpace_supported N hN)
    (localSpace_equivariant N hN) (space N hN) N.primeFactors.toList
    N.primeFactors.nodup_toList (fun p _ => space_le_local N hN p)

#print axioms localSpace_mul_eq
#print axioms localSpace_supported
#print axioms localSpace_equivariant
#print axioms space_le_local
#print axioms incidence_induction_mem
#print axioms diagonal_le_product

end AsymptoticTotalNewCorner
