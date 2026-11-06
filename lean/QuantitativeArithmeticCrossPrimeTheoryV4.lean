module

public import AsymptoticLocalOldGroupsV1
public import AsymptoticRepeatedJoinIndexV1
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite

/-! Consolidated chapter: QuantitativeArithmeticCrossPrime. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticCrossPrimeIndexV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticCrossPrime

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Equality of the actual finite coset counts makes the natural inclusion
of coset sets surjective, and hence supplies literal product factors. -/
theorem factor_of_relIndex_eq (H K L : Subgroup G) (hKL : K≤L)
    (hi : H.relIndex K=H.relIndex L) (hn : H.relIndex L≠0)
    (g : G) (hg : g∈L) : ∃ k∈K, ∃ h∈H, g=k*h := by
  let : Finite (L ⧸ H.subgroupOf L) := Nat.finite_of_card_ne_zero hn
  let e := Subgroup.quotientSubgroupOfEmbeddingOfLE H hKL
  have hs : Function.Surjective e :=
    ((Nat.bijective_iff_injective_and_card e).mpr ⟨e.injective,hi⟩).2
  obtain ⟨c,hc⟩ := hs (QuotientGroup.mk (⟨g,hg⟩ : L))
  induction c using Quotient.inductionOn with
  | h k =>
    change (QuotientGroup.mk (⟨k.val,hKL k.property⟩ : L) : L ⧸ H.subgroupOf L)=
      QuotientGroup.mk (⟨g,hg⟩ : L) at hc
    have he : (k.val)⁻¹*g∈H := by
      have heL := QuotientGroup.eq.mp hc
      exact heL
    refine ⟨k.val,k.property,k.val⁻¹*g,he,?_⟩
    simp only [mul_inv_cancel_left]

/-- Finite-index arithmetic equality implies actual subgroup permutability,
not merely an equality of rooted traces. -/
theorem permutes_of_relIndex_eq (H K L : Subgroup G) (hHL : H≤L) (hKL : K≤L)
    (hi : H.relIndex K=H.relIndex L) (hn : H.relIndex L≠0) :
    (H:Set G)*(K:Set G)=(K:Set G)*(H:Set G) := by
  apply Set.Subset.antisymm
  · rintro g ⟨h,hh,k,hk,rfl⟩
    obtain ⟨k',hk',h',hh',he⟩ := factor_of_relIndex_eq H K L hKL hi hn (h*k)
      (L.mul_mem (hHL hh) (hKL hk))
    exact ⟨k',hk',h',hh',he.symm⟩
  · rintro g ⟨k,hk,h,hh,rfl⟩
    obtain ⟨k',hk',h',hh',he⟩ := factor_of_relIndex_eq H K L hKL hi hn (k*h)⁻¹
      (L.inv_mem (L.mul_mem (hKL hk) (hHL hh)))
    refine ⟨h'⁻¹,H.inv_mem hh',k'⁻¹,K.inv_mem hk',?_⟩
    have he' := congrArg Inv.inv he
    simpa only [_root_.mul_inv_rev,inv_inv] using he'.symm

/-- Permutability is preserved by actual homomorphisms, including Fricke conjugation. -/
theorem permutes_map {G' : Type*} [Group G'] (H K : Subgroup G) (f : G→*G')
    (h : (H:Set G)*(K:Set G)=(K:Set G)*(H:Set G)) :
    (H.map f:Set G')*(K.map f:Set G')=(K.map f:Set G')*(H.map f:Set G') := by
  change (f '' (H:Set G))*(f '' (K:Set G))=(f '' (K:Set G))*(f '' (H:Set G))
  simpa only [← Set.image_mul] using congrArg (fun s : Set G => f '' s) h

#print axioms factor_of_relIndex_eq
#print axioms permutes_of_relIndex_eq
#print axioms permutes_map

end QuantitativeArithmeticCrossPrime
end
end

/-! ## QuantitativeArithmeticCrossPrimeCoreV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticCrossPrime

open AsymptoticCongruenceStrip AsymptoticLocalCongruence AsymptoticRamifiedCosets
open scoped Pointwise

/-- Different-prime support forces the literal intersection, including
projective scalar identifications. -/
theorem supported_intersection (N p q : ℕ) (hN : 0<N) (hpq : p≠q)
    (A B : Subgroup AsymptoticRationalGroup.Group)
    (hA : A≤projectiveOutside N {p}) (hB : B≤projectiveOutside N {q})
    (hHA : gamma N≤A) (hHB : gamma N≤B) : A⊓B=gamma N := by
  apply le_antisymm
  · have hd : Disjoint ({p}:Set ℕ) {q} := by simpa using hpq
    exact (inf_le_inf hA hB).trans (le_of_eq (projectiveOutside_disjoint N hN hd))
  · exact le_inf hHA hHB

theorem gamma_gamma_intersection (M p q : ℕ) (hM : 0<M) (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) : gamma (q*M)⊓gamma (p*M)=gamma (p*(q*M)) := by
  apply supported_intersection (p*(q*M)) p q (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hpq
  · exact gamma_lower_le_projectiveOutside (q*M) p (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hp
  · simpa only [Nat.mul_left_comm] using gamma_lower_le_projectiveOutside (p*M) q (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hq
  · exact gamma_le_of_dvd (Nat.dvd_mul_left (q*M) p)
  · apply gamma_le_of_dvd
    exact ⟨q,by ring⟩

theorem gamma_degeneracy_intersection (M p q : ℕ) (hM : 0<M) (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) : gamma (q*M)⊓degeneracyGroup (p*M) q hq.pos=gamma (p*(q*M)) := by
  apply supported_intersection (p*(q*M)) p q (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hpq
  · exact gamma_lower_le_projectiveOutside (q*M) p (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hp
  · simpa only [Nat.mul_left_comm] using degeneracy_le_projectiveOutside (p*M) q (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hq
  · exact gamma_le_of_dvd (Nat.dvd_mul_left (q*M) p)
  · simpa only [Nat.mul_left_comm] using gamma_le_degeneracyGroup (p*M) q (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hq.pos

/-- The q-index is unaffected by multiplying the base level by a different
prime, even if either prime already occurs repeatedly in the level. -/
theorem prime_index_stable (M p q : ℕ) (hM : 0<M) (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) :
    (gamma (q*(p*M))).relIndex (gamma (p*M))=(gamma (q*M)).relIndex (gamma M) := by
  have hqp : ¬q∣p := by
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  by_cases hd : q∣M
  · rw [projective_index (p*M) q (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hq.pos (dvd_mul_of_dvd_right hd p),
      projective_index M q hM hq.pos hd]
  · have hd' : ¬q∣p*M := fun h => (hq.dvd_mul.mp h).elim hqp hd
    rw [projective_index_coprime (p*M) q (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hq (hq.coprime_iff_not_dvd.mpr hd'),
      projective_index_coprime M q hM hq (hq.coprime_iff_not_dvd.mpr hd)]

theorem prime_index_ne_zero (M q : ℕ) (hM : 0<M) (hq : q.Prime) :
    (gamma (q*M)).relIndex (gamma M)≠0 := by
  by_cases hd : q∣M
  · rw [projective_index M q hM hq.pos hd]
    exact hq.ne_zero
  · rw [projective_index_coprime M q hM hq (hq.coprime_iff_not_dvd.mpr hd)]
    omega

/-- Actual first-old subgroups at distinct primes permute. -/
theorem gamma_gamma_permute (M p q : ℕ) (hM : 0<M) (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) :
    (gamma (q*M):Set AsymptoticRationalGroup.Group)*(gamma (p*M):Set AsymptoticRationalGroup.Group)=
      (gamma (p*M):Set AsymptoticRationalGroup.Group)*(gamma (q*M):Set AsymptoticRationalGroup.Group) := by
  apply permutes_of_relIndex_eq _ _ (gamma M)
    (gamma_le_of_dvd (Nat.dvd_mul_left M q)) (gamma_le_of_dvd (Nat.dvd_mul_left M p))
  · rw [← Subgroup.inf_relIndex_right,gamma_gamma_intersection M p q hM hp hq hpq]
    simpa only [Nat.mul_left_comm] using prime_index_stable M p q hM hp hq hpq
  · exact prime_index_ne_zero M q hM hq

/-- The mixed first-old/second-old subgroups also permute. The containing
subgroup is the actual lower degeneracy group, so no strong approximation
or abstract direct-product premise is introduced. -/
theorem gamma_degeneracy_permute (M p q : ℕ) (hM : 0<M) (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) :
    (gamma (q*M):Set AsymptoticRationalGroup.Group)*
      (degeneracyGroup (p*M) q hq.pos:Set AsymptoticRationalGroup.Group)=
    (degeneracyGroup (p*M) q hq.pos:Set AsymptoticRationalGroup.Group)*
      (gamma (q*M):Set AsymptoticRationalGroup.Group) := by
  apply permutes_of_relIndex_eq _ _ (degeneracyGroup M q hq.pos)
    (gamma_le_degeneracyGroup M q hM hq.pos)
    (degeneracyGroup_mono hq.pos (Nat.dvd_mul_left M p))
  · rw [← Subgroup.inf_relIndex_right,gamma_degeneracy_intersection M p q hM hp hq hpq,
      lower_degeneracy_index M q hM hq.pos]
    rw [show p*(q*M)=q*(p*M) by ring,degeneracyGroup_index (p*M) q (by have hp0 := hp.pos; have hq0 := hq.pos; positivity) hq.pos]
    exact prime_index_stable M p q hM hp hq hpq
  · rw [lower_degeneracy_index M q hM hq.pos]
    exact prime_index_ne_zero M q hM hq

#print axioms gamma_gamma_permute
#print axioms gamma_degeneracy_permute

end QuantitativeArithmeticCrossPrime
end
end
