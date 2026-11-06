module

public import QuantitativeArithmeticCertificateV1
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Data.Nat.ChineseRemainder

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

/-- Dirichlet supplies a positive prime in C + A*Z for either sign of A.
Only A = 0 is excluded. The bound permits avoidance of any fixed finite set. -/
theorem exists_prime_shear (A C : ℤ) (hA : A ≠ 0) (hcop : IsCoprime C A)
    (bound : ℕ) : ∃ p : ℕ, bound < p ∧ p.Prime ∧ ∃ n : ℤ, (p : ℤ) = C+n*A := by
  have ha : A.natAbs ≠ 0 := by simpa using hA
  have hc : IsCoprime C (A.natAbs : ℤ) := by
    simpa [Int.natCast_natAbs] using hcop.abs_right
  obtain ⟨p, hpbound, hp, heq⟩ := Nat.forall_exists_prime_gt_and_zmodEq bound ha hc
  have hdiv : A ∣ (p : ℤ)-C := (Int.modEq_natAbs.mp heq).symm.dvd
  obtain ⟨n, hn⟩ := hdiv
  exact ⟨p, hpbound, hp, n, by nlinarith [hn]⟩

/-- Simultaneously choose distinct primes for any fixed finite family of
integer arithmetic progressions. This invokes Mathlib's proved Dirichlet theorem. -/
theorem exists_distinct_prime_shears {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A C : ι → ℤ) (hA : ∀ i, A i ≠ 0)
    (hcop : ∀ i, IsCoprime (C i) (A i)) (bound : ℕ) :
    ∃ p : ι → ℕ,
      (∀ i ∈ s, bound < p i ∧ (p i).Prime ∧ ∃ n : ℤ, (p i : ℤ) = C i+n*A i) ∧
      Set.InjOn p s := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 0, by simp, by simp [Set.InjOn]⟩
  | @insert i s hi ih =>
    obtain ⟨p, hp, hinj⟩ := ih
    obtain ⟨c, hc, hcprime, hn⟩ :=
      exists_prime_shear (A i) (C i) (hA i) (hcop i) (max bound (s.sup p))
    have hbound : bound < c := lt_of_le_of_lt (le_max_left _ _) hc
    have hlt (j : ι) (hj : j ∈ s) : p j < c :=
      lt_of_le_of_lt (Finset.le_sup hj) (lt_of_le_of_lt (le_max_right _ _) hc)
    refine ⟨Function.update p i c, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using And.intro hbound (And.intro hcprime hn)
      · have hji : j ≠ i := by intro h; subst j; exact hi hj
        simpa [Function.update_of_ne hji] using hp j hj
    · intro j hj k hk heq
      by_cases hji : j = i
      · subst j
        by_cases hki : k = i
        · exact hki.symm
        · have hks : k ∈ s := (Finset.mem_insert.mp hk).resolve_left hki
          have he : c = p k := by simpa [Function.update_of_ne hki] using heq
          exact False.elim ((ne_of_lt (hlt k hks)) he.symm)
      · by_cases hki : k = i
        · subst k
          have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hji
          have he : p j = c := by simpa [Function.update_of_ne hji] using heq
          exact False.elim ((ne_of_lt (hlt j hjs)) he)
        · exact hinj ((Finset.mem_insert.mp hj).resolve_left hji)
            ((Finset.mem_insert.mp hk).resolve_left hki)
            (by simpa [Function.update_of_ne hji, Function.update_of_ne hki] using heq)

/-- A positive integral CRT representative for a finite family, allowing
negative residues. All moduli are positive and pairwise coprime. -/
theorem exists_positive_integer_crt {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise fun i j => (m i).Coprime (m j)) :
    ∃ Q : ℤ, 0 < Q ∧ ∀ i, (m i : ℤ) ∣ Q-a i := by
  classical
  let r : ι → ℕ := fun i => (a i % (m i : ℤ)).toNat
  let k := Nat.chineseRemainderOfFinset r m Finset.univ
    (fun i _ => ne_of_gt (hm i)) (fun i _ j _ hij => hcop hij)
  let P : ℕ := ∏ i, m i
  have hP : 0 < P := Finset.prod_pos (fun i _ => hm i)
  refine ⟨((k.val+P : ℕ) : ℤ), by exact_mod_cast (by omega : 0 < k.val+P), ?_⟩
  intro i
  have hk : (k.val : ℤ) ≡ (r i : ℤ) [ZMOD (m i : ℤ)] :=
    Int.natCast_modEq_iff.mpr (k.property i (Finset.mem_univ i))
  have hr : (r i : ℤ) ≡ a i [ZMOD (m i : ℤ)] := by
    dsimp [r]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast ne_of_gt (hm i)))]
    simp [Int.ModEq]
  have hdivP : m i ∣ P := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hdivP' : (m i : ℤ) ∣ (P : ℤ) := by exact_mod_cast hdivP
  have hshift : (k.val : ℤ)+(P : ℤ) ≡ (k.val : ℤ) [ZMOD (m i : ℤ)] :=
    Int.add_modEq_left_iff.mpr hdivP'
  simpa using (hshift.trans (hk.trans hr)).symm.dvd

/-- The full fixed arithmetic preparation: distinct prime lower-left
coefficients, a positive common upper-left entry, and both integral shears.
The prime coefficients avoid N*Q. Negative nonzero original A_i are allowed. -/
theorem exists_fixed_certificate_preparation {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (a : ℤ) (A C : ι → ℤ)
    (hA : ∀ i, A i ≠ 0) (hcop : ∀ i, IsCoprime (C i) (A i))
    (hres : ∀ i, (N : ℤ) ∣ A i-a) :
    ∃ (p : ι → ℕ) (n t : ι → ℤ) (Q : ℤ),
      0 < Q ∧ Function.Injective p ∧ (N : ℤ) ∣ Q-a ∧
      ∀ i, (p i).Prime ∧ N < p i ∧ (p i : ℤ) = C i+n i*A i ∧
        Q = A i+(N : ℤ)*(p i : ℤ)*t i ∧ ¬(p i : ℤ) ∣ (N : ℤ)*Q := by
  classical
  let bound := max N (Finset.univ.sup fun i => (A i).natAbs)
  obtain ⟨p, hp, hinj⟩ := exists_distinct_prime_shears Finset.univ A C hA hcop bound
  have hp' (i : ι) := hp i (Finset.mem_univ i)
  have hinj' : Function.Injective p := by simpa using hinj
  have hpN (i : ι) : N < p i := lt_of_le_of_lt (le_max_left _ _) (hp' i).1
  have hpA (i : ι) : (A i).natAbs < p i :=
    lt_of_le_of_lt (Finset.le_sup (f := fun j => (A j).natAbs) (Finset.mem_univ i))
      (lt_of_le_of_lt (le_max_right _ _) (hp' i).1)
  have hNp (i : ι) : N.Coprime (p i) := by
    apply Nat.Coprime.symm
    apply (hp' i).2.1.coprime_iff_not_dvd.mpr
    intro hd
    exact (not_le_of_gt (hpN i)) (Nat.le_of_dvd hN hd)
  let m : Option ι → ℕ := fun j => j.elim N p
  let b : Option ι → ℤ := fun j => j.elim a A
  have hm : ∀ j, 0 < m j := by
    intro j
    cases j with
    | none => exact hN
    | some i => exact (hp' i).2.1.pos
  have hmco : Pairwise fun i j => (m i).Coprime (m j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact hNp j
    | some i =>
      cases j with
      | none => exact (hNp i).symm
      | some j =>
        apply (Nat.coprime_primes (hp' i).2.1 (hp' j).2.1).mpr
        intro he
        exact hij (congrArg some (hinj' he))
  obtain ⟨Q, hQ, hcrt⟩ := exists_positive_integer_crt m b hm hmco
  have hQN : (N : ℤ) ∣ Q-a := hcrt none
  have hQp (i : ι) : (p i : ℤ) ∣ Q-A i := hcrt (some i)
  have hNdiff (i : ι) : (N : ℤ) ∣ Q-A i := by
    convert dvd_sub hQN (hres i) using 1
    ring
  have ht (i : ι) : ∃ t : ℤ, Q = A i+(N : ℤ)*(p i : ℤ)*t := by
    obtain ⟨t, ht⟩ := (hNp i).isCoprime.mul_dvd (hNdiff i) (hQp i)
    exact ⟨t, by linarith⟩
  choose t ht using ht
  choose n hn using fun i => (hp' i).2.2
  refine ⟨p, n, t, Q, hQ, hinj', hQN, ?_⟩
  intro i
  refine ⟨(hp' i).2.1, hpN i, hn i, ht i, ?_⟩
  intro hdiv
  have hpz : Prime (p i : ℤ) := Nat.prime_iff_prime_int.mp (hp' i).2.1
  rcases hpz.dvd_mul.mp hdiv with hdN | hdQ
  · have hn : p i ∣ N := by exact_mod_cast hdN
    exact (not_le_of_gt (hpN i)) (Nat.le_of_dvd hN hn)
  · have hdA : (p i : ℤ) ∣ A i := by
      convert dvd_sub hdQ (hQp i) using 1
      ring
    have hdA' : p i ∣ (A i).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hdA
    exact (not_le_of_gt (hpA i)) (Nat.le_of_dvd (Int.natAbs_pos.mpr (hA i)) hdA')

#print axioms exists_prime_shear
#print axioms exists_distinct_prime_shears
#print axioms exists_positive_integer_crt
#print axioms exists_fixed_certificate_preparation

end QuantitativeArithmetic
