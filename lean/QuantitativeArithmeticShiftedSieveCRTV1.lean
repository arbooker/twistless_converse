module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticShiftedSieveCRT
open scoped BigOperators

/-- Excluding zero and one nonzero residue removes exactly two classes. -/
theorem local_avoidance_card (p : ℕ) (hp : p.Prime) (q : ZMod p) (hq : q ≠ 0) :
    Nat.card {x : ZMod p // x ≠ 0 ∧ x ≠ q} = p-2 := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card]
  have he : {x : ZMod p // x ≠ 0 ∧ x ≠ q} ≃
      {x : ZMod p // ¬(x=0 ∨ x=q)} := Equiv.subtypeEquivRight (by simp)
  rw [Fintype.card_congr he, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq_or_eq_of_ne hq.symm, ZMod.card]

/-- CRT transports any coordinatewise finite sieve condition exactly. -/
theorem crt_predicate_card {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (P : ∀ i, ZMod (p i) → Prop) :
    Nat.card {x : ZMod (∏ i, p i) //
      ∀ i, P i (ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i)) x)} =
      ∏ i, Nat.card {x : ZMod (p i) // P i x} := by
  classical
  let e := ZMod.prodEquivPi p hcop
  have he : {x : ZMod (∏ i, p i) //
      ∀ i, P i (ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i)) x)} ≃
      {f : ∀ i, ZMod (p i) // ∀ i, P i (f i)} :=
    e.toEquiv.subtypeEquiv (by
      intro x
      change (∀ i, P i _) ↔ ∀ i, P i (ZMod.prodEquivPi p hcop x i)
      simp only [ZMod.prodEquivPi_apply])
  rw [Nat.card_congr (he.trans Equiv.subtypePiEquivPi), Nat.card_pi]

/-- Exact count of classes avoiding both 0 and Q at each distinct prime. -/
theorem avoidance_card {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) (Q : ℤ)
    (hQ : ∀ i, (Q : ZMod (p i)) ≠ 0) :
    Nat.card {x : ZMod (∏ i, p i) //
      ∀ i, let xi := ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i)) x
        xi ≠ 0 ∧ xi ≠ (Q : ZMod (p i))} = ∏ i, (p i-2) := by
  calc
    _ = ∏ i, Nat.card {x : ZMod (p i) // x ≠ 0 ∧ x ≠ (Q : ZMod (p i))} :=
      crt_predicate_card p hcop (fun i x => x ≠ 0 ∧ x ≠ (Q : ZMod (p i)))
    _ = _ := Finset.prod_congr rfl (fun i _ => local_avoidance_card (p i) (hp i) Q (hQ i))

/-- A class modulo the squarefree product is a unit exactly when every
prime coordinate is nonzero. -/
theorem isUnit_iff_coordinates {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j)))
    (x : ZMod (∏ i, p i)) :
    IsUnit x ↔ ∀ i, ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i)) x ≠ 0 := by
  rw [← MulEquiv.isUnit_map (ZMod.prodEquivPi p hcop), Pi.isUnit_iff]
  apply forall_congr'
  intro i
  let : Fact (p i).Prime := ⟨hp i⟩
  rw [isUnit_iff_ne_zero, ZMod.prodEquivPi_apply]

/-- The literal reduced residue classes allowed by the finite shifted sieve. -/
def AllowedUnits {ι : Type*} [Fintype ι] (p : ι → ℕ) (Q : ℤ) :=
  {u : (ZMod (∏ i, p i))ˣ // ∀ i,
    ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i)) (u : ZMod (∏ i, p i)) ≠
      (Q : ZMod (p i))}

theorem allowedUnits_card {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) (Q : ℤ)
    (hQ : ∀ i, (Q : ZMod (p i)) ≠ 0) :
    Nat.card (AllowedUnits p Q) = ∏ i, (p i-2) := by
  classical
  let f : AllowedUnits p Q → {x : ZMod (∏ i, p i) //
      ∀ i, let xi := ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i)) x
        xi ≠ 0 ∧ xi ≠ (Q : ZMod (p i))} := fun u =>
    ⟨u.val, fun i => ⟨(isUnit_iff_coordinates p hp hcop u.val).mp u.val.isUnit i, u.property i⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val huv
    · intro x
      have hu : IsUnit x.val := (isUnit_iff_coordinates p hp hcop x.val).mpr (fun i => (x.property i).1)
      obtain ⟨u,hu⟩ := hu
      refine ⟨⟨u, ?_⟩, ?_⟩
      · intro i
        simpa only [hu] using (x.property i).2
      · apply Subtype.ext
        exact hu
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  exact avoidance_card p hp hcop Q hQ

theorem units_card {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) :
    Nat.card (ZMod (∏ i, p i))ˣ = ∏ i, (p i-1) := by
  rw [Nat.card_congr (Units.mapEquiv (ZMod.prodEquivPi p hcop).toMulEquiv).toEquiv,
    Nat.card_congr MulEquiv.piUnits.toEquiv, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  let : NeZero (p i) := ⟨(hp i).ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (hp i)]

/-- The exact relative density among reduced residue classes. -/
theorem allowedUnits_proportion {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) (Q : ℤ)
    (hQ : ∀ i, (Q : ZMod (p i)) ≠ 0) :
    (Nat.card (AllowedUnits p Q) : ℝ) / (Nat.card (ZMod (∏ i, p i))ˣ : ℝ) =
      ∏ i, (1-1/((p i : ℝ)-1)) := by
  rw [allowedUnits_card p hp hcop Q hQ, units_card p hp hcop]
  simp only [Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have h2 := (hp i).two_le
  have h1 : 1 ≤ p i := by omega
  rw [Nat.cast_sub h2, Nat.cast_sub h1]
  push_cast
  have hd : (p i : ℝ)-1 ≠ 0 := by exact_mod_cast (show (p i : ℤ)-1 ≠ 0 by omega)
  field_simp
  ring

/-- The same exact proportion with Euler's totient as denominator. -/
theorem allowedUnits_totient_proportion {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => Nat.Coprime (p i) (p j))) (Q : ℤ)
    (hQ : ∀ i, (Q : ZMod (p i)) ≠ 0) :
    (Nat.card (AllowedUnits p Q) : ℝ) / (Nat.totient (∏ i, p i) : ℝ) =
      ∏ i, (1-1/((p i : ℝ)-1)) := by
  let : NeZero (∏ i, p i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)⟩
  have he := allowedUnits_proportion p hp hcop Q hQ
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using he

/-- An additional fixed residue at a coprime modulus costs exactly one
coordinate: the remaining sieve count is unchanged under the literal CRT. -/
theorem fixed_residue_card (M R : ℕ) (hMR : M.Coprime R)
    (a : ZMod M) (P : ZMod R → Prop) :
    Nat.card {x : ZMod (M*R) // (ZMod.chineseRemainder hMR x).1=a ∧
      P (ZMod.chineseRemainder hMR x).2} = Nat.card {x : ZMod R // P x} := by
  let e := ZMod.chineseRemainder hMR
  let f : {x : ZMod (M*R) // (e x).1=a ∧ P (e x).2} ≃ {x : ZMod R // P x} :=
    { toFun := fun x => ⟨(e x.val).2,x.property.2⟩
      invFun := fun y => ⟨e.symm (a,y.val),by simp [y.property]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply e.injective
        simp only [e.apply_symm_apply]
        exact Prod.ext x.property.1.symm rfl
      right_inv := by intro y; apply Subtype.ext; simp }
  exact Nat.card_congr f

/-- Specialization to a finite set of distinct auxiliary primes. -/
theorem finset_allowedUnits_card (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime)
    (Q : ℤ) (hQ : ∀ p ∈ S, ¬ (p : ℤ) ∣ Q) :
    Nat.card (AllowedUnits (fun p : S => (p : ℕ)) Q) = ∏ p ∈ S, (p-2) := by
  have hcop : Pairwise (fun i j : S => Nat.Coprime (i : ℕ) (j : ℕ)) := by
    intro i j hij
    exact (hp i i.property).coprime_iff_not_dvd.mpr (by
      intro hdiv
      have he := (Nat.dvd_prime (hp j j.property)).mp hdiv
      rcases he with he | he
      · exact (hp i i.property).ne_one he
      · exact hij (Subtype.ext he))
  have hn (i : S) : (Q : ZMod (i : ℕ)) ≠ 0 := by
    intro hz
    exact hQ i i.property ((ZMod.intCast_zmod_eq_zero_iff_dvd Q (i : ℕ)).mp hz)
  calc
    _ = ∏ i : S, ((i : ℕ)-2) := allowedUnits_card (fun i : S => (i : ℕ)) (fun i => hp i i.property) hcop Q hn
    _ = _ := Finset.prod_coe_sort S (fun i : ℕ => i-2)

#print axioms fixed_residue_card
#print axioms allowedUnits_totient_proportion
#print axioms allowedUnits_proportion
#print axioms finset_allowedUnits_card
#print axioms allowedUnits_card
#print axioms avoidance_card
#print axioms crt_predicate_card
end QuantitativeArithmeticShiftedSieveCRT
