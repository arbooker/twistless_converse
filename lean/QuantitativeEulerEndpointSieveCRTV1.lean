module

public import QuantitativeArithmeticShiftedSieveProgressionV1
public import Mathlib.Data.ZMod.QuotientRing

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve
open Finset Nat QuantitativeArithmeticShiftedSieveProgression

/-- Any finite union of residue classes has discrepancy at most its number
of classes. Unlike the existing one-class lemma this applies to the actual
extra forbidden residues in a growing Selberg sieve. -/
theorem count_period_error_general (P : ℕ → Prop) [DecidablePred P]
    (m x : ℕ) (hm : 0<m) (hper : Function.Periodic P m) :
    |(Nat.count P x : ℝ)-(x : ℝ)*(Nat.count P m : ℝ)/(m : ℝ)|≤Nat.count P m := by
  have he : Nat.count P x=(x/m)*Nat.count P m+Nat.count P (x%m) := by
    conv_lhs => rw [← Nat.div_add_mod x m]
    rw [Nat.count_add,count_period_mul P m hper]
    congr 1
    congr 1
    funext n
    simpa only [Nat.nsmul_eq_mul,Nat.mul_comm,Nat.add_comm] using hper.nsmul (x/m) n
  have hrem := (Nat.count_monotone P) (Nat.mod_lt x hm).le
  have hx : (x : ℝ)=(m : ℝ)*(x/m : ℕ)+(x%m : ℕ) := by
    exact_mod_cast (Nat.div_add_mod x m).symm
  have hmod : ((x%m : ℕ) : ℝ)≤m := by exact_mod_cast (Nat.mod_lt x hm).le
  have h0 : (0 : ℝ)≤(x%m : ℕ) := by positivity
  have hc0 : (0 : ℝ)≤(Nat.count P (x%m) : ℕ) := by positivity
  have hc : ((Nat.count P (x%m) : ℕ) : ℝ)≤Nat.count P m := by exact_mod_cast hrem
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hcR : (Nat.count P x : ℝ)=(x/m : ℕ)*(Nat.count P m : ℝ)+Nat.count P (x%m) := by
    exact_mod_cast he
  have hlo : (x/m : ℕ)*(Nat.count P m : ℝ)≤(x : ℝ)*(Nat.count P m : ℝ)/m := by
    apply (le_div_iff₀ hmR).mpr
    nlinarith [mul_nonneg h0 (Nat.cast_nonneg (Nat.count P m) : (0 : ℝ)≤Nat.count P m)]
  have hhi : (x : ℝ)*(Nat.count P m : ℝ)/m≤
      (x/m : ℕ)*(Nat.count P m : ℝ)+Nat.count P m := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmod (Nat.cast_nonneg (Nat.count P m) : (0 : ℝ)≤Nat.count P m)]
  rw [abs_le]
  constructor <;> linarith

/-- Exact identification of one complete natural period with the residue
ring, for an arbitrary predicate on residues. -/
theorem count_cast_period (m : ℕ) [NeZero m] (P : ZMod m → Prop) [DecidablePred P] :
    Nat.count (fun n : ℕ => P (n : ZMod m)) m=Fintype.card {r : ZMod m // P r} := by
  rw [Nat.count_eq_card_filter_range,Fintype.card_subtype]
  apply card_bij (fun (n : ℕ) _ => (n : ZMod m))
  · intro n hn
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hn).2⟩
  · intro a ha b hb hab
    have ha' := mem_range.mp (mem_filter.mp ha).1
    have hb' := mem_range.mp (mem_filter.mp hb).1
    simpa only [ZMod.val_natCast_of_lt ha',ZMod.val_natCast_of_lt hb'] using congrArg ZMod.val hab
  · intro r hr
    refine ⟨r.val,mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt r),?_⟩,?_⟩
    · simpa only [ZMod.natCast_zmod_val] using (mem_filter.mp hr).2
    · exact ZMod.natCast_zmod_val r

/-- CRT counts every local residue choice exactly once. -/
theorem crt_residue_card {ι : Type*} [Fintype ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (R : ∀ i, Finset (ZMod (m i))) :
    Fintype.card {r : ZMod (∏ i, m i) // ∀ i, (ZMod.prodEquivPi m hcop r) i∈R i}=
      ∏ i, (R i).card := by
  classical
  let e := (ZMod.prodEquivPi m hcop).toEquiv
  let e' : {r : ZMod (∏ i, m i) // ∀ i, e r i∈R i} ≃
      {f : ∀ i, ZMod (m i) // ∀ i, f i∈R i} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  have h := Fintype.card_congr (e'.trans Equiv.subtypePiEquivPi)
  simpa [e] using h

/-- Exact complete-period count for the literal local congruence conditions. -/
theorem crt_period_count {ι : Type*} [Fintype ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (R : ∀ i, Finset (ZMod (m i))) :
    Nat.count (fun n : ℕ => ∀ i, (n : ZMod (m i))∈R i) (∏ i, m i)=∏ i, (R i).card := by
  classical
  have h := count_cast_period (∏ i, m i)
    (fun r : ZMod (∏ i, m i) => ∀ i, (ZMod.prodEquivPi m hcop r) i∈R i)
  rw [crt_residue_card] at h
  simpa only [map_natCast,Pi.natCast_apply] using h


/-- Literal residue conditions on a finite interval, with discrepancy at
most the exact CRT residue count. All constants are independent of how
large the product modulus is. -/
theorem crt_count_error {ι : Type*} [Fintype ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (R : ∀ i, Finset (ZMod (m i))) (x : ℕ) :
    |(Nat.count (fun n : ℕ => ∀ i, (n : ZMod (m i))∈R i) x : ℝ)-
      (x : ℝ)*(∏ i, ((R i).card : ℝ))/(∏ i, (m i : ℝ))|≤
        ∏ i, ((R i).card : ℝ) := by
  classical
  have hper : Function.Periodic (fun n : ℕ => ∀ i, (n : ZMod (m i))∈R i) (∏ i, m i) := by
    intro n
    have hcast (i : ι) : ((∏ j, m j : ℕ) : ZMod (m i))=0 := by
      apply (CharP.cast_eq_zero_iff (ZMod (m i)) (m i) _).mpr
      exact dvd_prod_of_mem m (mem_univ i)
    simp only [Nat.cast_add,hcast,add_zero]
  have h := count_period_error_general _ (∏ i, m i) x (NeZero.pos _) hper
  rw [crt_period_count m hcop R] at h
  simpa only [Nat.cast_prod] using h

def twoResidues (m Q : ℕ) (active : Prop) [Decidable active] : Finset (ZMod m) :=
  if active then {0,(Q : ZMod m)} else {0}

theorem twoResidues_card (m Q : ℕ) (active : Prop) [Decidable active]
    (hQ : active → (Q : ZMod m)≠0) :
    (twoResidues m Q active).card=if active then 2 else 1 := by
  by_cases ha : active
  · have hn := hQ ha
    simp [twoResidues,ha,Ne.symm hn]
  · simp [twoResidues,ha]

/-- The two actual forbidden residues give density 2/p exactly, while
inactive primes give density 1/p. CRT and the finite-interval discrepancy
are both proved; no residue-counting hypothesis is assumed. -/
theorem two_residue_count_error {ι : Type*} [Fintype ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (Q x : ℕ) (active : ι → Prop) [DecidablePred active]
    (hQ : ∀ i, active i → (Q : ZMod (m i))≠0) :
    |(Nat.count (fun n : ℕ => ∀ i, (n : ZMod (m i))=0 ∨
        (active i ∧ (n : ZMod (m i))=Q)) x : ℝ)-
      (x : ℝ)*(∏ i, (if active i then (2 : ℝ) else 1))/(∏ i, (m i : ℝ))|≤
        ∏ i, (if active i then (2 : ℝ) else 1) := by
  classical
  have h := crt_count_error m hcop (fun i => twoResidues (m i) Q (active i)) x
  have hc (i : ι) : ((twoResidues (m i) Q (active i)).card : ℝ)=
      if active i then 2 else 1 := by
    rw [twoResidues_card (m i) Q (active i) (hQ i)]
    split_ifs <;> norm_num
  have hp (i : ι) (n : ℕ) : (n : ZMod (m i))∈twoResidues (m i) Q (active i) ↔
      (n : ZMod (m i))=0 ∨ (active i ∧ (n : ZMod (m i))=Q) := by
    by_cases ha : active <| i
    · simp [twoResidues,ha]
    · simp [twoResidues,ha]
  simpa only [hc,hp] using h

#print axioms count_period_error_general
#print axioms count_cast_period
#print axioms crt_residue_card
#print axioms crt_period_count
#print axioms crt_count_error
#print axioms two_residue_count_error
end QuantitativeEulerEndpointSieve
