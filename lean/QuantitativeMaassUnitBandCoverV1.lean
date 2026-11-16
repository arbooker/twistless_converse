module

public import QuantitativeMaassGrowingBandWidthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set

namespace QuantitativeMaass

/-- A wide interval has an explicit finite unit-window cover, all of
whose centres lie in the same dyadic interval. -/
theorem unit_band_cover (t L : ℝ) (ht : 6≤t) (hL : 1≤L) (hLt : L≤t/4) :
    ∃ n : ℕ,(n:ℝ)≤4*L ∧ ∃ s : Fin n → ℝ,
      (∀ i,t/2≤s i ∧ s i≤2*t) ∧
      ∀ x∈Icc (t-L) (t+L),∃ i,x∈Icc (s i-1/2) (s i+1/2) := by
  let n := ⌈2*L⌉₊+1
  let s : Fin n → ℝ := fun i => t-L+(i.val:ℝ)+1/2
  have hc := Nat.ceil_lt_add_one (show 0≤2*L by linarith)
  refine ⟨n,?_,s,?_,?_⟩
  · dsimp only [n]
    push_cast
    linarith
  · intro i
    have hi : (i.val:ℝ)≤(⌈2*L⌉₊:ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hi0 : 0≤(i.val:ℝ) := Nat.cast_nonneg _
    change t/2≤t-L+(i.val:ℝ)+1/2 ∧ t-L+(i.val:ℝ)+1/2≤2*t
    constructor <;> linarith
  · intro x hx
    let a := x-(t-L)
    have ha : 0≤a := sub_nonneg.mpr hx.1
    have haL : a≤2*L := by dsimp only [a]; linarith [hx.2]
    have hj : ⌊a⌋₊≤⌈2*L⌉₊ := by
      have hh := (Nat.floor_le ha).trans (haL.trans (Nat.le_ceil (2*L)))
      exact_mod_cast hh
    let i : Fin n := ⟨⌊a⌋₊,Nat.lt_succ_iff.mpr hj⟩
    refine ⟨i,?_⟩
    have hlo := Nat.floor_le ha
    have hhi := Nat.lt_floor_add_one a
    change t-L+(⌊a⌋₊:ℝ)+1/2-1/2≤x ∧ x≤t-L+(⌊a⌋₊:ℝ)+1/2+1/2
    dsimp only [a] at hlo hhi
    constructor <;> linarith

/-- Overlap in a finite cover only increases the sum of fibre sizes. -/
theorem finite_cover_card_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : κ → ι → Prop) [∀ j i,Decidable (P j i)] (hcover : ∀ i,∃ j,P j i) :
    Fintype.card ι≤∑ j,Fintype.card {i // P j i} := by
  classical
  let F : κ → Finset ι := fun j => Finset.univ.filter (P j)
  have he : Finset.univ.biUnion F=(Finset.univ : Finset ι) := by
    ext i
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,F,Finset.mem_filter]
    exact ⟨fun _ => trivial,fun _ => hcover i⟩
  have hh : (Finset.univ.biUnion F).card≤∑ j,(F j).card := Finset.card_biUnion_le
  rw [he] at hh
  simpa only [Finset.card_univ,F,Fintype.card_subtype] using hh

#print axioms unit_band_cover
#print axioms finite_cover_card_le

end QuantitativeMaass
