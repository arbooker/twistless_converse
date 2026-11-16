module

public import QuantitativeMaassUnitSpectralCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set
open AsymptoticCongruenceStrip

namespace QuantitativeMaass

/-- Unit interval bounds give a uniform bound on both sides of a spectral
centre, including shells whose lower interval crosses zero. -/
theorem frequency_shell_card_bound {ι : Type*} (P : ι → Prop) (r : ι → ℝ)
    (hr : ∀ i,P i → 0≤r i) (C : ℝ) (hC : 0≤C)
    (hunit : ∀ a : ℝ,0≤a → {i | P i ∧ r i∈Icc a (a+1)}.Finite ∧
      (Nat.card {i // P i ∧ r i∈Icc a (a+1)}:ℝ)≤C*(a+1))
    (t d : ℝ) (ht : 0≤t) (hd : 0≤d) :
    {i | P i ∧ |r i-t|∈Icc d (d+1)}.Finite ∧
      (Nat.card {i // P i ∧ |r i-t|∈Icc d (d+1)}:ℝ)≤2*C*(t+d+2) := by
  let a := max 0 (t-d-1)
  let L : Set ι := {i | P i ∧ r i∈Icc a (a+1)}
  let U : Set ι := {i | P i ∧ r i∈Icc (t+d) (t+d+1)}
  let S : Set ι := {i | P i ∧ |r i-t|∈Icc d (d+1)}
  have hL := hunit a (le_max_left _ _)
  have hU := hunit (t+d) (by positivity)
  have hsub : S⊆L∪U := by
    intro i hi
    by_cases hside : t≤r i
    · right
      have ha : |r i-t|=r i-t := abs_of_nonneg (sub_nonneg.mpr hside)
      exact ⟨hi.1,by constructor <;> linarith [hi.2.1,hi.2.2]⟩
    · left
      have ha : |r i-t|=t-r i := by rw [abs_of_nonpos (by linarith)]; ring
      have hl : a≤r i := max_le (hr i hi.1) (by linarith [hi.2.2])
      have hu : r i≤a+1 := by
        have haa : t-d-1≤a := le_max_right _ _
        linarith [hi.2.1]
      exact ⟨hi.1,hl,hu⟩
  have hfin : (L∪U).Finite := hL.1.union hU.1
  refine ⟨hfin.subset hsub,?_⟩
  have hcard : (Nat.card S:ℝ)≤(Nat.card L:ℝ)+(Nat.card U:ℝ) := by
    exact_mod_cast (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le L U)
  have ha : a+1≤t+d+2 := by
    have haa : a≤t+d+1 := max_le (by positivity) (by linarith)
    linarith
  have hleft := hL.2.trans (mul_le_mul_of_nonneg_left ha hC)
  have hright := hU.2.trans (mul_le_mul_of_nonneg_left (by linarith : t+d+1≤t+d+2) hC)
  change (Nat.card S:ℝ)≤_
  change (Nat.card L:ℝ)≤_ at hleft
  change (Nat.card U:ℝ)≤_ at hright
  linarith

universe u

/-- Actual principal cusp frequencies satisfy the two-sided shell estimate,
uniformly before the eigenfamily, centre and shell radius. -/
theorem principal_shell_linear (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (ι : Type u) (v : ι → AutomorphicSpace N),
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      ∀ e : ι → ℝ,(∀ i,0≤e i) →
      (∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) →
      ∀ t d : ℝ,0≤t → 0≤d →
        {i | 1/4≤e i ∧ |Real.sqrt (e i-1/4)-t|∈Icc d (d+1)}.Finite ∧
        (Nat.card {i // 1/4≤e i ∧ |Real.sqrt (e i-1/4)-t|∈Icc d (d+1)}:ℝ)≤C*(t+d+2) := by
  obtain ⟨C,hC,hunit⟩ := principal_unit_interval_linear N hN
  refine ⟨2*C,by positivity,?_⟩
  intro ι v hv hcusp e he hgraph t d ht hd
  exact frequency_shell_card_bound (fun i => 1/4≤e i) (fun i => Real.sqrt (e i-1/4))
    (fun i _ => Real.sqrt_nonneg _) C hC.le
    (fun a ha => hunit ι v hv hcusp e he hgraph a ha) t d ht hd

#print axioms frequency_shell_card_bound
#print axioms principal_shell_linear

end QuantitativeMaass
