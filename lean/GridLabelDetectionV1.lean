module

public import GridCenterChoiceV1
public import GridRestrictedRowsV1

@[expose] public section

namespace GridLabelDetection

open GridPrimeParts GridCosetOrder GridTriangularDetection GridRestrictedRows

noncomputable def labelOrder {G : ℕ} (a : Fin G) := addOrderOf (a.val:ZMod G)
noncomputable def labelModulus {G : ℕ} (a : Fin G) := primePart G (fun p => p∣labelOrder a)

noncomputable def labelHit {G : ℕ} (a : Fin G) : Finset (Fin G) := by
  classical
  exact Finset.univ.filter (fun z => Nat.ModEq (labelModulus a) z.val a.val)

theorem mem_labelHit {G : ℕ} (a z : Fin G) :
    z∈labelHit a ↔ Nat.ModEq (labelModulus a) z.val a.val := by
  classical
  simp [labelHit]

theorem labelHit_strict {G : ℕ} (hG : 0<G) (a z : Fin G)
    (hz : z∈labelHit a) (hne : z≠a) : labelOrder a<labelOrder z := by
  apply grid_coset_strict hG (mem_labelHit _ _ |>.mp hz)
  intro he
  apply hne
  apply Fin.ext
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt z.isLt,Nat.mod_eq_of_lt a.isLt] using he

theorem small_order {G : ℕ} (hG : 0<G) (a : Fin G) (ha : labelOrder a≤2) :
    a.val=0 ∨ 2*a.val=G := by
  let : NeZero G := ⟨Nat.ne_of_gt hG⟩
  have hp : 0<labelOrder a := addOrderOf_pos (a.val:ZMod G)
  have hh : labelOrder a=1 ∨ labelOrder a=2 := by omega
  rcases hh with h1|h2
  · have hz := AddMonoid.addOrderOf_eq_one_iff.mp h1
    have hd := (ZMod.natCast_eq_zero_iff a.val G).mp hz
    left
    exact Nat.eq_zero_of_dvd_of_lt hd a.isLt
  · have hd := order_annihilation G a.val
    change G∣labelOrder a*a.val at hd
    rw [h2] at hd
    rcases hd with ⟨t,ht⟩
    have ht2 : t<2 := by nlinarith [a.isLt]
    have htt : t=0 ∨ t=1 := by omega
    rcases htt with rfl|rfl
    · left; omega
    · right; omega

#print axioms labelHit_strict
#print axioms small_order

end GridLabelDetection
