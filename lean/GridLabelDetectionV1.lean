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

theorem high_labels_zero {K : Type*} [AddCommMonoid K] {G : ℕ} (hG : 0<G)
    (f : Fin G → K) (hf : ∀a,2<labelOrder a → ∑z∈labelHit a,f z=0) :
    ∀a,2<labelOrder a → f a=0 :=
  triangular_detect_above labelOrder 2 labelHit
    (fun a _ => (mem_labelHit a a).mpr (Nat.ModEq.refl _))
    (fun a _ z hz hne => labelHit_strict hG a z hz hne) f hf

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

theorem label_detect {K : Type*} [AddCommMonoid K] {G : ℕ} (hG : 0<G)
    (f : Fin G → K) (hhigh : ∀a,2<labelOrder a → ∑z∈labelHit a,f z=0)
    (hzero : f ⟨0,hG⟩=0)
    (hpair : ∀a:Fin G,2*a.val=G → f ⟨0,hG⟩+f a=0) : f=0 := by
  funext a
  change f a=0
  by_cases ha : 2<labelOrder a
  · exact high_labels_zero hG f hhigh a ha
  · rcases small_order hG a (by omega) with hz|hp
    · have he : a=⟨0,hG⟩ := Fin.ext hz
      simpa only [he] using hzero
    · simpa only [hzero,zero_add] using hpair a hp

#print axioms label_detect

end GridLabelDetection
