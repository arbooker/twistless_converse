module

public import GridTriangularDetectionV1
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace GridOrderTriangularity

variable {A D : Type*} [AddGroup A] [AddGroup D] [Finite A] [Finite D]

theorem order_pair_ge (a : A) (b : D) : addOrderOf a≤addOrderOf (a,b) :=
  Nat.le_of_dvd (addOrderOf_pos (a,b)) addOrderOf_fst_dvd_addOrderOf

omit [Finite A] [Finite D] in
theorem equal_order_forces_zero (a : A) (b : D)
    (hc : Nat.Coprime (addOrderOf a) (Nat.card D))
    (he : addOrderOf (a,b)=addOrderOf a) : b=0 := by
  have hb : addOrderOf b∣addOrderOf a := he ▸ (addOrderOf_snd_dvd_addOrderOf (x:=(a,b)))
  have hone := Nat.eq_one_of_dvd_coprimes hc hb (addOrderOf_dvd_natCard b)
  exact AddMonoid.addOrderOf_eq_one_iff.mp hone

theorem nonzero_second_strict_order (a : A) (b : D)
    (hc : Nat.Coprime (addOrderOf a) (Nat.card D)) (hb : b≠0) :
    addOrderOf a<addOrderOf (a,b) := by
  apply lt_of_le_of_ne (order_pair_ge a b)
  intro he
  exact hb (equal_order_forces_zero a b hc he.symm)

variable {G : Type*} [AddGroup G] [Finite G]

omit [Finite G] in
/-- A fixed first CRT component and zero complementary component give a
triangular pivot: every other point of its coset has strictly larger order. -/
theorem same_component_strict_order (e : G ≃+ A×D) (a z : G)
    (ha : (e a).2=0) (hz : (e z).1=(e a).1)
    (hc : Nat.Coprime (addOrderOf a) (Nat.card D)) (hne : z≠a) :
    addOrderOf a<addOrderOf z := by
  have hea : e a=((e a).1,0) := Prod.ext rfl ha
  have hez : e z=((e a).1,(e z).2) := Prod.ext hz rfl
  have hao : addOrderOf a=addOrderOf (e a).1 := by
    rw [←e.addOrderOf_eq a,hea,Prod.addOrderOf]
    simp
  have hb : (e z).2≠0 := by
    intro hb
    apply hne
    apply e.injective
    exact Prod.ext hz (hb.trans ha.symm)
  have hgt := nonzero_second_strict_order (e a).1 (e z).2 (by rwa [←hao]) hb
  rw [←hao,←hez] at hgt
  simpa using hgt

#print axioms same_component_strict_order

theorem residue_coset_strict_order {m d a z : ℕ} (hm : 0<m) (hd : 0<d)
    (hmd : Nat.Coprime m d) (hda : d∣a) (hza : Nat.ModEq m z a)
    (hc : Nat.Coprime (addOrderOf (a:ZMod (m*d))) d)
    (hne : ¬Nat.ModEq (m*d) z a) :
    addOrderOf (a:ZMod (m*d))<addOrderOf (z:ZMod (m*d)) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let e := ZMod.chineseRemainder hmd
  apply same_component_strict_order e.toAddEquiv (a:ZMod (m*d)) (z:ZMod (m*d))
  · change (e (a:ZMod (m*d))).2=0
    rw [map_natCast]
    exact (ZMod.natCast_eq_zero_iff a d).mpr hda
  · change (e (z:ZMod (m*d))).1=(e (a:ZMod (m*d))).1
    rw [map_natCast,map_natCast]
    exact (ZMod.natCast_eq_natCast_iff z a m).mpr hza
  · simpa using hc
  · exact fun he => hne ((ZMod.natCast_eq_natCast_iff z a (m*d)).mp he)

#print axioms residue_coset_strict_order

end GridOrderTriangularity
