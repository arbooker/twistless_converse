module

public import SpanningCyclicCoordinatesV1
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace CompleteRowCosets

open SpanningCyclicCoordinates SpanningTraceAlgebra

theorem residue_eq_iff {Q : ℕ} (hQ : 0<Q) (x y : ℤ) :
    residue hQ x=residue hQ y ↔ Int.ModEq Q x y := by
  constructor
  · intro h
    have hh := congrArg (fun i:Fin Q => (i.val:ℤ)) h
    have hQ0 : (Q:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hQ
    change (((x%(Q:ℤ)).toNat:ℤ))=(((y%(Q:ℤ)).toNat:ℤ)) at hh
    rw [Int.toNat_of_nonneg (Int.emod_nonneg x hQ0),Int.toNat_of_nonneg (Int.emod_nonneg y hQ0)] at hh
    exact hh
  · intro h
    apply Fin.ext
    exact congrArg Int.toNat h

theorem residue_nat {Q : ℕ} (hQ : 0<Q) (j : Fin Q) : residue hQ j.val=j := by
  apply Fin.ext
  simp only [residue]
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)]
  rfl

theorem residue_mod {Q : ℕ} (hQ : 0<Q) (x : ℤ) : Int.ModEq Q (residue hQ x).val x := by
  change (((x%(Q:ℤ)).toNat:ℤ)%(Q:ℤ))=x%(Q:ℤ)
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt hQ)),Int.emod_emod]

def rowIndex {q D : ℕ} (hq : 0<q) (hD : 0<D) (u : ℤ) (k : Fin q) :
    {j:Fin (q*D) // Int.ModEq D j.val u} :=
  ⟨residue (Nat.mul_pos hq hD) (u+(k.val:ℤ)*D),by
    have hh := (residue_mod (Nat.mul_pos hq hD) (u+(k.val:ℤ)*D)).of_dvd
      (show (D:ℤ)∣(q*D:ℕ) by exact_mod_cast dvd_mul_left D q)
    exact hh.trans (by simp [Int.ModEq])⟩

theorem rowIndex_injective {q D : ℕ} (hq : 0<q) (hD : 0<D) (u : ℤ) :
    Function.Injective (rowIndex hq hD u) := by
  intro k l he
  have hh := (residue_eq_iff (Nat.mul_pos hq hD) _ _).mp (congrArg Subtype.val he)
  have hh' := hh.add_left_cancel' u
  rw [Nat.cast_mul] at hh'
  have hd0 : (D:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hk := Int.ModEq.mul_right_cancel' hd0 hh'
  apply Fin.ext
  have he' : (k.val:ℤ)=(l.val:ℤ) := by
    have hkq : (k.val:ℤ)<(q:ℤ) := by exact_mod_cast k.isLt
    have hlq : (l.val:ℤ)<(q:ℤ) := by exact_mod_cast l.isLt
    simpa only [Int.ModEq,Int.emod_eq_of_lt (by omega : (0:ℤ)≤k.val) hkq,
      Int.emod_eq_of_lt (by omega : (0:ℤ)≤l.val) hlq] using hk
  exact_mod_cast he'

theorem rowIndex_surjective {q D : ℕ} (hq : 0<q) (hD : 0<D) (u : ℤ) :
    Function.Surjective (rowIndex hq hD u) := by
  intro j
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp j.property.symm
  have hj : (j.val.val:ℤ)=u+(D:ℤ)*t := by omega
  let k := residue hq t
  refine ⟨k,Subtype.ext ?_⟩
  change residue (Nat.mul_pos hq hD) (u+(k.val:ℤ)*D)=j.val
  rw [←residue_nat (Nat.mul_pos hq hD) j.val]
  apply (residue_eq_iff (Nat.mul_pos hq hD) _ _).mpr
  have hk := (residue_mod hq t).mul_right' (c:=(D:ℤ))
  have hku := hk.add_left u
  simpa only [Nat.cast_mul,hj,Int.mul_comm t (D:ℤ)] using hku

noncomputable def rowEquiv {q D : ℕ} (hq : 0<q) (hD : 0<D) (u : ℤ) :
    Fin q ≃ {j:Fin (q*D) // Int.ModEq D j.val u} :=
  Equiv.ofBijective (rowIndex hq hD u) ⟨rowIndex_injective hq hD u,rowIndex_surjective hq hD u⟩

noncomputable def cosetSum {K : Type*} [AddCommMonoid K] (Q D : ℕ) (u : ℤ) (v : ℤ → K) : K := by
  classical
  exact ∑j:{j:Fin Q // Int.ModEq D j.val u},v j.val.val

theorem trace_coset_sum {K : Type*} [AddCommMonoid K] {q D : ℕ}
    (hq : 0<q) (hD : 0<D) (u : ℤ) (v : ℤ → K) (hv : Cyclic (q*D) v) :
    trace q D v u=cosetSum (q*D) D u v := by
  classical
  unfold cosetSum
  rw [trace,←Fin.sum_univ_eq_sum_range]
  rw [←(rowEquiv hq hD u).sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  change v (u+(k.val:ℤ)*D)=v ((residue (Nat.mul_pos hq hD) (u+(k.val:ℤ)*D)).val:ℤ)
  have hQ0 : ((q*D:ℕ):ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hq hD)
  simp only [residue,Int.toNat_of_nonneg (Int.emod_nonneg (u+(k.val:ℤ)*D) hQ0)]
  exact (cyclic_emod hv _).symm

#print axioms rowEquiv
#print axioms trace_coset_sum

end CompleteRowCosets
