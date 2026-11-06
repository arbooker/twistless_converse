module

public import SpanningPrimeReciprocalPacketV1
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

namespace SpanningSmallPrimeDensity

theorem prod_one_sub_mul_sum_le_one {I:Type*} (S:Finset I) (f:I → ℝ)
    (hf:∀i∈S,0≤f i ∧ f i≤1) :
    (∏i∈S,(1-f i))*(1+∑i∈S,f i)≤1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀j∈S,0≤f j ∧ f j≤1 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hP : 0≤∏j∈S,(1-f j) := Finset.prod_nonneg (fun j hj => sub_nonneg.mpr (hfs j hj).2)
    have hsum : 0≤∑j∈S,f j := Finset.sum_nonneg (fun j hj => (hfs j hj).1)
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    calc
      (1-f i)*(∏j∈S,(1-f j))*(1+(f i+∑j∈S,f j))=
          (∏j∈S,(1-f j))*(1+∑j∈S,f j)-
            (∏j∈S,(1-f j))*f i*(f i+∑j∈S,f j) := by ring
      _≤(∏j∈S,(1-f j))*(1+∑j∈S,f j) :=
        sub_le_self _ (mul_nonneg (mul_nonneg hP hfi.1) (add_nonneg hfi.1 hsum))
      _≤1 := ih hfs

noncomputable def density (S:Finset ℕ) : ℝ := ∏p∈S,(1-1/(p:ℝ))

theorem prime_reciprocal_bounds {p:ℕ} (hp:p.Prime) :
    0≤1/(p:ℝ) ∧ 1/(p:ℝ)≤1 := by
  have hpos : (0:ℝ)<p := by exact_mod_cast hp.pos
  constructor
  · positivity
  · exact (div_le_one hpos).mpr (by exact_mod_cast hp.one_lt.le)

theorem density_nonneg {S:Finset ℕ} (hp:∀p∈S,p.Prime) : 0≤density S :=
  Finset.prod_nonneg (fun p h => sub_nonneg.mpr (prime_reciprocal_bounds (hp p h)).2)

theorem packet {bound:ℕ} : ∃S:Finset ℕ,(∀p∈S,p.Prime ∧ bound<p) ∧ density S≤2/3 := by
  let k := bound+1
  let S := (4^(k.primesBelow.card+1)).succ.primesBelow \ k.primesBelow
  have hp : ∀p∈S,p.Prime ∧ bound<p := by
    intro p h
    have hs := Finset.mem_sdiff.mp h
    have hprime := Nat.prime_of_mem_primesBelow hs.1
    have hn : k≤p := by
      by_contra hlt
      apply hs.2
      exact Nat.mem_primesBelow.mpr ⟨by omega,hprime⟩
    exact ⟨hprime,by dsimp [k] at hn; omega⟩
  have hsum : (1:ℝ)/2≤∑p∈S,1/(p:ℝ) := SpanningPrimeReciprocalPacket.half_sum k
  have hprod := prod_one_sub_mul_sum_le_one S (fun p:ℕ => 1/(p:ℝ))
    (fun p h => prime_reciprocal_bounds (hp p h).1)
  have hn := density_nonneg (fun p h => (hp p h).1)
  refine ⟨S,hp,?_⟩
  change density S*(1+∑p∈S,1/(p:ℝ))≤1 at hprod
  nlinarith

theorem density_power (bound n:ℕ) :
    ∃S:Finset ℕ,(∀p∈S,p.Prime ∧ bound<p) ∧ density S≤(2/3:ℝ)^n := by
  classical
  induction n with
  | zero => exact ⟨∅,by simp,by simp [density]⟩
  | succ n ih =>
    obtain ⟨S,hS,hρS⟩ := ih
    obtain ⟨T,hT,hρT⟩ := packet (bound:=max bound (S.sup id))
    have hd : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro p hp hpt
      have hple : p≤S.sup id := Finset.le_sup (f:=id) hp
      have hplt := (hT p hpt).2
      omega
    refine ⟨S∪T,?_,?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with hp|hp
      · exact hS p hp
      · exact ⟨(hT p hp).1,lt_of_le_of_lt (le_max_left _ _) (hT p hp).2⟩
    · unfold density at hρS hρT ⊢
      rw [Finset.prod_union hd,pow_succ]
      exact mul_le_mul hρS hρT (density_nonneg (fun p h => (hT p h).1))
        (pow_nonneg (by norm_num) _)

theorem arbitrarily_small_density (bound:ℕ) {ε:ℝ} (hε:0<ε) :
    ∃S:Finset ℕ,(∀p∈S,p.Prime ∧ bound<p) ∧ density S<ε := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hε (show (2/3:ℝ)<1 by norm_num)
  obtain ⟨S,hS,hs⟩ := density_power bound n
  exact ⟨S,hS,hs.trans_lt hn⟩

#print axioms arbitrarily_small_density

end SpanningSmallPrimeDensity
