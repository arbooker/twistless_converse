module

/- Elementary close powers by a finite coloring of normalized powers.
No logarithmic irrationality or Diophantine approximation input. -/
public import CobhamColoringV1
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace CobhamClosePowers

private theorem same_bin_cross {K U V U' V' : ℕ}
    (hV : 0<V) (hV' : 0<V') (hUV : V≤U)
    (he : K*U/V=K*U'/V') : K*U'*V < (K+1)*U*V' := by
  have hlo := Nat.div_mul_le_self (K*U) V
  have hhi : K*U'<(K*U'/V'+1)*V' :=
    (Nat.div_lt_iff_lt_mul hV').mp (Nat.lt_succ_self _)
  rw [← he] at hhi
  have h1 := Nat.mul_lt_mul_of_pos_right hhi hV
  have h2 := Nat.mul_le_mul_right V' hlo
  have h3 := Nat.mul_le_mul_right V' hUV
  nlinarith

theorem close_powers_ordered {a b : ℕ} (hb : 2≤b) (hab : b≤a) (K : ℕ) :
    ∃ m n, 0<m ∧ 0<n ∧ K*a^m<(K+1)*b^n ∧ K*b^n<(K+1)*a^m := by
  classical
  have hb0 : 0<b := by omega
  have ha0 : 0<a := by omega
  let e : ℕ → ℕ := fun i => Nat.log b (a^i)
  have hlo (i) : b^(e i)≤a^i := Nat.pow_log_le_self b (pow_ne_zero _ (by omega))
  have hhi (i) : a^i<b*b^(e i) := by
    have := Nat.lt_pow_succ_log_self (by omega : 1<b) (a^i)
    simpa [e,pow_succ,mul_comm] using this
  let f : ℕ → Fin ((K+1)*b) := fun i => ⟨K*a^i / b^(e i), by
    apply (Nat.div_lt_iff_lt_mul (pow_pos hb0 _)).mpr
    have := Nat.mul_le_mul_left K (Nat.le_of_lt (hhi i))
    have := pow_pos hb0 (e i)
    nlinarith⟩
  obtain ⟨i,j,hij,_,_,he⟩ := CobhamColoring.repeated_pair f (fun _ => ()) ()
    (by simpa using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite))
  have he' : K*a^i / b^(e i)=K*a^j / b^(e j) := congrArg Fin.val he
  have hej : e i<e j := by
    have h1 : b^(e i+1)≤a^(i+1) := by
      rw [pow_succ,pow_succ]
      exact Nat.mul_le_mul (hlo i) hab
    have h2 := Nat.pow_le_pow_right ha0 (show i+1≤j by omega)
    have := Nat.le_log_of_pow_le (by omega : 1<b) (h1.trans h2)
    exact this
  have hA : a^j=a^i*a^(j-i) := by rw [← pow_add,Nat.add_sub_of_le (Nat.le_of_lt hij)]
  have hB : b^(e j)=b^(e i)*b^(e j-e i) := by
    rw [← pow_add,Nat.add_sub_of_le (Nat.le_of_lt hej)]
  have h1 := same_bin_cross (pow_pos hb0 (e i)) (pow_pos hb0 (e j)) (hlo i) he'
  have h2 := same_bin_cross (pow_pos hb0 (e j)) (pow_pos hb0 (e i)) (hlo j) he'.symm
  rw [hA,hB] at h1 h2
  have hp : 0<a^i*b^(e i) := Nat.mul_pos (pow_pos ha0 _) (pow_pos hb0 _)
  refine ⟨j-i,e j-e i,by omega,by omega,?_,?_⟩
  · apply (Nat.mul_lt_mul_left hp).mp
    nlinarith only [h1]
  · apply (Nat.mul_lt_mul_left hp).mp
    nlinarith only [h2]

theorem close_powers {a b : ℕ} (ha : 2≤a) (hb : 2≤b) (K : ℕ) :
    ∃ m n, 0<m ∧ 0<n ∧ K*a^m<(K+1)*b^n ∧ K*b^n<(K+1)*a^m := by
  rcases le_total b a with h | h
  · exact close_powers_ordered hb h K
  · obtain ⟨n,m,hn,hm,h1,h2⟩ := close_powers_ordered ha h K
    exact ⟨m,n,hm,hn,h2,h1⟩

#print axioms close_powers

end CobhamClosePowers
