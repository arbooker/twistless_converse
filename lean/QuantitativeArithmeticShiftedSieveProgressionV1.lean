module

public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Data.Nat.Periodic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticShiftedSieveProgression
open scoped BigOperators

/-- Counting complete periods uses only actual periodicity of a predicate. -/
theorem count_period_mul (p : ℕ → Prop) [DecidablePred p] (m : ℕ)
    (hper : Function.Periodic p m) (k : ℕ) :
    Nat.count p (m*k) = k * Nat.count p m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    have hh : (fun n => p (m*k+n)) = p := by
      funext n
      simpa only [Nat.nsmul_eq_mul, Nat.mul_comm, Nat.add_comm] using hper.nsmul k n
    simp only [hh]
    ring

theorem count_period_error (p : ℕ → Prop) [DecidablePred p] (m x : ℕ)
    (hm : 0 < m) (hper : Function.Periodic p m) (hcount : Nat.count p m=1) :
    |(Nat.count p x : ℝ) - (x : ℝ)/(m : ℝ)| ≤ 1 := by
  have hdecomp : Nat.count p x = x/m + Nat.count p (x%m) := by
    conv_lhs => rw [← Nat.div_add_mod x m]
    rw [Nat.count_add, count_period_mul p m hper, hcount, mul_one]
    congr 1
    congr 1
    funext n
    simpa only [Nat.nsmul_eq_mul, Nat.mul_comm, Nat.add_comm] using hper.nsmul (x/m) n
  have hrem : Nat.count p (x%m) ≤ 1 := by
    simpa only [hcount] using (Nat.count_monotone p) (Nat.mod_lt x hm).le
  have hdiv : (x : ℝ) = (m : ℝ)*(x/m : ℕ)+(x%m : ℕ) := by
    exact_mod_cast (Nat.div_add_mod x m).symm
  have hremR : (0 : ℝ) ≤ (x%m : ℕ) := by positivity
  have hremLt : ((x%m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt x hm
  have hcR : (Nat.count p x : ℝ) = (x/m : ℕ)+(Nat.count p (x%m) : ℕ) := by
    exact_mod_cast hdecomp
  have hcLo : (0 : ℝ) ≤ (Nat.count p (x%m) : ℕ) := by positivity
  have hcHi : ((Nat.count p (x%m) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hrem
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlo : ((x/m : ℕ) : ℝ) ≤ (x : ℝ)/m := (le_div_iff₀ hmR).mpr (by nlinarith)
  have hhi : (x : ℝ)/m ≤ (x/m : ℕ)+1 := (div_le_iff₀ hmR).mpr (by nlinarith)
  rw [abs_le]
  constructor <;> linarith

/-- One residue class occurs exactly once in one complete period. -/
theorem count_modEq_period (m b : ℕ) (hm : 0 < m) :
    Nat.count (fun n => Nat.ModEq m n b) m = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have he : (Finset.range m).filter (fun n => Nat.ModEq m n b) = {b%m} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hn,he⟩
      exact (Nat.mod_eq_of_lt hn).symm.trans he
    · intro he
      subst n
      exact ⟨Nat.mod_lt b hm, by simp [Nat.ModEq]⟩
  rw [he, Finset.card_singleton]

theorem count_shift_period (p : ℕ → Prop) [DecidablePred p] (m : ℕ)
    (hper : Function.Periodic p m) :
    Nat.count (fun n => p (n+1)) m = Nat.count p m := by
  have h1 := Nat.count_succ p m
  have h2 := Nat.count_succ' p m
  have he : p m = p 0 := by simpa using hper 0
  simp only [he] at h1
  omega

theorem card_Icc_filter_eq_count_shift (p : ℕ → Prop) [DecidablePred p] (x : ℕ) :
    ((Finset.Icc 1 x).filter p).card = Nat.count (fun n => p (n+1)) x := by
  rw [Nat.count_eq_card_filter_range]
  symm
  apply Finset.card_bij (fun n _ => n+1)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega,by omega⟩,hn.2⟩
  · intro a ha b hb he
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    refine ⟨n-1,?_,by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega,by simpa only [Nat.sub_add_cancel hn.1.1] using hn.2⟩

/-- Uniform unit error for the count of a residue class on 1,...,x. -/
theorem progression_count_error (m b x : ℕ) (hm : 0 < m) :
    |(((Finset.Icc 1 x).filter (fun n => Nat.ModEq m n b)).card : ℝ) -
      (x : ℝ)/(m : ℝ)| ≤ 1 := by
  rw [card_Icc_filter_eq_count_shift]
  have hper : Function.Periodic (fun n => Nat.ModEq m n b) m := by
    intro n
    simp [Nat.ModEq]
  have hshift : Function.Periodic (fun n => Nat.ModEq m (n+1) b) m := by
    intro n
    simpa only [Nat.add_assoc, Nat.add_comm m 1] using hper (n+1)
  exact count_period_error _ m x hm hshift
    ((count_shift_period _ m hper).trans (count_modEq_period m b hm))

/-- CRT identifies divisibility inside a progression with one class modulo Rd. -/
theorem progression_divisibility_iff (R d b n : ℕ) (hcop : R.Coprime d) :
    Nat.ModEq R n b ∧ d ∣ n ↔ Nat.ModEq (R*d) n (Nat.chineseRemainder hcop b 0).val := by
  constructor
  · rintro ⟨hR,hd⟩
    exact Nat.chineseRemainder_modEq_unique hcop hR (Nat.modEq_zero_iff_dvd.mpr hd)
  · intro h
    have hR := (h.of_mul_right d).trans (Nat.chineseRemainder hcop b 0).property.1
    have hd := (h.of_mul_left R).trans (Nat.chineseRemainder hcop b 0).property.2
    exact ⟨hR,Nat.modEq_zero_iff_dvd.mp hd⟩

/-- Actual progression-and-divisibility count, with error at most one. -/
theorem progression_divisibility_count_error (R d b x : ℕ)
    (hR : 0 < R) (hd : 0 < d) (hcop : R.Coprime d) :
    |(((Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b ∧ d ∣ n)).card : ℝ) -
      (x : ℝ)/((R : ℝ)*(d : ℝ))| ≤ 1 := by
  have he : (fun n => Nat.ModEq R n b ∧ d ∣ n) =
      (fun n => Nat.ModEq (R*d) n (Nat.chineseRemainder hcop b 0).val) := by
    funext n
    exact propext (progression_divisibility_iff R d b n hcop)
  simpa only [he, Nat.cast_mul] using
    progression_count_error (R*d) (Nat.chineseRemainder hcop b 0).val x (Nat.mul_pos hR hd)

def reciprocalDensity : ArithmeticFunction ℝ :=
  ⟨fun d => 1/(d : ℝ),by simp⟩

theorem reciprocalDensity_multiplicative : reciprocalDensity.IsMultiplicative := by
  constructor
  · norm_num [reciprocalDensity]
  · intro m n _
    simp [reciprocalDensity, Nat.cast_mul, mul_comm]

/-- The actual Selberg sieve on a single arithmetic progression. -/
def progressionSieve (R b x P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => by norm_num
  totalMass := (x : ℝ)/(R : ℝ)
  nu := reciprocalDensity
  nu_mult := reciprocalDensity_multiplicative
  nu_pos_of_prime := by
    intro p hp _
    change 0 < 1/(p : ℝ)
    exact div_pos zero_lt_one (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    change 1/(p : ℝ) < 1
    exact (div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)

@[simp] theorem progressionSieve_nu (R b x P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (progressionSieve R b x P hP).nu d = 1/(d : ℝ) := rfl

theorem progressionSieve_multSum (R b x P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (progressionSieve R b x P hP).multSum d =
      (((Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b ∧ d ∣ n)).card : ℝ) := by
  simp only [BoundingSieve.multSum, progressionSieve]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem progressionSieve_rem_bound (R b x P : ℕ) (hR : 0 < R)
    (hP : Squarefree P) (hcop : R.Coprime P) (d : ℕ) (hd : d ∣ P) :
    |(progressionSieve R b x P hP).rem d| ≤ 1 := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hP.ne_zero)
  have hRd : R.Coprime d := hcop.of_dvd_right hd
  have he : (1/(d : ℝ))*((x : ℝ)/(R : ℝ)) = (x : ℝ)/((R : ℝ)*(d : ℝ)) := by ring
  simpa only [BoundingSieve.rem, progressionSieve_multSum, progressionSieve_nu,
    show (progressionSieve R b x P hP).totalMass = (x : ℝ)/(R : ℝ) from rfl, he] using
      progression_divisibility_count_error R d b x hR hdpos hRd

theorem progressionSieve_siftedSum (R b x P : ℕ) (hP : Squarefree P) :
    (progressionSieve R b x P hP).siftedSum =
      (((Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b ∧ P.Coprime n)).card : ℝ) := by
  change (∑ d ∈ (Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b),
    if P.Coprime d then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp only [Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Large primes in the progression survive sieving; small primes cost at most z. -/
theorem progression_prime_count_le_sifted (R b x P z : ℕ) (hP : Squarefree P)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ P → p ≤ z) :
    (((Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b ∧ n.Prime)).card : ℝ) ≤
      (progressionSieve R b x P hP).siftedSum+(z : ℝ) := by
  rw [progressionSieve_siftedSum]
  have hsub : (Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b ∧ n.Prime) ⊆
      ((Finset.Icc 1 x).filter (fun n => Nat.ModEq R n b ∧ P.Coprime n)) ∪ Finset.Icc 1 z := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    by_cases hnz : n ≤ z
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨hn.1.1,hnz⟩)
    · apply Finset.mem_union_left
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨hn.1,hn.2.1,?_⟩
      exact ((hn.2.2.coprime_iff_not_dvd).mpr (fun hd => hnz (hsmall n hn.2.2 hd))).symm
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hzcard : (Finset.Icc 1 z).card=z := by simp
  rw [hzcard] at hcard
  exact_mod_cast hcard

#print axioms progressionSieve_rem_bound
#print axioms progression_prime_count_le_sifted
#print axioms progression_divisibility_count_error
#print axioms count_period_error
#print axioms count_modEq_period
end QuantitativeArithmeticShiftedSieveProgression
