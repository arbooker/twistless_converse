module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic
public import QuantitativeArithmeticExponentialDivisionTheoryV4
public import QuantitativeArithmeticTwoSequenceStripRowsV1
public import SmallLevelTaylorRowCoefficientsV1

/-! Consolidated chapter: QuantitativeArithmeticVerticalBounded. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticVerticalBoundedAlgebraV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded
open Complex

/-- Uniform boundedness on every closed vertical strip, with constants
allowed to depend on the two endpoints. -/
def Bounded (F : ℂ → ℂ) : Prop :=
  ∀ l u : ℝ, ∃ C : ℝ,0≤C ∧ ∀ s : ℂ,l≤s.re → s.re≤u → ‖F s‖≤C

theorem Bounded.const (c : ℂ) : Bounded (fun _ => c) :=
  fun _ _ => ⟨‖c‖,norm_nonneg _,fun _ _ _ => le_rfl⟩

theorem Bounded.add {F G : ℂ → ℂ} (hf : Bounded F) (hg : Bounded G) :
    Bounded (fun s => F s+G s) := by
  intro l u
  obtain ⟨A,hA,ha⟩ := hf l u
  obtain ⟨B,hB,hb⟩ := hg l u
  exact ⟨A+B,add_nonneg hA hB,fun s hl hu =>
    (norm_add_le _ _).trans (add_le_add (ha s hl hu) (hb s hl hu))⟩

theorem Bounded.neg {F : ℂ → ℂ} (hf : Bounded F) : Bounded (fun s => -F s) := by
  intro l u
  obtain ⟨C,hC,h⟩ := hf l u
  exact ⟨C,hC,fun s hl hu => by simpa only [norm_neg] using h s hl hu⟩

theorem Bounded.sub {F G : ℂ → ℂ} (hf : Bounded F) (hg : Bounded G) :
    Bounded (fun s => F s-G s) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Bounded.mul {F G : ℂ → ℂ} (hf : Bounded F) (hg : Bounded G) :
    Bounded (fun s => F s*G s) := by
  intro l u
  obtain ⟨A,hA,ha⟩ := hf l u
  obtain ⟨B,hB,hb⟩ := hg l u
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro s hl hu
  rw [norm_mul]
  exact mul_le_mul (ha s hl hu) (hb s hl hu) (norm_nonneg _) hA

theorem Bounded.pow {F : ℂ → ℂ} (hf : Bounded F) (n : ℕ) :
    Bounded (fun s => F s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using Bounded.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem Bounded.sum {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i∈t,Bounded (F i)) : Bounded (fun s => ∑ i∈t,F i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Bounded.const 0
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- Real exponential rates have bounded modulus on vertical strips. -/
theorem exponential (a b : ℝ) : Bounded (fun s : ℂ => exp ((a:ℂ)*(s-(b:ℂ)))) := by
  intro l u
  refine ⟨Real.exp (max (a*(l-b)) (a*(u-b))), (Real.exp_pos _).le,?_⟩
  intro s hl hu
  rw [Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.sub_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  apply Real.exp_le_exp.mpr
  by_cases ha : 0≤a
  · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hu b) ha).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left (sub_le_sub_right hl b) (le_of_not_ge ha)).trans (le_max_left _ _)

theorem exponential_inv (a b : ℝ) :
    Bounded (fun s : ℂ => (exp ((a:ℂ)*(s-(b:ℂ))))⁻¹) := by
  have he : (fun s : ℂ => (exp ((a:ℂ)*(s-(b:ℂ))))⁻¹)=
      (fun s : ℂ => exp (((-a:ℝ):ℂ)*(s-(b:ℂ)))) := by
    funext s
    rw [← exp_neg,Complex.ofReal_neg,neg_mul]
  rw [he]
  exact exponential (-a) b

theorem Bounded.zpow {F : ℂ → ℂ} (hf : Bounded F)
    (hi : Bounded (fun s => (F s)⁻¹)) (n : ℤ) : Bounded (fun s => F s^n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hf.pow n
  | negSucc n => simpa only [zpow_negSucc,inv_pow] using hi.pow (n+1)
#print axioms exponential
#print axioms Bounded.zpow
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticPolynomialGrowthAlgebraV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded

def PolynomialGrowth (F : ℂ → ℂ) : Prop :=
  ∃ (d : ℕ) (C : ℝ),0≤C ∧ ∀ s : ℂ,‖F s‖≤C*(1+‖s‖)^d

theorem PolynomialGrowth.const (c : ℂ) : PolynomialGrowth (fun _ => c) :=
  ⟨0,‖c‖,norm_nonneg _,fun _ => by simp⟩

theorem PolynomialGrowth.id : PolynomialGrowth (fun s : ℂ => s) :=
  ⟨1,1,by norm_num,fun s => by simp⟩

theorem PolynomialGrowth.mul {F G : ℂ → ℂ}
    (hf : PolynomialGrowth F) (hg : PolynomialGrowth G) : PolynomialGrowth (fun s => F s*G s) := by
  obtain ⟨d,A,hA,ha⟩ := hf
  obtain ⟨e,B,hB,hb⟩ := hg
  refine ⟨d+e,A*B,mul_nonneg hA hB,?_⟩
  intro s
  rw [norm_mul,pow_add]
  calc
    ‖F s‖*‖G s‖≤(A*(1+‖s‖)^d)*(B*(1+‖s‖)^e) :=
      mul_le_mul (ha s) (hb s) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem PolynomialGrowth.add {F G : ℂ → ℂ}
    (hf : PolynomialGrowth F) (hg : PolynomialGrowth G) : PolynomialGrowth (fun s => F s+G s) := by
  obtain ⟨d,A,hA,ha⟩ := hf
  obtain ⟨e,B,hB,hb⟩ := hg
  refine ⟨d+e,A+B,add_nonneg hA hB,?_⟩
  intro s
  have hd : (1+‖s‖)^d≤(1+‖s‖)^(d+e) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.le_add_right d e)
  have he : (1+‖s‖)^e≤(1+‖s‖)^(d+e) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.le_add_left e d)
  calc
    ‖F s+G s‖≤‖F s‖+‖G s‖ := norm_add_le _ _
    _ ≤ A*(1+‖s‖)^d+B*(1+‖s‖)^e := add_le_add (ha s) (hb s)
    _ ≤ A*(1+‖s‖)^(d+e)+B*(1+‖s‖)^(d+e) :=
      add_le_add (mul_le_mul_of_nonneg_left hd hA) (mul_le_mul_of_nonneg_left he hB)
    _ = _ := by ring

theorem PolynomialGrowth.neg {F : ℂ → ℂ} (hf : PolynomialGrowth F) :
    PolynomialGrowth (fun s => -F s) := by
  obtain ⟨d,C,hC,h⟩ := hf
  exact ⟨d,C,hC,fun s => by simpa only [norm_neg] using h s⟩

theorem PolynomialGrowth.sub {F G : ℂ → ℂ}
    (hf : PolynomialGrowth F) (hg : PolynomialGrowth G) : PolynomialGrowth (fun s => F s-G s) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem PolynomialGrowth.pow {F : ℂ → ℂ} (hf : PolynomialGrowth F) (n : ℕ) :
    PolynomialGrowth (fun s => F s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using PolynomialGrowth.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem PolynomialGrowth.aeval {R : Type*} [CommRing R] [Algebra R ℂ]
    {F : ℂ → ℂ} (hF : PolynomialGrowth F) (p : Polynomial R) :
    PolynomialGrowth (fun s => Polynomial.aeval (F s) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n a =>
    simpa only [Polynomial.aeval_monomial] using (PolynomialGrowth.const (algebraMap R ℂ a)).mul (hF.pow n)

theorem binomial_polynomial_growth (k n : ℕ) :
    PolynomialGrowth (fun s : ℂ => Ring.choose (s+(n:ℂ)-(k:ℂ)) n) := by
  have hf := (PolynomialGrowth.id.add (PolynomialGrowth.const (n:ℂ))).sub
    (PolynomialGrowth.const (k:ℂ))
  have h := (PolynomialGrowth.const ((n.factorial:ℂ)⁻¹)).mul
    (hf.aeval (descPochhammer ℤ n))
  simpa only [Ring.choose_eq_smul,← Polynomial.aeval_eq_smeval,smul_eq_mul] using h
#print axioms binomial_polynomial_growth
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticPolynomialOnSetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded
open Set Complex

def PolynomialOn (S : Set ℂ) (F : ℂ → ℂ) : Prop :=
  ∃ (d : ℕ) (C : ℝ),0≤C ∧ ∀ s∈S,‖F s‖≤C*(1+‖s‖)^d

def StripPolynomial (F : ℂ → ℂ) : Prop :=
  ∀ l u : ℝ,PolynomialOn {s : ℂ | l≤s.re ∧ s.re≤u} F

def PolynomialSubstrips (b : ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ l u : ℝ,b<l → b<u → PolynomialOn {s : ℂ | l≤s.re ∧ s.re≤u} F

theorem PolynomialOn.mono {S T : Set ℂ} {F : ℂ → ℂ}
    (h : PolynomialOn S F) (hTS : T⊆S) : PolynomialOn T F := by
  obtain ⟨d,C,hC,h⟩ := h
  exact ⟨d,C,hC,fun s hs => h s (hTS hs)⟩

theorem PolynomialOn.congr {S : Set ℂ} {F G : ℂ → ℂ}
    (h : PolynomialOn S F) (he : EqOn F G S) : PolynomialOn S G := by
  obtain ⟨d,C,hC,h⟩ := h
  exact ⟨d,C,hC,fun s hs => by rw [← he hs]; exact h s hs⟩

theorem PolynomialOn.of_bound {S : Set ℂ} {F : ℂ → ℂ} (C : ℝ) (hC : 0≤C)
    (h : ∀ s∈S,‖F s‖≤C) : PolynomialOn S F :=
  ⟨0,C,hC,fun s hs => by simpa only [pow_zero,mul_one] using h s hs⟩

theorem PolynomialOn.const (S : Set ℂ) (c : ℂ) : PolynomialOn S (fun _ => c) :=
  PolynomialOn.of_bound ‖c‖ (norm_nonneg _) (fun _ _ => le_rfl)

theorem PolynomialGrowth.onSet {F : ℂ → ℂ} (h : PolynomialGrowth F) (S : Set ℂ) : PolynomialOn S F := by
  obtain ⟨d,C,hC,h⟩ := h
  exact ⟨d,C,hC,fun s _ => h s⟩

theorem PolynomialOn.mul {S : Set ℂ} {F G : ℂ → ℂ}
    (hf : PolynomialOn S F) (hg : PolynomialOn S G) : PolynomialOn S (fun s => F s*G s) := by
  obtain ⟨d,A,hA,ha⟩ := hf
  obtain ⟨e,B,hB,hb⟩ := hg
  refine ⟨d+e,A*B,mul_nonneg hA hB,?_⟩
  intro s hs
  rw [norm_mul,pow_add]
  calc
    ‖F s‖*‖G s‖≤(A*(1+‖s‖)^d)*(B*(1+‖s‖)^e) :=
      mul_le_mul (ha s hs) (hb s hs) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem PolynomialOn.add {S : Set ℂ} {F G : ℂ → ℂ}
    (hf : PolynomialOn S F) (hg : PolynomialOn S G) : PolynomialOn S (fun s => F s+G s) := by
  obtain ⟨d,A,hA,ha⟩ := hf
  obtain ⟨e,B,hB,hb⟩ := hg
  refine ⟨d+e,A+B,add_nonneg hA hB,?_⟩
  intro s hs
  have hd : (1+‖s‖)^d≤(1+‖s‖)^(d+e) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.le_add_right d e)
  have he : (1+‖s‖)^e≤(1+‖s‖)^(d+e) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.le_add_left e d)
  calc
    ‖F s+G s‖≤‖F s‖+‖G s‖ := norm_add_le _ _
    _ ≤ A*(1+‖s‖)^d+B*(1+‖s‖)^e := add_le_add (ha s hs) (hb s hs)
    _ ≤ A*(1+‖s‖)^(d+e)+B*(1+‖s‖)^(d+e) :=
      add_le_add (mul_le_mul_of_nonneg_left hd hA) (mul_le_mul_of_nonneg_left he hB)
    _ = _ := by ring

theorem PolynomialOn.neg {S : Set ℂ} {F : ℂ → ℂ} (h : PolynomialOn S F) : PolynomialOn S (fun s => -F s) := by
  obtain ⟨d,C,hC,h⟩ := h
  exact ⟨d,C,hC,fun s hs => by simpa only [norm_neg] using h s hs⟩

theorem PolynomialOn.sub {S : Set ℂ} {F G : ℂ → ℂ}
    (hf : PolynomialOn S F) (hg : PolynomialOn S G) : PolynomialOn S (fun s => F s-G s) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem PolynomialOn.pow {S : Set ℂ} {F : ℂ → ℂ} (hf : PolynomialOn S F) (n : ℕ) :
    PolynomialOn S (fun s => F s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using PolynomialOn.const S 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem PolynomialOn.sum {S : Set ℂ} {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i∈t,PolynomialOn S (F i)) : PolynomialOn S (fun s => ∑ i∈t,F i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using PolynomialOn.const S 0
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem Bounded.stripPolynomial {F : ℂ → ℂ} (h : Bounded F) : StripPolynomial F := by
  intro l u
  obtain ⟨C,hC,h⟩ := h l u
  exact PolynomialOn.of_bound C hC (fun s hs => h s hs.1 hs.2)

theorem PolynomialGrowth.stripPolynomial {F : ℂ → ℂ} (h : PolynomialGrowth F) : StripPolynomial F :=
  fun _ _ => h.onSet _

theorem StripPolynomial.mul {F G : ℂ → ℂ} (hf : StripPolynomial F) (hg : StripPolynomial G) :
    StripPolynomial (fun s => F s*G s) := fun l u => (hf l u).mul (hg l u)

theorem StripPolynomial.add {F G : ℂ → ℂ} (hf : StripPolynomial F) (hg : StripPolynomial G) :
    StripPolynomial (fun s => F s+G s) := fun l u => (hf l u).add (hg l u)

theorem StripPolynomial.sum {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i∈t,StripPolynomial (F i)) : StripPolynomial (fun s => ∑ i∈t,F i s) :=
  fun l u => PolynomialOn.sum t F (fun i hi => hF i hi l u)

#print axioms PolynomialOn.sum
#print axioms StripPolynomial.sum
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticPolynomialStripOperationsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded
open Complex Set Metric

theorem PolynomialOn.comp_add {S T : Set ℂ} {F : ℂ → ℂ}
    (hF : PolynomialOn T F) (c : ℂ) (hST : ∀ s∈S,s+c∈T) :
    PolynomialOn S (fun s => F (s+c)) := by
  obtain ⟨d,C,hC,h⟩ := hF
  refine ⟨d,C*(1+‖c‖)^d,by positivity,?_⟩
  intro s hs
  calc
    ‖F (s+c)‖≤C*(1+‖s+c‖)^d := h _ (hST s hs)
    _ ≤ C*((1+‖c‖)*(1+‖s‖))^d := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (by positivity)
      have hh := norm_add_le s c
      nlinarith [norm_nonneg s,norm_nonneg c]
    _ = _ := by rw [mul_pow]; ring

theorem PolynomialOn.inverse_real_shift (S : Set ℂ) (a : ℝ)
    (hS : ∀ s∈S,1≤|s.im|) : PolynomialOn S (fun s : ℂ => (s-(a:ℂ))⁻¹) := by
  apply PolynomialOn.of_bound 1 (by norm_num)
  intro s hs
  rw [norm_inv]
  apply inv_le_one_of_one_le₀
  have hh := abs_im_le_norm (s-(a:ℂ))
  simp only [sub_im,ofReal_im,sub_zero] at hh
  exact (hS s hs).trans hh

/-- A polynomial bound at large imaginary height extends across the compact
middle of a strip for any continuous function. -/
theorem polynomial_strip_of_tail {F : ℂ → ℂ} (hF : Continuous F) (l u : ℝ)
    (h : PolynomialOn {s : ℂ | l≤s.re ∧ s.re≤u ∧ 1≤|s.im|} F) :
    PolynomialOn {s : ℂ | l≤s.re ∧ s.re≤u} F := by
  obtain ⟨d,C,hC,h⟩ := h
  let R : ℝ := |l|+|u|+1
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hF.continuousOn
  let K' : ℝ := max K 0
  have hK' : 0≤K' := le_max_right _ _
  refine ⟨d,C+K',add_nonneg hC hK',?_⟩
  intro s hs
  by_cases hi : 1≤|s.im|
  · exact (h s ⟨hs.1,hs.2,hi⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK') (by positivity))
  · have hre : |s.re|≤|l|+|u| := by
      apply abs_le.mpr
      constructor
      · have hl := neg_abs_le l
        linarith [abs_nonneg u,hs.1]
      · have hu := le_abs_self u
        linarith [abs_nonneg l,hs.2]
    have hnorm : ‖s‖≤R := by
      have hh := norm_le_abs_re_add_abs_im s
      dsimp [R]
      linarith
    have hb : ‖F s‖≤K' := (hK s (by simpa only [mem_closedBall,dist_zero_right] using hnorm)).trans (le_max_left _ _)
    have hp : 1≤(1+‖s‖)^d := one_le_pow₀ (by linarith [norm_nonneg s])
    calc
      ‖F s‖≤K' := hb
      _ ≤ (C+K')*(1+‖s‖)^d := by nlinarith

/-- Multiplication by a positive power makes the zero divisor itself
harmless for an estimate obtained away from that divisor. -/
theorem PolynomialOn.fill_divisor {S : Set ℂ} {D F : ℂ → ℂ} (n : ℕ) (hn : 0<n)
    (h : PolynomialOn (S∩{s : ℂ | D s≠0}) (fun s => D s^n*F s)) :
    PolynomialOn S (fun s => D s^n*F s) := by
  obtain ⟨d,C,hC,h⟩ := h
  refine ⟨d,C,hC,?_⟩
  intro s hs
  by_cases hd : D s=0
  · simp only [hd,zero_pow (Nat.ne_of_gt hn),zero_mul,norm_zero]
    positivity
  · exact h s ⟨hs,hd⟩
#print axioms PolynomialOn.comp_add
#print axioms polynomial_strip_of_tail
#print axioms PolynomialOn.fill_divisor
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticPolynomialSubstripBootstrapV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded
open Complex Set QuantitativeArithmeticMellinStrip

theorem boundedSubstrips_polynomial {b : ℝ} {F : ℂ → ℂ}
    (h : BoundedSubstrips b F) : PolynomialSubstrips b F := by
  intro l u hl hu
  obtain ⟨C,hC,h⟩ := h l u hl hu
  exact PolynomialOn.of_bound C hC (fun s hs => h s hs.1 hs.2)

theorem PolynomialSubstrips.mono {a b : ℝ} {F : ℂ → ℂ}
    (h : PolynomialSubstrips a F) (hab : a≤b) : PolynomialSubstrips b F :=
  fun l u hl hu => h l u (hab.trans_lt hl) (hab.trans_lt hu)

theorem PolynomialSubstrips.shift {b l u : ℝ} {F : ℂ → ℂ}
    (h : PolynomialSubstrips b F) (c : ℝ) (hl : b<l+c) (hu : b<u+c) :
    PolynomialOn {s : ℂ | l≤s.re ∧ s.re≤u} (fun s => F (s+(c:ℂ))) := by
  apply (h (l+c) (u+c) hl hu).comp_add (c:ℂ)
  intro s hs
  simp only [mem_ofPred_eq,add_re,ofReal_re]
  constructor <;> linarith [hs.1,hs.2]

/-- A positive-power cleared estimate on the high part of slightly larger
strips gives genuine polynomial bounds, even at the divisor zeros. -/
theorem quadratic_substrip_step (ρ : ℂ) (hρ : ρ≠0) (κ a : ℂ)
    (e : ℕ) (he : 0<e) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (b : ℝ)
    (htail : ∀ l u : ℝ,b-1<l → b-1<u →
      PolynomialOn ({s : ℂ | l≤s.re ∧ s.re≤u ∧ 1≤|s.im|} ∩
        {s : ℂ | a*exp (ρ*(s-κ))+exp (ρ*(s-κ))^2-1≠0})
        (fun s => (a*exp (ρ*(s-κ))+exp (ρ*(s-κ))^2-1)^e*H s)) :
    PolynomialSubstrips (b-1/2) H := by
  intro l u hl hu
  let D : ℂ → ℂ := fun s => a*exp (ρ*(s-κ))+exp (ρ*(s-κ))^2-1
  have hD : Continuous D := by fun_prop
  have hp := (htail (l-1/4) (u+1/4) (by linarith) (by linarith)).fill_divisor e he
  have hstrip := polynomial_strip_of_tail ((hD.pow e).mul hH.continuous) (l-1/4) (u+1/4) hp
  obtain ⟨d,C,hC,hbound⟩ := hstrip
  obtain ⟨C',hC',h'⟩ := QuantitativeArithmeticExponentialDivision.quadratic_polynomial_strip
    ρ hρ κ a e (1/4) (by norm_num) H hH l u C d hC
    (fun s hs ht => hbound s ⟨hs,ht⟩)
  exact ⟨d,C',hC',fun s hs => h' s hs.1 hs.2⟩

/-- Repeating a half-unit advance covers every finite vertical strip. -/
theorem stripPolynomial_of_half_step {ι : Type*} (H : ι → ℂ → ℂ)
    (B : ℝ) (hB : ∀ i,PolynomialSubstrips B (H i))
    (hstep : ∀ b : ℝ,(∀ i,PolynomialSubstrips b (H i)) →
      ∀ i,PolynomialSubstrips (b-1/2) (H i)) : ∀ i,StripPolynomial (H i) := by
  have hn : ∀ n : ℕ,∀ i,PolynomialSubstrips (B-(n:ℝ)/2) (H i) := by
    intro n
    induction n with
    | zero => simpa using hB
    | succ n ih =>
      have hh := hstep (B-(n:ℝ)/2) ih
      have he : B-((n+1:ℕ):ℝ)/2=(B-(n:ℝ)/2)-1/2 := by push_cast; ring
      rw [he]
      exact hh
  intro i l u
  obtain ⟨n,hn'⟩ := exists_nat_gt (2*(B-min l u))
  apply hn n i l u
  · have hh := min_le_left l u
    linarith
  · have hh := min_le_right l u
    linarith
#print axioms quadratic_substrip_step
#print axioms stripPolynomial_of_half_step
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticVerticalClearedAlgebraV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded

/-- A finite power of D clears the denominator, leaving a strip-bounded
numerator. Equality is asserted only where D is nonzero. -/
def Cleared (D F : ℂ → ℂ) : Prop :=
  ∃ (n : ℕ) (A : ℂ → ℂ), Bounded A ∧ ∀ s : ℂ,D s≠0 → F s=A s/(D s)^n

theorem Bounded.cleared {D F : ℂ → ℂ} (hf : Bounded F) : Cleared D F :=
  ⟨0,F,hf,fun _ _ => by simp⟩

theorem Cleared.const (D : ℂ → ℂ) (c : ℂ) : Cleared D (fun _ => c) :=
  (Bounded.const c).cleared

theorem Cleared.inv_self (D : ℂ → ℂ) : Cleared D (fun s => (D s)⁻¹) :=
  ⟨1,fun _ => 1,Bounded.const 1,fun _ _ => by simp⟩

theorem Cleared.mul {D F G : ℂ → ℂ} (hf : Cleared D F) (hg : Cleared D G) :
    Cleared D (fun s => F s*G s) := by
  obtain ⟨n,A,hA,ha⟩ := hf
  obtain ⟨m,B,hB,hb⟩ := hg
  refine ⟨n+m,fun s => A s*B s,hA.mul hB,?_⟩
  intro s hs
  dsimp only
  rw [ha s hs,hb s hs,pow_add,mul_div_mul_comm]

theorem Cleared.add {D F G : ℂ → ℂ} (hD : Bounded D)
    (hf : Cleared D F) (hg : Cleared D G) : Cleared D (fun s => F s+G s) := by
  obtain ⟨n,A,hA,ha⟩ := hf
  obtain ⟨m,B,hB,hb⟩ := hg
  refine ⟨n+m,fun s => A s*D s^m+B s*D s^n,
    (hA.mul (hD.pow m)).add (hB.mul (hD.pow n)),?_⟩
  intro s hs
  dsimp only
  rw [ha s hs,hb s hs,pow_add]
  field_simp

theorem Cleared.neg {D F : ℂ → ℂ} (hf : Cleared D F) : Cleared D (fun s => -F s) := by
  obtain ⟨n,A,hA,ha⟩ := hf
  exact ⟨n,fun s => -A s,hA.neg,fun s hs => by dsimp only; rw [ha s hs,neg_div]⟩

theorem Cleared.sub {D F G : ℂ → ℂ} (hD : Bounded D)
    (hf : Cleared D F) (hg : Cleared D G) : Cleared D (fun s => F s-G s) := by
  simpa only [sub_eq_add_neg] using hf.add hD hg.neg

theorem Cleared.pow {D F : ℂ → ℂ} (hf : Cleared D F) (n : ℕ) :
    Cleared D (fun s => F s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using Cleared.const D 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem Cleared.div {D F G : ℂ → ℂ} (hf : Cleared D F)
    (hg : Cleared D (fun s => (G s)⁻¹)) : Cleared D (fun s => F s/G s) := by
  simpa only [div_eq_mul_inv] using hf.mul hg

theorem Cleared.sum {D : ℂ → ℂ} (hD : Bounded D) {ι : Type*}
    (t : Finset ι) (F : ι → ℂ → ℂ) (hF : ∀ i∈t,Cleared D (F i)) :
    Cleared D (fun s => ∑ i∈t,F i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Cleared.const D 0
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add hD
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- Any fixed finite collection admits a common clearing power and bounded
numerators. This avoids expanding the reconstruction matrix. -/
theorem Cleared.uniform {D : ℂ → ℂ} (hD : Bounded D) {ι : Type*}
    [Fintype ι] [Nonempty ι] (F : ι → ℂ → ℂ) (hF : ∀ i,Cleared D (F i)) :
    ∃ (n : ℕ) (A : ι → ℂ → ℂ), (∀ i,Bounded (A i)) ∧
      ∀ i s,D s≠0 → F i s=A i s/(D s)^n := by
  classical
  choose n A ha he using hF
  let d : ℕ := Finset.univ.sup n
  have hn (i : ι) : n i≤d := Finset.le_sup (Finset.mem_univ i)
  refine ⟨d,fun i s => A i s*D s^(d-n i),fun i => (ha i).mul (hD.pow _),?_⟩
  intro i s hs
  rw [he i s hs]
  have hd : d=n i+(d-n i) := (Nat.add_sub_of_le (hn i)).symm
  rw [hd,pow_add]
  field_simp
  simp only [Nat.add_sub_cancel_left]

#print axioms Cleared.uniform
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticQuarticClearingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded

theorem Cleared.inv_factor {D F G : ℂ → ℂ} (hG : Bounded G)
    (he : ∀ s,D s=F s*G s) : Cleared D (fun s => (F s)⁻¹) := by
  refine ⟨1,G,hG,?_⟩
  intro s hs
  have hf : F s≠0 := by intro h; apply hs; rw [he s,h,zero_mul]
  dsimp only
  rw [pow_one]
  field_simp
  exact he s

theorem quartic_inverse_factors {x : ℂ → ℂ} (hx : Bounded x) :
    Cleared (fun s => x s^4-1) (fun s => (x s-1)⁻¹) ∧
    Cleared (fun s => x s^4-1) (fun s => (x s+1)⁻¹) ∧
    Cleared (fun s => x s^4-1) (fun s => (x s^2+1)⁻¹) := by
  have hp := hx.add (Bounded.const 1)
  have hm := hx.sub (Bounded.const 1)
  have hsq := (hx.pow 2).add (Bounded.const 1)
  exact ⟨Cleared.inv_factor (hp.mul hsq) (fun s => by ring),
    Cleared.inv_factor (hm.mul hsq) (fun s => by ring),
    Cleared.inv_factor (hm.mul hp) (fun s => by ring)⟩
#print axioms quartic_inverse_factors
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticRegularizedShiftBoundV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded
open Complex Set

/-- Recover polynomial control of a meromorphic function on a translated
high strip from its entire simple-pole regularization. -/
theorem regularized_shift_polynomial {H G : ℂ → ℂ} (k : ℝ)
    (he : ∀ s : ℂ,s≠(k:ℂ) → H s=(s-(k:ℂ))*G s)
    {b l u : ℝ} (hH : PolynomialSubstrips b H) (c : ℝ)
    (hl : b<l+c) (hu : b<u+c) :
    PolynomialOn {s : ℂ | l≤s.re ∧ s.re≤u ∧ 1≤|s.im|} (fun s => G (s+(c:ℂ))) := by
  let T : Set ℂ := {s : ℂ | l≤s.re ∧ s.re≤u ∧ 1≤|s.im|}
  have hp : PolynomialOn T (fun s => H (s+(c:ℂ))) :=
    (hH.shift c hl hu).mono (fun s hs => ⟨hs.1,hs.2.1⟩)
  have hi := PolynomialOn.inverse_real_shift T (k-c) (fun s hs => hs.2.2)
  apply (hp.mul hi).congr
  intro s hs
  have hn : s+(c:ℂ)≠(k:ℂ) := by
    intro h
    have hh := congrArg Complex.im h
    simp only [add_im,ofReal_im,add_zero] at hh
    have ht := hs.2.2
    rw [hh,abs_zero] at ht
    norm_num at ht
  dsimp only
  rw [he _ hn]
  have ha : s-((k-c:ℝ):ℂ)=s+(c:ℂ)-(k:ℂ) := by push_cast; ring
  rw [ha]
  field_simp [sub_ne_zero.mpr hn]
#print axioms regularized_shift_polynomial
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticTaylorScalarStripGrowthV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded
open Complex

theorem positive_cpow_bounded {c : ℝ} (hc : 0<c) (κ : ℝ) :
    Bounded (fun s : ℂ => (c:ℂ)^(s-(κ:ℂ))) := by
  have he : (fun s : ℂ => (c:ℂ)^(s-(κ:ℂ)))=
      (fun s : ℂ => exp ((Real.log c:ℂ)*(s-(κ:ℂ)))) := by
    funext s
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hc.ne'),← ofReal_log hc.le]
  rw [he]
  exact exponential (Real.log c) κ

theorem taylorRowScalar_stripPolynomial (k : ℕ) {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (χ : ℂ) (n : ℕ) : StripPolynomial (SmallLevelTaylor.taylorRowScalar k L r χ n) := by
  have hb := ((Bounded.const χ).mul (positive_cpow_bounded
    (mul_pos hL (sq_pos_of_ne_zero hr)) ((k:ℝ)/2))).mul
      (Bounded.const ((I*(L:ℂ)*(r:ℂ))^n))
  have he : (((k:ℝ)/2:ℝ):ℂ)=(k:ℂ)/2 := by push_cast; rfl
  change StripPolynomial (fun s : ℂ =>
    χ*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*(I*(L:ℂ)*(r:ℂ))^n*
      Ring.choose (s+(n:ℂ)-(k:ℂ)) n)
  simpa only [he] using
    hb.stripPolynomial.mul (binomial_polynomial_growth k n).stripPolynomial
#print axioms taylorRowScalar_stripPolynomial
end QuantitativeArithmeticVerticalBounded
end
end

/-! ## QuantitativeArithmeticUniformPositiveClearingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticVerticalBounded

theorem Cleared.uniform_positive {D : ℂ → ℂ} (hD : Bounded D) {ι : Type*}
    [Fintype ι] [Nonempty ι] (F : ι → ℂ → ℂ) (hF : ∀ i,Cleared D (F i)) :
    ∃ (n : ℕ) (A : ι → ℂ → ℂ),0<n ∧ (∀ i,Bounded (A i)) ∧
      ∀ i s,D s≠0 → F i s=A i s/(D s)^n := by
  obtain ⟨n,A,hA,he⟩ := Cleared.uniform hD F hF
  refine ⟨n+1,fun i s => A i s*D s,by omega,fun i => (hA i).mul hD,?_⟩
  intro i s hs
  dsimp only
  rw [he i s hs,pow_succ]
  field_simp
#print axioms Cleared.uniform_positive
end QuantitativeArithmeticVerticalBounded
end
end
