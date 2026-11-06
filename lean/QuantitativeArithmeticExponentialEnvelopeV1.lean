module

public import QuantitativeHolomorphicGrowingFoldV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticEnvelope

/-- Uniform polynomial and exponential envelopes on the logarithmic
accuracy parameter. Constants are independent of that parameter. -/
def Poly (d : ℕ) (f : ℝ → ℝ) : Prop := ∃C : ℝ,0≤C ∧ ∀u : ℝ,1≤u → f u≤C*u^d
def Exp (d : ℕ) (f : ℝ → ℝ) : Prop := ∃C : ℝ,0≤C ∧ ∀u : ℝ,1≤u → f u≤Real.exp (C*u^d)

variable {d r : ℕ} {f g : ℝ → ℝ}

theorem Poly.mono (hf : Poly d f) (hfg : ∀u,1≤u → g u≤f u) : Poly d g := by
  obtain ⟨C,hC,h⟩ := hf
  exact ⟨C,hC,fun u hu => (hfg u hu).trans (h u hu)⟩

theorem Exp.mono (hf : Exp d f) (hfg : ∀u,1≤u → g u≤f u) : Exp d g := by
  obtain ⟨C,hC,h⟩ := hf
  exact ⟨C,hC,fun u hu => (hfg u hu).trans (h u hu)⟩

theorem Poly.const (c : ℝ) (d : ℕ) : Poly d (fun _ => c) := by
  refine ⟨|c|,abs_nonneg _,fun u hu => ?_⟩
  exact (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) (one_le_pow₀ hu))

theorem Poly.id : Poly 1 (fun u => u) := ⟨1,zero_le_one,fun _ _ => by simp⟩

theorem Poly.weaken (hf : Poly d f) (hdr : d≤r) : Poly r f := by
  obtain ⟨C,hC,h⟩ := hf
  exact ⟨C,hC,fun u hu => (h u hu).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu hdr) hC)⟩

theorem Exp.weaken (hf : Exp d f) (hdr : d≤r) : Exp r f := by
  obtain ⟨C,hC,h⟩ := hf
  exact ⟨C,hC,fun u hu => (h u hu).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu hdr) hC))⟩

theorem Poly.add (hf : Poly d f) (hg : Poly d g) : Poly d (fun u => f u+g u) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,add_nonneg hC hD,fun u hu => ?_⟩
  simpa only [add_mul] using add_le_add (hf u hu) (hg u hu)

theorem Poly.mul (hf : Poly d f) (hg : Poly r g) (hg0 : ∀u,1≤u → 0≤g u) :
    Poly (d+r) (fun u => f u*g u) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C*D,mul_nonneg hC hD,fun u hu => ?_⟩
  have hh := mul_le_mul (hf u hu) (hg u hu) (hg0 u hu) (mul_nonneg hC (pow_nonneg (zero_le_one.trans hu) d))
  convert hh using 1
  rw [pow_add]
  ring

theorem Poly.exp (hf : Poly d f) : Exp d (fun u => Real.exp (f u)) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨C,hC,fun u hu => Real.exp_le_exp.mpr (hf u hu)⟩

theorem Poly.toExp (hf : Poly d f) : Exp d f := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨C,hC,fun u hu => (hf u hu).trans (by linarith [Real.add_one_le_exp (C*u^d)])⟩

theorem Exp.const (c : ℝ) (d : ℕ) : Exp d (fun _ => c) := (Poly.const c d).toExp

theorem Exp.mul (hf : Exp d f) (hg : Exp d g) (hg0 : ∀u,1≤u → 0≤g u) :
    Exp d (fun u => f u*g u) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,add_nonneg hC hD,fun u hu => ?_⟩
  have hh := mul_le_mul (hf u hu) (hg u hu) (hg0 u hu) (Real.exp_nonneg _)
  apply hh.trans_eq
  rw [←Real.exp_add,←add_mul]

theorem Exp.add (hf : Exp d f) (hg : Exp d g) : Exp d (fun u => f u+g u) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D+2,by positivity,fun u hu => ?_⟩
  have hu0 : 0≤u^d := pow_nonneg (zero_le_one.trans hu) _
  have hu1 : 1≤u^d := one_le_pow₀ hu
  have hF : f u≤Real.exp ((C+D)*u^d) := (hf u hu).trans (Real.exp_le_exp.mpr (by nlinarith))
  have hG : g u≤Real.exp ((C+D)*u^d) := (hg u hu).trans (Real.exp_le_exp.mpr (by nlinarith))
  have h2 : (2:ℝ)≤Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  calc
    f u+g u ≤ 2*Real.exp ((C+D)*u^d) := by linarith
    _ ≤ Real.exp 2*Real.exp ((C+D)*u^d) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = Real.exp (2+(C+D)*u^d) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem Exp.natpow (hf : Exp d f) (hf0 : ∀u,1≤u → 0≤f u)
    (n : ℝ → ℕ) (hn : Poly r (fun u => (n u:ℝ))) :
    Exp (d+r) (fun u => f u^(n u)) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hn⟩ := hn
  refine ⟨C*D,mul_nonneg hC hD,fun u hu => ?_⟩
  apply (pow_le_pow_left₀ (hf0 u hu) (hf u hu) (n u)).trans
  rw [←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (hn u hu) (mul_nonneg hC (pow_nonneg (zero_le_one.trans hu) d))
  convert hh using 1
  rw [pow_add]
  ring

theorem Exp.binaryDepth (hf : Exp d f) (hf0 : ∀u,1≤u → 0≤f u) :
    Poly d (fun u => (QuantitativeHolomorphic.Schedule.binaryDepth (f u):ℝ)) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨(Real.log 6+C)/Real.log 2,?_,fun u hu => ?_⟩
  · exact div_nonneg (add_nonneg (Real.log_nonneg (by norm_num)) hC) (Real.log_pos (by norm_num)).le
  · exact QuantitativeHolomorphic.Schedule.binaryDepth_le_exponential
      (hf0 u hu) hC (one_le_pow₀ hu) (hf u hu)

theorem Exp.ceil (hf : Exp d f) (hf0 : ∀u,1≤u → 0≤f u) :
    Exp d (fun u => ((⌈f u⌉₊+1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨C+Real.log 3,add_nonneg hC (Real.log_nonneg (by norm_num)),fun u hu =>
    QuantitativeHolomorphic.Schedule.ceil_add_one_le_exponential
      (hf0 u hu) hC (one_le_pow₀ hu) (hf u hu)⟩

#print axioms Exp.natpow
#print axioms Exp.binaryDepth
#print axioms Exp.ceil
end QuantitativeArithmeticEnvelope
