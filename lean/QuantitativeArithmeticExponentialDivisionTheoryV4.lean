module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import QuantitativeArithmeticExponentialDivisionSmallV1

/-! Consolidated chapter: QuantitativeArithmeticExponentialDivision. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticExponentialProductDivisionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticExponentialDivision
open Complex Set Metric

def factorProduct (a : ℂ) (c : List ℂ) (z : ℂ) : ℂ :=
  (c.map (fun b => 1-b*exp (a*z))).prod

/-- A finite product of exponential factors can be divided out with a
uniform local sup estimate. The radius grows only with the number of factors. -/
theorem product_local_envelope (a : ℂ) (ha : a≠0) (r : ℝ) (hr : 0<r)
    (har : ‖a‖*r≤1) (c : List ℂ) :
    ∃ K : ℝ,0<K ∧ ∀ G : ℂ → ℂ,Differentiable ℂ G →
      ∀ (z : ℂ) (M : ℝ),0≤M →
      (∀ v : ℂ,‖v-z‖≤2*r*(c.length:ℝ) → ‖factorProduct a c v*G v‖≤M) →
      ‖G z‖≤K*M := by
  induction c with
  | nil =>
    refine ⟨1,by norm_num,?_⟩
    intro G _ z M _ h
    simpa only [factorProduct,List.map_nil,List.prod_nil,one_mul] using h z (by simp)
  | cons b c ih =>
    obtain ⟨K,hK,hc⟩ := ih
    obtain ⟨K1,hK1,hlocal⟩ := small_local_envelope a ha r hr har
    refine ⟨K1*K,mul_pos hK1 hK,?_⟩
    intro G hG z M hM hb
    let H : ℂ → ℂ := fun v => (1-b*exp (a*v))*G v
    have hH : Differentiable ℂ H := by
      apply Differentiable.mul _ hG
      fun_prop
    have hbound : ∀ v : ℂ,‖v-z‖≤2*r → ‖H v‖≤K*M := by
      intro v hv
      apply hc H hH v M hM
      intro u hu
      have huz : ‖u-z‖≤2*r*((b::c).length:ℝ) := by
        have ht := norm_add_le (u-v) (v-z)
        rw [sub_add_sub_cancel] at ht
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith
      have he : factorProduct a c u*H u=factorProduct a (b::c) u*G u := by
        simp only [factorProduct,List.map_cons,List.prod_cons,H]
        ring
      rw [he]
      exact hb u huz
    have hh := hlocal b H G hG (fun _ => rfl) z (K*M) (mul_nonneg hK.le hM) hbound
    simpa only [mul_assoc] using hh

/-- The same product division preserves polynomial growth on compact
vertical strips, after the corresponding arbitrarily small enlargement. -/
theorem product_polynomial_strip (a : ℂ) (ha : a≠0) (r : ℝ) (hr : 0<r)
    (har : ‖a‖*r≤1) (c : List ℂ) :
    ∃ K : ℝ,0<K ∧ ∀ G : ℂ → ℂ,Differentiable ℂ G →
      ∀ (l u C : ℝ) (d : ℕ),0≤C →
      (∀ z : ℂ,l-2*r*(c.length:ℝ)≤z.re → z.re≤u+2*r*(c.length:ℝ) →
        ‖factorProduct a c z*G z‖≤C*(1+‖z‖)^d) →
      ∀ z : ℂ,l≤z.re → z.re≤u →
        ‖G z‖≤(K*C*(1+2*r*(c.length:ℝ))^d)*(1+‖z‖)^d := by
  obtain ⟨K,hK,hlocal⟩ := product_local_envelope a ha r hr har c
  refine ⟨K,hK,?_⟩
  intro G hG l u C d hC hA z hzl hzu
  let R : ℝ := 2*r*(c.length:ℝ)
  have hR : 0≤R := by dsimp [R]; positivity
  have hb : ∀ v : ℂ,‖v-z‖≤R → ‖factorProduct a c v*G v‖≤C*(1+R)^d*(1+‖z‖)^d := by
    intro v hv
    have hvre : |v.re-z.re|≤R := by
      simpa only [Complex.sub_re] using (abs_re_le_norm (v-z)).trans hv
    have hnorm : ‖v‖≤‖z‖+R := by
      have ht := norm_add_le (v-z) z
      rw [sub_add_cancel] at ht
      linarith
    calc
      ‖factorProduct a c v*G v‖≤C*(1+‖v‖)^d := hA v (by linarith [(abs_le.mp hvre).1]) (by linarith [(abs_le.mp hvre).2])
      _ ≤ C*((1+R)*(1+‖z‖))^d := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [norm_nonneg z]
      _ = C*(1+R)^d*(1+‖z‖)^d := by rw [mul_pow]; ring
  have hh := hlocal G hG z (C*(1+R)^d*(1+‖z‖)^d) (by positivity) hb
  convert hh using 1
  ring
#print axioms product_local_envelope
#print axioms product_polynomial_strip
end QuantitativeArithmeticExponentialDivision
end
end

/-! ## QuantitativeArithmeticQuadraticExponentialDivisionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticExponentialDivision
open Complex

theorem factorProduct_append (a : ℂ) (c d : List ℂ) (s : ℂ) :
    factorProduct a (c++d) s=factorProduct a c s*factorProduct a d s := by
  simp only [factorProduct,List.map_append,List.prod_append]

theorem factorProduct_replicate (a b : ℂ) (n : ℕ) (s : ℂ) :
    factorProduct a (List.replicate n b) s=(1-b*exp (a*s))^n := by
  simp only [factorProduct,List.map_replicate,List.prod_replicate]

/-- The only nonmonomial divisor in the nonzero-eigenvalue charts splits
into two exponential factors, with multiplicity allowed. -/
theorem quadratic_factorization (ρ κ a : ℂ) (n : ℕ) :
    ∃ c : List ℂ,c.length=2*n ∧ ∀ s : ℂ,
      factorProduct ρ c s=(-1:ℂ)^n*(a*exp (ρ*(s-κ))+exp (ρ*(s-κ))^2-1)^n := by
  let d : ℂ := (a^2+4)^((2:ℂ)⁻¹)
  have hd : d^2=a^2+4 := cpow_nat_inv_pow _ (by decide : (2:ℕ)≠0)
  let b : ℂ := (a+d)/2*exp (-ρ*κ)
  let c : ℂ := (a-d)/2*exp (-ρ*κ)
  have he (s : ℂ) : (1-b*exp (ρ*s))*(1-c*exp (ρ*s))=
      -(a*exp (ρ*(s-κ))+exp (ρ*(s-κ))^2-1) := by
    have hx : exp (ρ*(s-κ))=exp (-ρ*κ)*exp (ρ*s) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hx]
    dsimp only [b,c]
    linear_combination -(exp (-ρ*κ)*exp (ρ*s))^2/4*hd
  refine ⟨List.replicate n b++List.replicate n c,?_,?_⟩
  · simp only [List.length_append,List.length_replicate]
    omega
  · intro s
    rw [factorProduct_append,factorProduct_replicate,factorProduct_replicate,← mul_pow,he,neg_pow]

/-- Clearing a finite power of the quadratic divisor preserves polynomial
strip bounds after an arbitrarily small enlargement. -/
theorem quadratic_polynomial_strip (ρ : ℂ) (hρ : ρ≠0) (κ a : ℂ)
    (n : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ (G : ℂ → ℂ),Differentiable ℂ G → ∀ (l u C : ℝ) (d : ℕ),0≤C →
      (∀ z : ℂ,l-ε≤z.re → z.re≤u+ε →
        ‖(a*exp (ρ*(z-κ))+exp (ρ*(z-κ))^2-1)^n*G z‖≤C*(1+‖z‖)^d) →
      ∃ C' : ℝ,0≤C' ∧ ∀ z : ℂ,l≤z.re → z.re≤u → ‖G z‖≤C'*(1+‖z‖)^d := by
  obtain ⟨cs,hlen,hfactor⟩ := quadratic_factorization ρ κ a n
  let r : ℝ := min (ε/(4*((n:ℝ)+1))) (1/(‖ρ‖+1))
  have hr : 0<r := lt_min (by positivity) (by positivity)
  have hr1 : r≤1/(‖ρ‖+1) := min_le_right _ _
  have hre : r≤ε/(4*((n:ℝ)+1)) := min_le_left _ _
  have har : ‖ρ‖*r≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0<‖ρ‖+1)).mp hr1
    nlinarith
  have hrad : 2*r*(cs.length:ℝ)≤ε := by
    have hh := (le_div_iff₀ (by positivity : 0<4*((n:ℝ)+1))).mp hre
    rw [hlen]
    push_cast
    nlinarith
  obtain ⟨K,hK,hstrip⟩ := product_polynomial_strip ρ hρ r hr har cs
  intro G hG l u C d hC hA
  refine ⟨K*C*(1+2*r*(cs.length:ℝ))^d,by positivity,?_⟩
  apply hstrip G hG l u C d hC
  intro z hzl hzu
  rw [hfactor,mul_assoc,norm_mul,norm_pow]
  norm_num only [norm_neg,norm_one,one_pow,one_mul]
  exact hA z (by linarith) (by linarith)
#print axioms quadratic_factorization
#print axioms quadratic_polynomial_strip
end QuantitativeArithmeticExponentialDivision
end
end
