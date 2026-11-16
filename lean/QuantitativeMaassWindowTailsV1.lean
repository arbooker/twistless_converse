module

public import QuantitativeMaassWindowTranslationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace QuantitativeMaass

/-- A window separated from a point by d has a tail controlled by any
absolute moment of the actual positive smoothing kernel. -/
theorem smoothedWindow_distance_moment (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (R : ℝ) (hR : 0<R) (S : Set ℝ) (hS : MeasurableSet S) (x d : ℝ)
    (hd : 0≤d) (hsep : ∀ u∈S,d≤|x-u|) (k : ℕ) :
    d^k*smoothedWindow K R S x ≤ (∫ u,|u|^k*K u)/R^k := by
  have hk := (scaledWindowKernel_integrable K R hR).comp_sub_left x
  have hm := (scaledWindowKernel_moment_integrable K hK R hR k).comp_sub_left x
  have hn (u : ℝ) : 0≤scaledWindowKernel K R (x-u) := mul_nonneg hR.le (hK _)
  calc
    _ = ∫ u in S,d^k*scaledWindowKernel K R (x-u) := (integral_const_mul _ _).symm
    _ ≤ ∫ u in S,|x-u|^k*scaledWindowKernel K R (x-u) := by
      apply setIntegral_mono_on (hk.const_mul _).integrableOn hm.integrableOn hS
      intro u hu
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd (hsep u hu) k) (hn u)
    _ ≤ ∫ u,|x-u|^k*scaledWindowKernel K R (x-u) :=
      setIntegral_le_integral hm (Filter.Eventually.of_forall (fun u => mul_nonneg (pow_nonneg (abs_nonneg _) k) (hn u)))
    _ = (∫ u,|u|^k*K u)/R^k := by
      rw [integral_sub_left_eq_self (fun u => |u|^k*scaledWindowKernel K R u) volume x,
        scaledWindowKernel_moment K R hR k]

theorem smoothedWindow_distance_tail (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (R : ℝ) (hR : 0<R) (S : Set ℝ) (hS : MeasurableSet S) (x d : ℝ)
    (hd : 0<d) (hsep : ∀ u∈S,d≤|x-u|) (k : ℕ) :
    smoothedWindow K R S x ≤ (∫ u,|u|^k*K u)/(R*d)^k := by
  have h := smoothedWindow_distance_moment K hK R hR S hS x d hd.le hsep k
  have h' : smoothedWindow K R S x ≤ ((∫ u,|u|^k*K u)/R^k)/d^k :=
    (le_div_iff₀ (pow_pos hd k)).mpr (by simpa only [mul_comm] using h)
  convert h' using 1
  rw [div_div,mul_pow]

theorem squaredWindow_distance_tail (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (R : ℝ) (hR : 0<R) (S : Set ℝ) (hS : MeasurableSet S) (x d : ℝ)
    (hd : 0<d) (hsep : ∀ u∈S,d≤|x-u|) (k : ℕ) :
    (smoothedWindow K R S x)^2 ≤ (∫ u,|u|^k*K u)^2/(R*d)^(2*k) := by
  have h := smoothedWindow_distance_tail K hK R hR S hS x d hd hsep k
  have hn : 0≤smoothedWindow K R S x := integral_nonneg
    (fun u => mul_nonneg hR.le (hK (R*(x-u))))
  have hsq := pow_le_pow_left₀ hn h 2
  convert hsq using 1
  rw [div_pow,← pow_mul]
  rw [Nat.mul_comm k 2]

/-- Separation of a shrunken interval from the complement of the original
interval uses only order, and is uniform in its center and width. -/
theorem shrunken_interval_separation (a b δ x u : ℝ)
    (hx : x∉Icc a b) (hu : u∈Icc (a+δ) (b-δ)) : δ≤|x-u| := by
  by_cases hxa : x<a
  · have h := neg_le_abs (x-u)
    linarith [hu.1]
  · have hxb : b<x := by
      by_contra hn
      exact hx ⟨le_of_not_gt hxa,le_of_not_gt hn⟩
    have h := le_abs_self (x-u)
    linarith [hu.2]

theorem shrunken_symmetric_window_separation (t ε δ x u : ℝ)
    (hx : x∉Icc t (t+ε)∪Icc (-(t+ε)) (-t))
    (hu : u∈Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) : δ≤|x-u| := by
  have hp : x∉Icc t (t+ε) := fun h => hx (Or.inl h)
  have hn : x∉Icc (-(t+ε)) (-t) := fun h => hx (Or.inr h)
  rcases hu with hu|hu
  · exact shrunken_interval_separation t (t+ε) δ x u hp hu
  · apply shrunken_interval_separation (-(t+ε)) (-t) δ x u hn
    constructor <;> linarith [hu.1,hu.2]

/-- Every power of R*δ is available outside the original symmetric window,
with a constant depending only on the fixed kernel and the power. -/
theorem shrunken_squaredWindow_tail (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (t ε δ R x : ℝ) (hδ : 0<δ) (hR : 0<R)
    (hx : x∉Icc t (t+ε)∪Icc (-(t+ε)) (-t)) (k : ℕ) :
    (smoothedWindow K R (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) x)^2 ≤
      (∫ u,|u|^k*K u)^2/(R*δ)^(2*k) :=
  squaredWindow_distance_tail K hK R hR _ (measurableSet_Icc.union measurableSet_Icc)
    x δ hδ (fun u hu => shrunken_symmetric_window_separation t ε δ x u hx hu) k

/-- A version of the moment estimate with a nonsingular, uniform decay
weight. It applies also at zero separation. -/
theorem smoothedWindow_uniform_distance_bound (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (S : Set ℝ) (hS : MeasurableSet S) (x d : ℝ)
    (hd : 0≤d) (hsep : ∀ u∈S,d≤|x-u|) (k : ℕ) :
    (1+R*d)^k*smoothedWindow K R S x ≤ 2^k*(1+∫ u,|u|^k*K u) := by
  let m : ℝ := ∫ u,|u|^k*K u
  have hm0 : 0≤m := integral_nonneg (fun u => mul_nonneg (pow_nonneg (abs_nonneg _) k) (hK u))
  have hg := smoothedWindow_mem_unit K hK hm R hR S x
  have hRd : 0≤R*d := mul_nonneg hR.le hd
  by_cases hsmall : R*d≤1
  · have hp : (1+R*d)^k≤(2:ℝ)^k := pow_le_pow_left₀ (by positivity) (by linarith) k
    calc
      _ ≤ (1+R*d)^k*1 := mul_le_mul_of_nonneg_left hg.2 (by positivity)
      _ ≤ (2:ℝ)^k := by simpa using hp
      _ ≤ _ := by change (2:ℝ)^k≤2^k*(1+m); nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) k) hm0]
  · have hp : (1+R*d)^k≤((2:ℝ)*R*d)^k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    have hmoment := smoothedWindow_distance_moment K hK R hR S hS x d hd hsep k
    calc
      _ ≤ ((2:ℝ)*R*d)^k*smoothedWindow K R S x := mul_le_mul_of_nonneg_right hp hg.1
      _ = (2^k*R^k)*(d^k*smoothedWindow K R S x) := by rw [mul_pow,mul_pow]; ring
      _ ≤ (2^k*R^k)*(m/R^k) := mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = 2^k*m := by field_simp
      _ ≤ _ := by change 2^k*m≤2^k*(1+m); nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) k]

theorem squaredWindow_uniform_distance_tail (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (S : Set ℝ) (hS : MeasurableSet S) (x d : ℝ)
    (hd : 0≤d) (hsep : ∀ u∈S,d≤|x-u|) (k : ℕ) :
    (smoothedWindow K R S x)^2 ≤
      (2^k*(1+∫ u,|u|^k*K u))^2/(1+R*d)^(2*k) := by
  have hp : 0<(1+R*d)^k := pow_pos (by positivity) k
  have h := smoothedWindow_uniform_distance_bound K hK hm R hR S hS x d hd hsep k
  have hb : smoothedWindow K R S x ≤ (2^k*(1+∫ u,|u|^k*K u))/(1+R*d)^k :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using h)
  have hs := pow_le_pow_left₀ (smoothedWindow_mem_unit K hK hm R hR S x).1 hb 2
  convert hs using 1
  rw [div_pow,← pow_mul,Nat.mul_comm k 2]

/-- Constants uniform in t, epsilon, delta and R for the actual squared
spectral window outside the original closed window. -/
theorem shrunken_squaredWindow_uniform_tail (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (t ε δ R x : ℝ) (hδ : 0≤δ) (hR : 0<R)
    (hx : x∉Icc t (t+ε)∪Icc (-(t+ε)) (-t)) (k : ℕ) :
    (smoothedWindow K R (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) x)^2 ≤
      (2^k*(1+∫ u,|u|^k*K u))^2/(1+R*δ)^(2*k) :=
  squaredWindow_uniform_distance_tail K hK hm R hR _ (measurableSet_Icc.union measurableSet_Icc)
    x δ hδ (fun u hu => shrunken_symmetric_window_separation t ε δ x u hx hu) k

/-- Bounded windows have uniform polynomial decay at infinity for every
scale R>=1, with an explicit dependence on their containing interval. -/
theorem smoothedWindow_bounded_weight (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 1≤R) (S : Set ℝ) (hS : MeasurableSet S) (A : ℝ) (hA : 0≤A)
    (hSA : ∀ u∈S,|u|≤A) (x : ℝ) (k : ℕ) :
    (1+|x|)^k*smoothedWindow K R S x ≤
      (1+A)^k*(2^k*(1+∫ u,|u|^k*K u)) := by
  let d : ℝ := max 0 (|x|-A)
  have hd : 0≤d := le_max_left _ _
  have hsep (u : ℝ) (hu : u∈S) : d≤|x-u| := by
    apply max_le (abs_nonneg _)
    have h := abs_sub_abs_le_abs_sub x u
    linarith [hSA u hu]
  have hdx : |x|≤A+d := by have h := le_max_right 0 (|x|-A); dsimp [d]; linarith
  have hR0 : 0<R := by linarith
  have hsize : 1+|x|≤(1+A)*(1+R*d) := by
    nlinarith [mul_nonneg hA hd,mul_nonneg (sub_nonneg.mpr hR) hd,
      mul_nonneg hA (mul_nonneg (sub_nonneg.mpr hR) hd)]
  have hpow := pow_le_pow_left₀ (by positivity : 0≤1+|x|) hsize k
  have hg := smoothedWindow_mem_unit K hK hm R hR0 S x
  have hb := smoothedWindow_uniform_distance_bound K hK hm R hR0 S hS x d hd hsep k
  calc
    _ ≤ ((1+A)*(1+R*d))^k*smoothedWindow K R S x := mul_le_mul_of_nonneg_right hpow hg.1
    _ = (1+A)^k*((1+R*d)^k*smoothedWindow K R S x) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

theorem squaredWindow_principal_energy_weight (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 1≤R) (S : Set ℝ) (hS : MeasurableSet S) (A : ℝ) (hA : 0≤A)
    (hSA : ∀ u∈S,|u|≤A) (e : ℝ) (he : 1/4≤e) :
    (e+1)^8*(smoothedWindow K R S (Real.sqrt (e-1/4)))^2 ≤
      2^8*((1+A)^8*(2^8*(1+∫ u,|u|^8*K u)))^2 := by
  let r := Real.sqrt (e-1/4)
  have hr : 0≤r := Real.sqrt_nonneg _
  have hr2 : r^2=e-1/4 := Real.sq_sqrt (by linarith)
  have henergy : e+1≤2*(1+|r|)^2 := by rw [abs_of_nonneg hr]; nlinarith
  have hpow := pow_le_pow_left₀ (by linarith : 0≤e+1) henergy 8
  have hR0 : 0<R := by linarith
  have hg := smoothedWindow_mem_unit K hK hm R hR0 S r
  have hweight := smoothedWindow_bounded_weight K hK hm R hR S hS A hA hSA r 8
  have hsq := pow_le_pow_left₀ (mul_nonneg (by positivity) hg.1) hweight 2
  calc
    _ ≤ (2*(1+|r|)^2)^8*(smoothedWindow K R S r)^2 :=
      mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
    _ = 2^8*((1+|r|)^8*smoothedWindow K R S r)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- Summability on the principal part of any actual orthonormal cuspidal
eigenfamily. Exceptional energies are excluded explicitly here; no analytic
continuation of the window is silently assumed. -/
theorem cuspidal_principal_squaredWindow_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 1≤R) (S : Set ℝ) (hS : MeasurableSet S) (A : ℝ) (hA : 0≤A)
    (hSA : ∀ u∈S,|u|≤A) :
    Summable (fun i => if 1/4≤e i then
      (smoothedWindow K R S (Real.sqrt (e i-1/4)))^2 else 0) := by
  classical
  let C : ℝ := 2^8*((1+A)^8*(2^8*(1+∫ u,|u|^8*K u)))^2
  have hC : 0≤C := mul_nonneg (by norm_num) (sq_nonneg _)
  have hmajor : Summable (fun i => C/(e i+1)^8) := by
    simpa only [mul_one_div] using
      (cuspidal_inverse_eighth_summable N hN v hv hcusp e he hgraph).mul_left C
  apply Summable.of_nonneg_of_le (fun i => by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl) _ hmajor
  intro i
  have hei := he i
  split_ifs with hi
  · apply (le_div_iff₀ (pow_pos (by linarith : 0<e i+1) 8)).mpr
    rw [mul_comm]
    exact squaredWindow_principal_energy_weight K hK hm R hR S hS A hA hSA (e i) hi
  · exact div_nonneg hC (pow_nonneg (by linarith) 8)

#print axioms smoothedWindow_bounded_weight
#print axioms squaredWindow_principal_energy_weight
#print axioms cuspidal_principal_squaredWindow_summable

#print axioms smoothedWindow_uniform_distance_bound
#print axioms squaredWindow_uniform_distance_tail
#print axioms shrunken_squaredWindow_uniform_tail

#print axioms smoothedWindow_distance_moment
#print axioms smoothedWindow_distance_tail
#print axioms squaredWindow_distance_tail
#print axioms shrunken_interval_separation
#print axioms shrunken_symmetric_window_separation
#print axioms shrunken_squaredWindow_tail

end QuantitativeMaass
