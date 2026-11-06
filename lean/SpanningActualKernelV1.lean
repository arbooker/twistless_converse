module

/- The actual radius Q/sqrt(lcm(N,q^2)) and its kernel operations. -/
public import SpanningPrimitiveCompleteV1
public import SpanningLevelArithmeticV1
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace SpanningActualKernel

open SpanningTraceAlgebra SpanningWindows SpanningLevelArithmetic SpanningPrimitiveComplete

noncomputable def radius (N Q q : ℕ) : ℝ := Q / Real.sqrt (level N q)

theorem radius_nonneg (N Q q : ℕ) : 0≤radius N Q q :=
  div_nonneg (Nat.cast_nonneg Q) (Real.sqrt_nonneg _)

theorem radius_scale (N m Q q : ℕ) : radius N (m*Q) q=(m:ℝ)*radius N Q q := by
  simp only [radius,Nat.cast_mul,mul_div_assoc]

theorem radius_coprime_mul {N p : ℕ} (hp : 0<p) (hc : Nat.Coprime N p) (Q q : ℕ) :
    radius N (p*Q) (p*q)=radius N Q q := by
  unfold radius
  rw [level_coprime_mul hc,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,
    Real.sqrt_mul (sq_nonneg (p:ℝ)),Real.sqrt_sq (Nat.cast_nonneg p)]
  exact mul_div_mul_left _ _ (by exact_mod_cast (Nat.ne_of_gt hp))

theorem radius_divisor_mono {N : ℕ} (hN : 0<N) (Q d q : ℕ) (hd : d∣q) :
    radius N Q q≤radius N Q d := by
  by_cases hq : q=0
  · subst q
    simpa [radius,level] using radius_nonneg N Q d
  have hq0 : 0<q := Nat.pos_of_ne_zero hq
  have hd0 : 0<d := Nat.pos_of_dvd_of_pos hd hq0
  have hL := Nat.le_of_dvd (level_pos hN hq0) (level_dvd (N:=N) hd)
  have hs := Real.sqrt_le_sqrt (show (level N d:ℝ)≤level N q by exact_mod_cast hL)
  have hp : 0<Real.sqrt (level N d) := Real.sqrt_pos.mpr (by exact_mod_cast level_pos hN hd0)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg Q) hp hs

variable {F : Type*} [AddCommMonoid F]

abbrev Kernel (N Q : ℕ) (v : ℤ → F) := PrimitiveKernel (radius N) Q v
abbrev Augmented (N : ℕ) (L : Set ℕ) (Q : ℕ) (v : ℤ → F) :=
  AugmentedKernel (radius N) L Q v

theorem complete_iff_primitive {N Q : ℕ} (hN : 0<N) (hQ : 0<Q) (v : ℤ → F) :
    Kernel N Q v ↔ CompleteKernel (radius N) Q v :=
  kernel_equivalence hQ (radius_divisor_mono hN Q) v

theorem kernel_restrict {N m Q t : ℕ} {v : ℤ → F}
    (hv : Kernel N (m*Q) v) (ht : t<m) : Kernel N Q (restrict m t v) :=
  primitive_kernel_restrict (fun q _ => radius_scale N m Q q) hv ht

theorem kernel_trace {N p Q : ℕ} (hN : 0<N) (hp : 0<p) (hQ : 0<Q)
    (hc : Nat.Coprime N p) {v : ℤ → F} (hv : Kernel N (p*Q) v) :
    Kernel N Q (trace p Q v) := by
  apply (complete_iff_primitive hN hQ _).mpr
  apply complete_kernel_trace hp (fun q _ => radius_coprime_mul hp hc Q q)
  exact (complete_iff_primitive hN (Nat.mul_pos hp hQ) v).mp hv

theorem augmented_restrict {N m Q t : ℕ} {L : Set ℕ}
    (hdiv : ∀ ell∈L, ell∣Q) {v : ℤ → F}
    (hv : Augmented N L (m*Q) v) (ht : t<m) : Augmented N L Q (restrict m t v) :=
  augmented_kernel_restrict (fun q _ => radius_scale N m Q q) hdiv hv ht

theorem augmented_trace {N p Q : ℕ} {L : Set ℕ} (hp : 0<p) (hc : Nat.Coprime N p)
    (hdiv : ∀ ell∈L, ell∣Q) {v : ℤ → F} (hv : Augmented N L (p*Q) v) :
    Augmented N L Q (trace p Q v) :=
  augmented_kernel_trace hp (fun q _ => radius_coprime_mul hp hc Q q) hdiv hv

theorem zero_at_multiples {N m Q : ℕ} (hm : 0<m)
    (hz : ∀ v : ℤ → F, Kernel N Q v → v=0) :
    ∀ v : ℤ → F, Kernel N (m*Q) v → v=0 :=
  primitive_kernel_zero_at_multiples hm (fun q _ => radius_scale N m Q q) hz

#print axioms kernel_trace
#print axioms augmented_trace
#print axioms zero_at_multiples

end SpanningActualKernel
