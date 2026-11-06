module

public import QuantitativeArithmeticMixedGridDetectionV1
public import QuantitativeArithmeticRetainedPrimeChoiceV1
public import GridBufferedDetectionV1
public import SpanningKernelDifferencesV1
public import QuantitativeArithmeticGoodLabelWindowsV1
public import QuantitativeArithmeticRetainedConcentrationV1

@[expose] public section

namespace QuantitativeArithmeticRetainedGrid

open GridParameters GridSelectedWindows GridPrimeParts GridAdmissibleGap
  GridSupportedDetection GridLabelDetection GridCarrier CompleteRowCosets
  SpanningActualKernel SpanningWindows SpanningTraceAlgebra GridBufferedDetection
  QuantitativeArithmeticMixedGridDetection QuantitativeArithmeticRetainedPrimeChoice

/-- Full prime traces have no window constraint. -/
theorem prime_coset_zero {K : Type*} [AddCommMonoid K] {G v p : ℕ}
    (hG : 0 < G) (hv : 0 < v) (hp : 0 < p) (hpG : p ∣ G) (f : ℤ → K) (hcyc : Cyclic (G*v) f)
    (hz : trace p ((G*v)/p) f = 0) (u : ℤ) :
    cosetSum (G*v) ((G/p)*v) u f = 0 := by
  have hD : 0 < (G/p)*v := Nat.mul_pos
    (Nat.div_pos (Nat.le_of_dvd hG hpG) hp) hv
  have he : p*((G/p)*v) = G*v := by rw [←mul_assoc, Nat.mul_div_cancel' hpG]
  have hdiv : G*v/p = (G/p)*v := by rw [←he, Nat.mul_div_cancel_left _ hp]
  have hh := trace_coset_sum hp hD u f (by simpa only [he] using hcyc)
  rw [he] at hh
  rw [hdiv] at hz
  exact hh.symm.trans (congrFun hz u)

/-- Given the chosen legal windows, complete traces at retained primes
close every bad-label row in the grid detector. -/
theorem detect_from_windows {N G H R : ℕ} (hN : 0 < N) (hG : 0 < G)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPG : ∀ p ∈ P, p ∣ G)
    (hlarge : N < (∏ p ∈ P, p)^2) (_hR : 0 < R)
    (r : Fin G → ℕ)
    (hr : ∀ a, 0 < r a ∧ Nat.Coprime (r a) G ∧ r a ∣ H ∧ r a ≤ R ∧
      Nat.ModEq (labelModulus a) (r a*a.val) (labelModulus a/labelOrder a))
    (v : ℕ) (hv0 : 0 < v) (hHv : H ∣ v) (hv : 16*R ≤ v)
    (hwin : ∀ a, GoodLabel N a → ∀ t : Offsets (v/(8*R)),
      Legal (radius N (G*v) (primePart G (fun p => ¬p ∣ labelOrder a)*r a))
        (((labelModulus a/labelOrder a)*(v/r a) : ℕ)+t.val) ∧
      3*(v : ℝ)/(40*R)-1 ≤
        radius N (G*v) (primePart G (fun p => ¬p ∣ labelOrder a)*r a)-1-
          ((((labelModulus a/labelOrder a)*(v/r a) : ℕ) : ℤ)+t.val : ℤ))
    {K : Type*} [AddCommMonoid K] (f : ℤ → K) (hcyc : Cyclic (G*v) f)
    (hsupport : ∀ j : Fin (G*v), j ∉ Set.range (gridIndex hG hv0 (v/(8*R))) → f j.val = 0)
    (hrows : BufferedZero N (G*v) (3*(v : ℝ)/(40*R)-1) f)
    (htraces : ∀ p ∈ P, trace p ((G*v)/p) f = 0) : f = 0 := by
  classical
  obtain ⟨p,hp⟩ := exists_prime_choices hN hG P hP hlarge
  let w := fun a : Fin G => v/r a
  let c := fun a : Fin G => labelModulus a/labelOrder a
  have hrv : ∀ a, r a ∣ v := fun a => (hr a).2.2.1.trans hHv
  have hwv : ∀ a, v = r a*w a := fun a => (Nat.mul_div_cancel' (hrv a)).symm
  have hest := fun a => quotient_estimates (hr a).1 (hr a).2.2.2.1 hv (hrv a)
  have hJv : 2*(v/(8*R)) < v := (hest ⟨0,hG⟩).2.2
  apply mixed_grid_detect hG hv0 hJv (GoodLabel N) r w c p
    (fun a _ => (hest a).1) (fun a _ => hwv a)
    (fun a _ => by
      have he := row_factorization hG a (hwv a)
      exact ⟨primePart G (fun p => ¬p ∣ labelOrder a)*r a,by rw [←he]; ring⟩)
    (fun a _ => (hest a).2.1)
    (fun a _ => ((hr a).2.1.of_dvd_right (part_dvd G _)).symm)
    (fun a _ => (hr a).2.2.2.2)
    (fun a ha => (hp a ha).2.1) (fun a ha => hPG _ (hp a ha).1)
    (fun a ha => (hp a ha).2.2) f hcyc hsupport
  · intro a ha t
    have hmp : 0 < labelModulus a := Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hG) _)
    have hdp : 0 < primePart G (fun p => ¬p ∣ labelOrder a) :=
      Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hG) _)
    exact coset_zero_of_buffer (Nat.mul_pos hdp (hr a).1) (Nat.mul_pos hmp (hest a).1)
      (row_factorization hG a (hwv a)) hcyc hrows _ (hwin a ha t).1 (hwin a ha t).2
  · intro a ha t
    exact prime_coset_zero hG hv0 ((hp a ha).2.1.pos) (hPG _ (hp a ha).1) f hcyc
      (htraces _ (hp a ha).1) _

/-- A finite retained set whose product exceeds `sqrt N` supplies every
missing row. This is unconditional grid detection for arbitrary levels. -/
theorem exists_buffered_grid {N G : ℕ} (hN : 0 < N) (hG : 0 < G) (hNG : N ∣ G)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPG : ∀ p ∈ P, p ∣ G)
    (hlarge : N < (∏ p ∈ P, p)^2) :
    ∃ H R : ℕ, 0 < H ∧ 0 < R ∧ ∀ (v : ℕ) (hv0 : 0 < v), H ∣ v → 16*R ≤ v →
      ∀ {K : Type} [AddCommMonoid K] (f : ℤ → K),
      Cyclic (G*v) f →
      (∀ j : Fin (G*v), j ∉ Set.range (gridIndex hG hv0 (v/(8*R))) → f j.val = 0) →
      BufferedZero N (G*v) (3*(v : ℝ)/(40*R)-1) f →
      (∀ p ∈ P, trace p ((G*v)/p) f = 0) → f = 0 := by
  obtain ⟨r,H,_R₀,hH,_hR₀,hr⟩ := exists_grid_parameters hG
  obtain ⟨R,hR,hrR,hgap⟩ := QuantitativeArithmeticGoodLabelWindows.exists_uniform_scale hN r
  have hr' : ∀ a, 0 < r a ∧ Nat.Coprime (r a) G ∧ r a ∣ H ∧ r a ≤ R ∧
      Nat.ModEq (labelModulus a) (r a*a.val) (labelModulus a/labelOrder a) :=
    fun a => ⟨(hr a).1,(hr a).2.1,(hr a).2.2.1,hrR a,(hr a).2.2.2.2⟩
  refine ⟨H,R,hH,hR,?_⟩
  intro v hv0 hHv hv K _ f hcyc hsupport hrows htraces
  apply detect_from_windows hN hG P hP hPG hlarge hR r hr' v hv0 hHv hv
    (fun a ha t => ?_) f hcyc hsupport hrows htraces
  exact QuantitativeArithmeticGoodLabelWindows.selected_good_window_compatible
    hN hG hNG a (hr a).1 (hr a).2.1 (hrR a) (hgap a ha) hv
    (Nat.mul_div_cancel' ((hr a).2.2.1.trans hHv)).symm t.val (offset_bound hR t)

/-- Complete retained traces survive taking finite differences. -/
theorem difference_trace_zero {K : Type} [AddCommGroup K] (a q D : ℕ)
    (f : ℤ → K) (hf : trace q D f = 0) :
    trace q D (SpanningKernelDifferences.difference a f) = 0 := by
  funext u
  rw [SpanningKernelDifferences.trace_difference, hf]
  simp

/-- The retained-prime detector required by the concentration argument,
proved from the literal rows, with no additional detection premise. -/
theorem grid_difference_detector {N : ℕ} (hN : 0 < N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hlarge : N < (∏ p ∈ P, p)^2)
    (K : Type) [Field K] :
    QuantitativeArithmeticRetainedConcentration.GridDifferenceDetector K N P := by
  intro L hPL G hG hNG hPG
  obtain ⟨H,R,hH,hR,hdet⟩ := exists_buffered_grid hN hG hNG P hP hPG hlarge
  refine ⟨H,R,hH,hR,?_⟩
  intro v hv0 hHv hv a f ha hf hmargin hsize hsupp
  have hd := hdet v hv0 hHv hv (SpanningKernelDifferences.difference a f)
    (SpanningKernelDifferences.difference_cyclic hf.1.1) hsupp
    (SpanningKernelDifferences.difference_buffered hf.1 hmargin)
    (fun p hp => difference_trace_zero a p ((G*v)/p) f (hf.2 p (hPL hp)))
  exact SpanningKernelDifferences.small_period_kernel_zero ha hf.1
    ((SpanningKernelDifferences.difference_zero_iff a f).mp hd) hsize

#print axioms prime_coset_zero
#print axioms detect_from_windows
#print axioms exists_buffered_grid
#print axioms grid_difference_detector

end QuantitativeArithmeticRetainedGrid
