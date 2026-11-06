module

public import FinitenessAllLevelOriginalPencilV1
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set Filter FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelBoundaryGeometry
  FinitenessAllLevelCertificateBoundary FinitenessAllLevelPencilHeights
  FinitenessAllLevelReconstruction FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace
  QuantitativeArithmeticRetainedCertificate
open scoped Topology

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- One actual patched reconstruction step at an arbitrary positive height. -/
def step (A : Certificate N {p} Q hQ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  let w := Function.Periodic.qParam 1 z
  let j := selector Q hQ w
  ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) *
    twoDilationRow G (2 * m) χ (firstMultiplier (fun _ => lam) m)
      (fun q => (q : ℂ) ^ (2 * m)) j (line (coordinate w) z.im) i

/-- Finite-depth formal continuation. Values above the initial height are
always read directly from the Banach disk; no holomorphy below it is assumed. -/
def iterate (A : Certificate N {p} Q hQ) (a : ℝ) (χ : ℕ → ℂ) (m : ℕ)
    (lam : ℂ) (F : space (radius a)) : ℕ → ℂ → ℂ
  | 0 => lift F
  | n + 1 => fun z => if a ≤ z.im then lift F z else
      step A χ m lam (iterate A a χ m lam F n) z

theorem iterate_above (A : Certificate N {p} Q hQ) (a : ℝ) (χ : ℕ → ℂ) (m : ℕ)
    (lam : ℂ) (F : space (radius a)) (n : ℕ) {z : ℂ} (hz : a ≤ z.im) :
    iterate A a χ m lam F n z = lift F z := by
  cases n <;> simp only [iterate, ite_eq_left hz]

theorem step_congr (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    {c : ℝ} {G H : ℂ → ℂ} (hGH : ∀ w : ℂ, c ≤ w.im → G w = H w)
    {z : ℂ} (hz : 0 < z.im) (hze : z.im ≤ P.ε) (hc : c ≤ z.im / P.ρ) :
    step A χ m lam G z = step A χ m lam H z := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact rows_agree hN hp A P hz hze hc G H hGH χ _ _ (2 * m)
    (Function.Periodic.qParam 1 z) i hi

/-- Once every branch has reached the initial height, increasing the depth
does not change the value. The bound is uniform on every positive-height tail. -/
theorem iterate_stable (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) (n l : ℕ)
    {z : ℂ} (hz : a * P.ρ ^ n ≤ z.im) :
    iterate A a χ m lam F (n + l) z = iterate A a χ m lam F n z := by
  induction n generalizing l z with
  | zero =>
      have haz : a ≤ z.im := by simpa only [pow_zero, mul_one] using hz
      simp only [zero_add, iterate_above A a χ m lam F l haz, iterate]
  | succ n ih =>
      by_cases haz : a ≤ z.im
      · rw [iterate_above A a χ m lam F _ haz, iterate_above A a χ m lam F _ haz]
      · simp only [Nat.succ_add, iterate, ite_eq_right haz]
        apply step_congr hN hp A P χ m lam
          (fun w hw => ih l hw)
          ((mul_pos ha (pow_pos P.rho_pos _)).trans_le hz)
          ((le_of_not_ge haz).trans hae)
        apply (le_div_iff₀ P.rho_pos).mpr
        simpa only [pow_succ, mul_assoc] using hz

theorem depth_exists (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) {y : ℝ} (hy : 0 < y) : ∃ n : ℕ, a * P.ρ ^ n ≤ y := by
  have ht : Tendsto (fun n : ℕ => a * P.ρ ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one P.rho_pos.le P.rho_lt_one)
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const hy).exists
  exact ⟨n, hn.le⟩

def depth (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (z : ℂ) : ℕ :=
  if hz : 0 < z.im then Nat.find (depth_exists A P a hz) else 0

theorem depth_spec (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) {z : ℂ} (hz : 0 < z.im) : a * P.ρ ^ depth A P a z ≤ z.im := by
  simp only [depth, dite_eq_left hz]
  exact Nat.find_spec (depth_exists A P a hz)

def formal (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) (z : ℂ) : ℂ :=
  iterate A a χ m lam F (depth A P a z) z

/-- The globally defined formal continuation agrees with one fixed finite
expression on every positive-height tail. This is the finite-depth input
needed for the later common-domain distributional equations. -/
theorem formal_eq_iterate (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) (n : ℕ)
    {z : ℂ} (hz : 0 < z.im) (hn : a * P.ρ ^ n ≤ z.im) :
    formal A P a χ m lam F z = iterate A a χ m lam F n z := by
  let d := depth A P a z
  have hd := depth_spec A P a hz
  have h1 := iterate_stable hN hp A P ha hae χ m lam F d n hd
  have h2 := iterate_stable hN hp A P ha hae χ m lam F n d hn
  unfold formal
  exact h1.symm.trans (by simpa only [Nat.add_comm] using h2)

theorem uniform_depth (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    {y : ℝ} (hy : 0 < y) :
    ∃ n : ℕ, ∀ χ m lam (F : space (radius a)) (z : ℂ), y ≤ z.im →
      formal A P a χ m lam F z = iterate A a χ m lam F n z := by
  obtain ⟨n, hn⟩ := depth_exists A P a hy
  exact ⟨n, fun χ m lam F z hz => formal_eq_iterate hN hp A P ha hae χ m lam F n
    (hy.trans_le hz) (hn.trans hz)⟩

#print axioms iterate_stable
#print axioms depth_exists
#print axioms formal_eq_iterate
#print axioms uniform_depth

end FinitenessAllLevelFormalContinuation
