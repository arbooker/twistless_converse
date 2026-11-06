module

public import FinitenessAllLevelAutomaticGrowthV1
public import FinitenessPaper2DiskLimitsV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelBoundedFamilies

open Filter Set FinitenessOriginalInput FinitenessAllLevelDiskSeries FinitenessOriginalFourier
open scoped Topology

/-- No common coefficient exponent is assumed in a bounded-eigenvalue family. -/
def family (N k p : ℕ) (L : ℝ) : Set (ℕ → ℂ) :=
  {f | IsSolution N k f ∧ ‖f p‖ ≤ L}

theorem subset_fixed_growth {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L) :
    ∃ s : ℕ, ∀ m : ℕ, family N (2 * m) p L ⊆
      FinitenessPaper2.E N (2 * m) ((s : ℝ) + 1 / 2) := by
  obtain ⟨s, hs⟩ := FinitenessAllLevelAutomaticGrowth.uniform_coefficient_envelope
    hN hp hgood hlarge hL
  refine ⟨s, fun m f hf => ?_⟩
  exact (FinitenessPaper2.mem_iff_original N (2 * m) _ f).mpr
    ⟨hf.1, (hs m f hf.1 hf.2).1⟩

/-- Bounded eigenvalues now give compact coefficient closure through the
derived common growth exponent. Closedness of the analytic continuation
predicate is not asserted here. -/
theorem closure_isCompact {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L) (m : ℕ) :
    IsCompact (closure (family N (2 * m) p L)) := by
  obtain ⟨s, hs⟩ := subset_fixed_growth hN hp hgood hlarge hL
  exact (FinitenessPaper2.coefficient_closure_isCompact (k := 2 * m)
    (σ := (s : ℝ) + 1 / 2) hN).of_isClosed_subset isClosed_closure (closure_mono (hs m))

theorem closure_eigenvalue_bound {N k p : ℕ} {L : ℝ} {f : ℕ → ℂ}
    (hf : f ∈ closure (family N k p L)) : ‖f p‖ ≤ L := by
  apply closure_minimal (fun _ h => h.2)
    (isClosed_le (continuous_apply p).norm continuous_const) hf

theorem closure_eulerData {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L)
    {m : ℕ} {f : ℕ → ℂ} (hf : f ∈ closure (family N (2 * m) p L)) :
    EulerData N f ∧ f 1 = 1 ∧ ‖f p‖ ≤ L := by
  obtain ⟨s, hs⟩ := subset_fixed_growth hN hp hgood hlarge hL
  have hh := closure_mono (hs m) hf
  exact ⟨FinitenessPaper2.closure_eulerData hN hh, FinitenessPaper2.closure_one hh,
    closure_eigenvalue_bound hf⟩

/-- Convergence in the disk supremum norm for actual families bounded only
at one auxiliary prime. -/
theorem fourier_disk_tendsto {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L)
    {m : ℕ} {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    {a : ℕ → ℕ → ℂ} {f : ℕ → ℂ} (ha : ∀ j, a j ∈ family N (2 * m) p L)
    (ht : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (f n))) :
    Tendsto (fun j => diskSeries (fullCoefficients (a j) (2 * m)) R) atTop
      (𝓝 (diskSeries (fullCoefficients f (2 * m)) R)) := by
  obtain ⟨s, hs⟩ := subset_fixed_growth hN hp hgood hlarge hL
  exact FinitenessPaper2.fourier_disk_tendsto hN hR hR1 (fun j => hs m (ha j)) ht

theorem exists_subsequence {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L)
    (m : ℕ) (a : ℕ → ℕ → ℂ) (ha : ∀ j, a j ∈ family N (2 * m) p L) :
    ∃ f : ℕ → ℂ, EulerData N f ∧ f 1 = 1 ∧ ‖f p‖ ≤ L ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ n, Tendsto (fun j => a (φ j) n) atTop (𝓝 (f n))) ∧
        ∀ R : ℝ, 0 ≤ R → R < 1 →
          Tendsto (fun j => diskSeries (fullCoefficients (a (φ j)) (2 * m)) R) atTop
            (𝓝 (diskSeries (fullCoefficients f (2 * m)) R)) := by
  obtain ⟨f, hf, φ, hφ, ht⟩ := (closure_isCompact hN hp hgood hlarge hL m).tendsto_subseq
    (fun j => subset_closure (ha j))
  obtain ⟨he, h1, hb⟩ := closure_eulerData hN hp hgood hlarge hL hf
  have ht' (n : ℕ) : Tendsto (fun j => a (φ j) n) atTop (𝓝 (f n)) :=
    ((continuous_apply n).tendsto f).comp ht
  refine ⟨f, he, h1, hb, φ, hφ, ht', fun R hR hR1 => ?_⟩
  exact fourier_disk_tendsto hN hp hgood hlarge hL hR hR1 (fun j => ha (φ j)) ht'

#print axioms subset_fixed_growth
#print axioms closure_isCompact
#print axioms closure_eulerData
#print axioms fourier_disk_tendsto
#print axioms exists_subsequence

end FinitenessAllLevelBoundedFamilies
