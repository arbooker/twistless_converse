module

public import FinitenessAllLevelPropernessV1
public import FinitenessOriginalDiskIndependenceV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelTopology

open Filter Set FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessAllLevelDiskSeries FinitenessAllLevelProperness
open scoped Topology

theorem polynomial_diskSeries_apply {a : ℕ → ℂ}
    (ha : FinitenessPolynomialSeries.PolynomialBound a)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) (z : Disk R) :
    diskSeries a R z = FinitenessPolynomialSeries.sum a z.val := by
  rw [FinitenessPolynomialSeries.sum_eq_tsum]
  exact diskSeries_apply hR (fun n => norm_nonneg (a n)) (fun _ => le_rfl)
    (FinitenessPolynomialSeries.norm_summable ha hR hR1) z

/-- Restriction to any disk with positive radius still determines the original
solution. Uniqueness follows from the power series germ at zero. -/
theorem disk_injective (N k : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    Function.Injective (fun f : S N k => diskMap k R f.val) := by
  intro f g he
  apply (FinitenessOriginalDiskIndependence.normalized_independent N k).injective
  apply FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
  apply (FinitenessPolynomialSeries.has_series
    (FinitenessOriginalDiskIndependence.polynomial N k f)).eq_formalMultilinearSeries_of_eventually
      (FinitenessPolynomialSeries.has_series
        (FinitenessOriginalDiskIndependence.polynomial N k g))
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
  let w : Disk R := ⟨z, Metric.ball_subset_closedBall hz⟩
  have hw := congrArg (fun F : C(Disk R, ℂ) => F w) he
  simpa only [diskMap, polynomial_diskSeries_apply
    (FinitenessOriginalDiskIndependence.polynomial N k f) hR.le hR1,
    polynomial_diskSeries_apply
      (FinitenessOriginalDiskIndependence.polynomial N k g) hR.le hR1] using hw

/-- Coefficient convergence automatically bounds the chosen eigenvalue, so
the disk map is continuous on the entire original solution set. -/
theorem disk_continuous {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) (m : ℕ)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    Continuous (fun f : S N (2 * m) => diskMap (2 * m) R f.val) := by
  apply SeqContinuous.continuous
  intro a f ht
  have hcoeff (n : ℕ) : Tendsto (fun j => (a j).val n) atTop (𝓝 (f.val n)) :=
    (((continuous_apply n).comp continuous_subtype_val).tendsto f).comp ht
  obtain ⟨L, hL, hb⟩ := (Metric.isBounded_range_of_tendsto _ (hcoeff p)).exists_pos_norm_le
  exact FinitenessAllLevelBoundedFamilies.fourier_disk_tendsto hN hp hgood hlarge
    hL.le hR hR1 (fun j => ⟨(a j).property, hb _ (mem_range_self j)⟩) hcoeff

/-- The literal original solution set is closed in the coefficient space;
no uniform growth exponent is a premise. -/
theorem solutions_isClosed {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m) :
    IsClosed (S N (2 * m)) := by
  apply IsSeqClosed.isClosed
  intro a f ha ht
  have he : Tendsto (fun j => a j p) atTop (𝓝 (f p)) :=
    ((continuous_apply p).tendsto f).comp ht
  obtain ⟨L, hL, hb⟩ := (Metric.isBounded_range_of_tendsto _ he).exists_pos_norm_le
  exact ((family_isClosed hN hp hgood hlarge hL.le hm).mem_of_tendsto ht
    (Eventually.of_forall (fun j => ⟨ha j, hb _ (mem_range_self j)⟩))).1

/-- These are the actual eigenvalue and Banach coordinates used in the
paper's prospective analytic charts. -/
def coordinates (N k p : ℕ) (R : ℝ) (f : S N k) : ℂ × C(Disk R, ℂ) :=
  (f.val p, diskMap k R f.val)

theorem coordinates_continuous {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) (m : ℕ)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    Continuous (coordinates N (2 * m) p R) :=
  ((continuous_apply p).comp continuous_subtype_val).prodMk
    (disk_continuous hN hp hgood hlarge m hR hR1)

/-- The Banach-coordinate realization is proper and hence closed. This is
a topological statement, not an assumed complex analytic structure. -/
theorem coordinates_isProperMap {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    IsProperMap (coordinates N (2 * m) p R) :=
  isProperMap_of_comp_of_t2
    (coordinates_continuous hN hp hgood hlarge m hR hR1) continuous_fst
    (eigenvalue_isProperMap hN hp hgood hlarge hm)

/-- The coefficient topology agrees with the topology induced by the
eigenvalue and disk supremum-norm coordinates. -/
theorem coordinates_isClosedEmbedding {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    Topology.IsClosedEmbedding (coordinates N (2 * m) p R) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (coordinates_continuous hN hp hgood hlarge m hR.le hR1)
  · intro f g he
    exact disk_injective N (2 * m) hR hR1 (congrArg Prod.snd he)
  · exact (coordinates_isProperMap hN hp hgood hlarge hm hR.le hR1).isClosedMap

#print axioms disk_injective
#print axioms disk_continuous
#print axioms solutions_isClosed
#print axioms coordinates_isProperMap
#print axioms coordinates_isClosedEmbedding

end FinitenessAllLevelTopology
