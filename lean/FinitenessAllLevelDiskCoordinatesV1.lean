module

public import FinitenessAllLevelDiskAlgebraV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelDiskCoordinates

open Set FinitenessOriginalInput FinitenessAllLevelDiskAlgebra

/-- Actual original solutions in the eigenvalue times disk-algebra Banach
space. An analytic-space structure on this locus has not yet been proved. -/
def coordinates (N k p : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (f : S N k) : ℂ × space R :=
  (f.val p, representative N k hR hR1 f)

theorem coordinates_continuous {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) (m : ℕ)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    Continuous (coordinates N (2 * m) p hR hR1) :=
  ((continuous_apply p).comp continuous_subtype_val).prodMk
    (representative_continuous hN hp hgood hlarge m hR hR1)

theorem coordinates_injective (N k p : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    Function.Injective (coordinates N k p hR hR1) := by
  intro f g he
  exact representative_injective N k hR hR1 (congrArg Prod.snd he)

theorem coordinates_isProperMap {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsProperMap (coordinates N (2 * m) p hR hR1) :=
  isProperMap_of_comp_of_t2
    (coordinates_continuous hN hp hgood hlarge m hR hR1) continuous_fst
    (FinitenessAllLevelProperness.eigenvalue_isProperMap hN hp hgood hlarge hm)

theorem coordinates_isClosedEmbedding {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    Topology.IsClosedEmbedding (coordinates N (2 * m) p hR hR1) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (coordinates_continuous hN hp hgood hlarge m hR hR1)
    (coordinates_injective N (2 * m) p hR hR1)
    (coordinates_isProperMap hN hp hgood hlarge hm hR hR1).isClosedMap

def locus (N k p : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R < 1) : Set (ℂ × space R) :=
  range (coordinates N k p hR hR1)

theorem locus_isClosed {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) : IsClosed (locus N (2 * m) p hR hR1) :=
  (coordinates_isClosedEmbedding hN hp hgood hlarge hm hR hR1).isClosed_range

/-- Properness holds on the exact disk-algebra realization, independently
of the still missing analytic chart construction. -/
theorem projection_isProperMap {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsProperMap (fun x : locus N (2 * m) p hR hR1 => x.val.1) := by
  let c : S N (2 * m) → locus N (2 * m) p hR hR1 :=
    fun f => ⟨coordinates N (2 * m) p hR hR1 f, mem_range_self f⟩
  have hc : Continuous c :=
    (coordinates_continuous hN hp hgood hlarge m hR hR1).subtype_mk _
  apply isProperMap_of_comp_of_surj hc (continuous_fst.comp continuous_subtype_val)
    (FinitenessAllLevelProperness.eigenvalue_isProperMap hN hp hgood hlarge hm)
  rintro ⟨x, f, rfl⟩
  exact ⟨f, rfl⟩

#print axioms coordinates_isProperMap
#print axioms coordinates_isClosedEmbedding
#print axioms locus_isClosed
#print axioms projection_isProperMap

end FinitenessAllLevelDiskCoordinates
