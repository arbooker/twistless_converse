module

public import AsymptoticClassicalMultiplicityRelativeV1
public import AsymptoticClassicalNewDimensionDifferenceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalDimension

open UpperHalfPlane Filter Asymptotics AsymptoticSectorComparison
open AsymptoticClassicalCusp AsymptoticCongruenceStrip
open scoped Topology

/-- The empty partial-new condition recovers the full cusp dimension estimate. -/
theorem empty_dimension_littleO (N : ℕ) (hN : 0 < N) :
    (fun k : ℕ => (Module.finrank ℂ (partialNewSpace N hN (k : ℤ) ∅) : ℝ) -
      fullLeading N * k) =o[evenWeights] (fun k => (k : ℝ)) := by
  have hd (k : ℕ) : Module.finrank ℂ (partialNewSpace N hN (k : ℤ) ∅) =
      Module.finrank ℂ (CuspForm (level N) (k : ℤ)) := by
    rw [partialNewSpace_empty, finrank_top]
  simpa only [hd, fullLeading, div_mul_eq_mul_div] using cusp_dimension_littleO N hN

/-- A singleton partial-new condition is the original paired trace kernel. -/
theorem partialNewSpace_singleton (N : ℕ) (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) :
    partialNewSpace N hN k {p.val} = primeTraceKernel N hN k p := by
  rw [Set.singleton_def, partialNewSpace_insert, partialNewSpace_empty, inf_top_eq]

/-- At every level divisible by four, impose the repeated-2 condition first;
 its leading coefficient comes from the full-space second difference. -/
theorem two_dimension_littleO (N : ℕ) (hN : 0 < N) (h4 : 4 ∣ N) :
    (fun k : ℕ => (Module.finrank ℂ (partialNewSpace N hN (k : ℤ) {2}) : ℝ) -
      twoLeading N * k) =o[evenWeights] (fun k => (k : ℝ)) := by
  obtain ⟨L, hNL⟩ := h4
  have heN : N = 2 * (2 * L) := by omega
  clear hNL
  subst N
  have hL : 0 < L := by omega
  have he : 4 * L = 2 * (2 * L) := by omega
  have hd2 : 2 * (2 * L) / 2 = 2 * L := Nat.mul_div_cancel_left _ (by decide)
  have hd4 : 2 * (2 * L) / 4 = L := by rw [← he]; exact Nat.mul_div_cancel_left _ (by decide)
  have hh := twoKernel_dimension_littleO L hL
  have hs (k : ℕ) : partialNewSpace (2 * (2 * L)) (by omega) (k : ℤ) {2} =
      primeTraceKernel (2 * (2 * L)) (by omega) (k : ℤ) (repeatedPrime L 2 Nat.prime_two) :=
    partialNewSpace_singleton _ _ _ (repeatedPrime L 2 Nat.prime_two)
  have hdim (k : ℕ) := congrArg
    (fun U : Submodule ℂ (CuspForm (level (2 * (2 * L))) (k : ℤ)) => Module.finrank ℂ U) (hs k)
  simp_rw [← hdim] at hh
  simpa only [twoLeading, hd2, hd4, div_mul_eq_mul_div] using hh

#print axioms empty_dimension_littleO
#print axioms partialNewSpace_singleton
#print axioms two_dimension_littleO

end AsymptoticClassicalDimension
