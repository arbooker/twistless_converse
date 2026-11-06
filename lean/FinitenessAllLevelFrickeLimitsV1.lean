module

public import FinitenessAllLevelBoundedFamiliesV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelFrickeLimits

open Complex Filter Set FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction FinitenessAllLevelDiskSeries
open scoped Topology

theorem fourier_tendsto {N k : ℕ} {σ : ℝ} (hN : 0 < N)
    {a : ℕ → ℕ → ℂ} {f : ℕ → ℂ} (ha : ∀ j, a j ∈ FinitenessPaper2.E N k σ)
    (ht : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (f n)))
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun j => fourier (fullCoefficients (a j) k) z) atTop
      (𝓝 (fourier (fullCoefficients f k) z)) := by
  have hf : f ∈ closure (FinitenessPaper2.E N k σ) :=
    mem_closure_of_tendsto (tendsto_pi_nhds.mpr ht) (Eventually.of_forall ha)
  let w := Function.Periodic.qParam 1 z
  have hw : ‖w‖ < 1 := Function.Periodic.norm_qParam_lt_one (by norm_num) hz
  let v : Disk ‖w‖ := ⟨w, by simp⟩
  have h := FinitenessPaper2.fourier_disk_tendsto hN (norm_nonneg w) hw ha ht
  have hh := ((ContinuousMap.evalCLM ℂ v).continuous.tendsto
    (diskSeries (fullCoefficients f k) ‖w‖)).comp h
  have he (g : ℕ → ℂ) (hg : g ∈ closure (FinitenessPaper2.E N k σ)) :
      diskSeries (fullCoefficients g k) ‖w‖ v = fourier (fullCoefficients g k) z :=
    FinitenessPaper2.closure_diskSeries_eq hN (norm_nonneg w) hw hg v
  simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, he f hf,
    he _ (subset_closure (ha _))] using hh

/-- A single limiting root number works simultaneously at every point.
It is obtained from the compact two-element sign set, not chosen separately
for each z. -/
theorem fricke_limit {N k : ℕ} {σ : ℝ} (hN : 0 < N)
    {a : ℕ → ℕ → ℂ} {f : ℕ → ℂ} (ha : ∀ j, a j ∈ FinitenessPaper2.E N k σ)
    (ht : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (f n))) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ z : ℂ, 0 < z.im →
      fourier (fullCoefficients f k) z =
        (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
          fourier (fullCoefficients f k) (-1 / ((N : ℂ) * z)) := by
  have hsign (j : ℕ) := FinitenessOriginalFricke.fricke_of_continuation hN
    (ha j).1.zero (ha j).2 (ha j).1.continuation
  choose eps heps hFE using hsign
  have hcompact : IsCompact ({1, -1} : Set ℂ) := (Set.toFinite _).isCompact
  obtain ⟨ε, hε, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun j => by simpa only [mem_insert_iff, mem_singleton_iff] using heps j)
  refine ⟨ε, by simpa only [mem_insert_iff, mem_singleton_iff] using hε, ?_⟩
  intro z hz
  have hr : 0 < (-1 / ((N : ℂ) * z)).im := by
    simpa only [ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (N : ℝ)) (by exact_mod_cast hN) hz
  have hleft := (fourier_tendsto hN ha ht hz).comp hφ.tendsto_atTop
  have hright := ((hlim.mul_const (I ^ k)).div_const
    ((((Real.sqrt N : ℝ) : ℂ) * z) ^ k)).mul
    ((fourier_tendsto hN ha ht hr).comp hφ.tendsto_atTop)
  exact tendsto_nhds_unique hleft (hright.congr (fun j => (hFE (φ j) z hz).symm))

#print axioms fourier_tendsto
#print axioms fricke_limit

end FinitenessAllLevelFrickeLimits
