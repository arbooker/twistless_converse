module
public import QuantitativeArithmeticMaassCuspBandTheoryV4
public import QuantitativeArithmeticMaassCuspidalDiscretenessV1
public import QuantitativeMaassCuspSpectralSummabilityV1
public import QuantitativeMaassShiftedWavePacketV1
public import Mathlib.Analysis.InnerProductSpace.l2Space
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 0
set_option Elab.async false
@[expose] public noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
universe u

namespace QuantitativeArithmeticMaassCuspBand
open scoped ENNReal
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
open QuantitativeMaass QuantitativeMaass.Wave


/-- An actual complete orthonormal basis of geometric cusp vectors consisting
of eigenvectors of the Friedrichs resolvent, at every positive level. -/
theorem exists_cuspidal_resolvent_eigenbasis (N : ℕ) (hN : 0 < N) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (μ : ι → ℂ),
      ∀ i, cuspidalResolvent N hN (b i) = μ i • b i :=
  exists_eigenbasis_in_nested_L2_subspace
    (AsymptoticClassicalPetersson.quotientMeasure N)
    (AutomorphicL2.space (AsymptoticCongruenceStrip.gamma N)
      (AsymptoticClassicalPetersson.quotientMeasure N))
    (localCuspidalSpace N hN) (cuspidalResolvent N hN)
    (fun x y => cuspidalResolvent_symmetric N hN x y)
    (cuspidal_eigenspaces_dense N hN)

/-- The resolvent eigenvalue attached to a unit vector cannot vanish. -/
theorem resolvent_basis_eigenvalue_ne_zero (N : ℕ) (hN : 0 < N)
    {ι : Type*} (b : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (μ : ι → ℂ)
    (hμ : ∀ i, cuspidalResolvent N hN (b i) = μ i • b i) (i : ι) : μ i ≠ 0 := by
  intro hz
  have he : cuspidalResolvent N hN (b i) = cuspidalResolvent N hN 0 := by
    rw [hμ i, hz, zero_smul, map_zero]
  have hzero := cuspidalResolvent_injective N hN he
  exact b.orthonormal.ne_zero i hzero

/-- Every basis vector solves the original Friedrichs graph equation. -/
theorem resolvent_basis_graph (N : ℕ) (hN : 0 < N)
    {ι : Type*} (b : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (μ : ι → ℂ)
    (hμ : ∀ i, cuspidalResolvent N hN (b i) = μ i • b i) (i : ι) :
    FriedrichsGraph N (b i) (((μ i)⁻¹ - 1) • (b i : AutomorphicSpace N)) :=
  cuspidal_resolvent_eigenvector_graph N hN (μ i)
    (resolvent_basis_eigenvalue_ne_zero N hN b μ hμ i) (b i)
    (Module.End.mem_eigenspace_iff.mpr (hμ i))

#print axioms exists_cuspidal_resolvent_eigenbasis
#print axioms resolvent_basis_eigenvalue_ne_zero
#print axioms resolvent_basis_graph

/-- Symmetry and positivity determine the energy of a unit graph eigenvector. -/
theorem unit_graph_eigenvalue_real_nonnegative (N : ℕ)
    (v : AutomorphicSpace N) (hv : ‖v‖ = 1) (c : ℂ)
    (hg : FriedrichsGraph N v (c • v)) : (c.re : ℂ) = c ∧ 0 ≤ c.re := by
  have hi : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
  have hc : starRingEnd ℂ c = c := by
    simpa only [inner_smul_left (𝕜 := ℂ) v v, inner_smul_right (𝕜 := ℂ) v v, hi, mul_one] using
      friedrichsGraph_symmetric N hg hg
  refine ⟨RCLike.conj_eq_iff_re.mp hc, ?_⟩
  simpa only [inner_smul_right (𝕜 := ℂ) v v, hi, mul_one] using friedrichsGraph_nonnegative N hg

/-- A complete geometric cusp eigenbasis with nonnegative energies and a
summable resolvent weight. No spectral completeness or Weyl estimate is
assumed: the former follows from compactness, and the latter is unnecessary. -/
theorem exists_cuspidal_energy_basis (N : ℕ) (hN : 0 < N) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι → ℝ),
      (∀ i, 0 ≤ e i) ∧
      (∀ i, FriedrichsGraph N (b i) ((e i : ℂ) • (b i : AutomorphicSpace N))) ∧
      Summable (fun i => 1 / (e i + 1)^8) := by
  obtain ⟨ι, b, μ, hμ⟩ := exists_cuspidal_resolvent_eigenbasis N hN
  let v : ι → AutomorphicSpace N := fun i => b i
  have hv : Orthonormal ℂ v :=
    b.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let e : ι → ℝ := fun i => ((μ i)⁻¹ - 1).re
  have hreal (i : ι) : (e i : ℂ) = (μ i)⁻¹ - 1 ∧ 0 ≤ e i :=
    unit_graph_eigenvalue_real_nonnegative N (v i) (hv.norm_eq_one i)
      ((μ i)⁻¹ - 1) (resolvent_basis_graph N hN b μ hμ i)
  have hg (i : ι) : FriedrichsGraph N (v i) ((e i : ℂ) • v i) := by
    rw [(hreal i).1]
    exact resolvent_basis_graph N hN b μ hμ i
  exact ⟨ι, b, e, fun i => (hreal i).2, hg,
    cuspidal_inverse_eighth_summable N hN v hv (fun i => (b i).property)
      e (fun i => (hreal i).2) hg⟩

#print axioms unit_graph_eigenvalue_real_nonnegative
#print axioms exists_cuspidal_energy_basis

/-- The actual wave packet is the convergent multiplier expansion on the
complete geometric cusp basis, including exceptional nonnegative energies. -/
theorem cuspidal_basis_packet_expansion (N : ℕ) (hN : 0 < N)
    {ι : Type*} (b : HilbertBasis ι ℂ (localCuspidalSpace N hN))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    (hg : ∀ i, FriedrichsGraph N (b i) ((e i : ℂ) • (b i : AutomorphicSpace N)))
    (φ : ℝ → ℂ) (hφ : ShiftedWaveWeight φ) (v : localCuspidalSpace N hN) :
    HasSum (fun i => (b.repr v i * (∫ t, φ t * (signedCosine t (e i - 1/4) : ℂ))) •
      (b i : AutomorphicSpace N)) (shiftedQuotientWavePacket N φ hφ v) := by
  have hb := (localCuspidalSpace N hN).subtypeL.hasSum (b.hasSum_repr v)
  have h := (shiftedQuotientWavePacket N φ hφ).hasSum hb
  apply h.congr_fun
  intro i
  simp only [map_smul, Submodule.subtypeL_apply,
    shiftedQuotientWavePacket_eigen N φ hφ (he i) (hg i), smul_smul]

#print axioms cuspidal_basis_packet_expansion
end QuantitativeArithmeticMaassCuspBand
