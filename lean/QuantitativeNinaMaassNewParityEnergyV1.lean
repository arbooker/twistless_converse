module

public import QuantitativeMaassCanonicalParitySpaceV1
public import QuantitativeMaassCuspidalTraceIdentityV1
public import QuantitativeNinaMaassNewCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeMaass AsymptoticClassicalPetersson
open scoped ENNReal InnerProductSpace SchwartzMap

namespace QuantitativeNinaMaass

section Projection

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Exact energy comparison for two nested closed spaces. The smaller
space need not have a chosen spectral basis. This is a nonnegative sum
identity, so it does not assume trace finiteness. -/
theorem nested_projection_energy (V C : Submodule ℂ H) [CompleteSpace V]
    [CompleteSpace C] (hVC : V ≤ C) (b : HilbertBasis ι ℂ V)
    (c : HilbertBasis κ ℂ C) (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hAC : ∀ x ∈ C, A x ∈ C) :
    (∑' j, ENNReal.ofReal (‖V.starProjection (A (c j : H))‖ ^ 2)) =
      ∑' i, ENNReal.ofReal (‖A (b i : H)‖ ^ 2) := by
  obtain ⟨ρ, B, _⟩ := exists_hilbertBasis ℂ H
  have hV : 0 ≤ V.starProjection :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (ContinuousLinearMap.IsPositive.of_isStarProjection
        (isStarProjection_starProjection (U := V)))
  have hh := positive_smoothed_trace_two_bases C B c A V.starProjection hA hV hAC
    (fun x => hVC (V.orthogonalProjectionOnto x).property)
  have hq (x : H) : (inner ℂ (V.starProjection x) x).re =
      ‖V.starProjection x‖ ^ 2 := V.re_inner_starProjection_eq_normSq x
  simp only [hq] at hh
  rw [← hh, projected_energy_two_bases V B b A, hA.adjoint_eq]

/-- Ordinary summability and an exact real sum follow from the known
energy on the smaller space, with no subtraction of infinite quantities. -/
theorem nested_projection_energy_hasSum (V C : Submodule ℂ H) [CompleteSpace V]
    [CompleteSpace C] (hVC : V ≤ C) (b : HilbertBasis ι ℂ V)
    (c : HilbertBasis κ ℂ C) (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hAC : ∀ x ∈ C, A x ∈ C)
    (hs : Summable (fun i => ‖A (b i : H)‖ ^ 2)) :
    HasSum (fun j => ‖V.starProjection (A (c j : H))‖ ^ 2)
      (∑' i, ‖A (b i : H)‖ ^ 2) := by
  have he := nested_projection_energy V C hVC b c A hA hAC
  have ht : (∑' j, ENNReal.ofReal (‖V.starProjection (A (c j : H))‖ ^ 2)) ≠ ∞ := by
    rw [he]
    exact hs.tsum_ofReal_lt_top.ne
  have hp : Summable (fun j => ‖V.starProjection (A (c j : H))‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal ht
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hp,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs] at he
  have hr := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_ofReal (tsum_nonneg (fun _ => sq_nonneg _))] at hr
  exact hr ▸ hp.hasSum

end Projection

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- Literal spectral weights of the completed physical new-parity
projection, evaluated on the existing geometric cusp spectrum. -/
def newParitySpectralWeight {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (η : ℝ) (j : S.Index) : ℝ :=
  ‖(completedCuspidalNewParitySpace N hN η).starProjection
    (S.basis j : AutomorphicSpace N)‖ ^ 2

theorem newParitySpectralWeight_bounds {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (η : ℝ) (j : S.Index) :
    newParitySpectralWeight S η j ∈ Icc (0 : ℝ) 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have hh := (completedCuspidalNewParitySpace N hN η).norm_starProjection_apply_le
    (S.basis j : AutomorphicSpace N)
  have hn : ‖(S.basis j : AutomorphicSpace N)‖ = 1 := S.basis.orthonormal.norm_eq_one j
  rw [hn] at hh
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (one_pow 2)

/-- The actual completed-new-parity packet energy is its ordinary
convergent spectral multiplier sum. The projection weights are computed
from the actual cusp basis; no new/parity eigenbasis or trace identity is
assumed. Exceptional energies remain included in this equality. -/
theorem newParityPacket_spectral_energy {ι : Type*} {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (η : ℝ)
    (b : HilbertBasis ι ℂ (completedCuspidalNewParitySpace N hN η))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t, star (f t) = f t)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    HasSum (fun j => ‖smoothPacketMultiplier f (S.energy j)‖ ^ 2 *
      newParitySpectralWeight S η j)
      (hilbertSchmidtEnergy b
        (completedCuspidalNewParityTimePacket N hN η f hc he hr R hR hs)) := by
  let V := completedCuspidalNewParitySpace N hN η
  let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
  have hVC : V ≤ localCuspidalSpace N hN := fun _ hx => hx.1.1
  have hA : IsSelfAdjoint A :=
    Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr
  have hAC : ∀ x ∈ localCuspidalSpace N hN, A x ∈ localCuspidalSpace N hN :=
    fun x hx => shiftedQuotientWavePacket_mem_localCuspidalSpace N hN f _ x hx
  have hsum : Summable (fun i => ‖A (b i : AutomorphicSpace N)‖ ^ 2) := by
    obtain ⟨κ, c, _⟩ := exists_hilbertBasis ℂ (completedCuspidalNewSpace N hN)
    have hv : Orthonormal ℂ (fun i => completedCuspidalNewParityInclusion N hN η (b i)) :=
      ⟨fun i => b.orthonormal.norm_eq_one i,
        fun _ _ hij => b.orthonormal.inner_eq_zero hij⟩
    exact (orthonormal_energy_le c _ hv
      (completedCuspidalNewTimePacket N hN f (f.smooth ⊤) hc)
      (completedCuspidalNewTimePacket_summable N hN c f (f.smooth ⊤) hc)).1
  have hh := nested_projection_energy_hasSum V (localCuspidalSpace N hN)
    hVC b S.basis A hA hAC hsum
  have hscalar (j : S.Index) :
      ‖V.starProjection (A (S.basis j : AutomorphicSpace N))‖ ^ 2 =
        ‖smoothPacketMultiplier f (S.energy j)‖ ^ 2 * newParitySpectralWeight S η j := by
    dsimp only [A]
    rw [Wave.shiftedQuotientWavePacket_eigen N f _ (S.energy_nonneg j) (S.graph j),
      map_smul, norm_smul, mul_pow]
    rfl
  exact hh.congr_fun (fun j => (hscalar j).symm)

/-- The genuine completed-space energy is independent of its Hilbert
basis, including when a sign or parity space is zero. -/
theorem newParityPacket_energy_basis_independent {ι κ : Type*}
    (N : ℕ) [NeZero N] (hN : 0 < N) (η : ℝ)
    (b : HilbertBasis ι ℂ (completedCuspidalNewParitySpace N hN η))
    (c : HilbertBasis κ ℂ (completedCuspidalNewParitySpace N hN η))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t, star (f t) = f t)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    hilbertSchmidtEnergy b (completedCuspidalNewParityTimePacket N hN η f hc he hr R hR hs) =
      hilbertSchmidtEnergy c (completedCuspidalNewParityTimePacket N hN η f hc he hr R hR hs) :=
  (newParityPacket_spectral_energy (geometricCuspSpectrum N hN) η b f hc he hr R hR hs).unique
    (newParityPacket_spectral_energy (geometricCuspSpectrum N hN) η c f hc he hr R hR hs)

#print axioms nested_projection_energy
#print axioms nested_projection_energy_hasSum
#print axioms newParitySpectralWeight_bounds
#print axioms newParityPacket_spectral_energy
#print axioms newParityPacket_energy_basis_independent

end QuantitativeNinaMaass
