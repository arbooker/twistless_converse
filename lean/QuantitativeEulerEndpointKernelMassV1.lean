module

public import AsymptoticEulerCountTheoremV1
public import AsymptoticInfiniteKernelCountReductionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointKernelMass
open UpperHalfPlane Filter Asymptotics MeasureTheory
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorComparison
open AsymptoticCompactObservationCount AsymptoticRegularObservation
open scoped Topology

/-- A fixed upper slope cannot lie below a proved leading coefficient. -/
theorem leading_le_upper (v : ℕ → ℝ) {c b : ℝ}
    (hv : (fun k => v k-c*(k:ℝ))=o[evenWeights] (fun k => (k:ℝ)))
    (hu : LinearUpper v b) : c≤b := by
  by_contra h
  have hd : 0<c-b := sub_pos.mpr (lt_of_not_ge h)
  have he : 0<(c-b)/3 := by positivity
  have hk : ∀ᶠ k : ℕ in evenWeights, 0<k :=
    (eventually_gt_atTop 0).filter_mono inf_le_left
  obtain ⟨k,hk,hlo,hup⟩ := (hk.and ((hv.bound he).and (hu _ he))).exists
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have habs : |v k-c*(k:ℝ)|≤((c-b)/3)*(k:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hkR.le] using hlo
  have hn := (abs_le.mp habs).1
  nlinarith

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Every finite family of actual original equations retains at least the
classical total leading mass. Uses the independently proved qualitative
count theorem, not the quantitative endpoint being sought. -/
theorem totalRegularTrace_lower (hN : GridAdmissibleGap.Admissible N) (P : Parameters A)
    {ι : Type*} [Fintype ι] (r : ι → Row N) (s : ι → Set ℍ)
    (hs : ∀ i, IsCompact (s i)) :
    4*Real.pi*AsymptoticTotalNewCorner.arithmeticCoefficient N≤
      totalRegularTrace A hN.1 P r s hs := by
  have hu : LinearUpper (fun k => ((FinitenessOriginalInput.S N k).ncard:ℝ))
      (totalRegularTrace A hN.1 P r s hs/(4*Real.pi)) :=
    linearUpper_of_even_index _ _ (fun δ hδ => count_upper_of_fixed_observations A hN.1 P r s hs hδ)
  have h := leading_le_upper _ (AsymptoticEulerCountTheorem.arithmetic_leading_term N hN) hu
  have hπ : 0<4*Real.pi := by positivity
  simpa only [mul_comm] using (le_div_iff₀ hπ).mp h

/-- The same lower mass remains after passing to the exact joint kernel
of any fixed finite family of original rows. -/
theorem totalKernelTrace_lower (hN : GridAdmissibleGap.Admissible N) (P : Parameters A)
    {ι : Type*} [Fintype ι] (r : ι → Row N) (s : ι → Set ℍ)
    (hs : ∀ i, IsCompact (s i)) :
    4*Real.pi*AsymptoticTotalNewCorner.arithmeticCoefficient N≤
      totalKernelTrace A hN.1 P r s hs := by
  apply ge_of_tendsto (repeated_totalTrace_tendsto A hN.1 P r s hs)
  exact Eventually.of_forall (fun n => totalRegularTrace_lower A hN P
    (fun j : Fin ((n+1)^2) × ι => r j.2) (fun j => s j.2) (fun j => hs j.2))

/-- Normality passes the classical lower mass through every countable
family of compact original equations. -/
theorem totalInfiniteKernelTrace_lower (hN : GridAdmissibleGap.Admissible N) (P : Parameters A)
    (r : ℕ → Row N) (s : ℕ → Set ℍ) (hs : ∀ i, IsCompact (s i)) :
    4*Real.pi*AsymptoticTotalNewCorner.arithmeticCoefficient N≤
      totalInfiniteKernelTrace A hN.1 P r s hs := by
  apply ge_of_tendsto (finite_totalKernelTrace_tendsto A hN.1 P r s hs)
  exact Eventually.of_forall (fun n => totalKernelTrace_lower A hN P
    (fun i : Fin n => r i) (fun i => s i) (fun i => hs i))

/-- The actual common kernel of ALL original compact equations has exactly
the classical leading trace. This is an equality of regular traces; it does
not assert a quantitative spectral gap or a finite-count rate. -/
theorem universal_kernel_total_trace (hN : GridAdmissibleGap.Admissible N)
    (P : Parameters A) (K : CompactExhaustion ℍ) :
    totalInfiniteKernelTrace A hN.1 P (familyRows (universalRows N))
      (familyRegions K) (familyRegions_compact K)=
        4*Real.pi*AsymptoticTotalNewCorner.arithmeticCoefficient N := by
  apply le_antisymm
  · exact (totalInfiniteKernelTrace_le_incidence A hN.1 P K).trans
      (AsymptoticTotalNewCorner.totalTrace_le_arithmetic N hN
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos (by omega))
  · exact totalInfiniteKernelTrace_lower A hN P _ _ _

#print axioms totalRegularTrace_lower
#print axioms totalKernelTrace_lower
#print axioms totalInfiniteKernelTrace_lower
#print axioms universal_kernel_total_trace
end QuantitativeEulerEndpointKernelMass
