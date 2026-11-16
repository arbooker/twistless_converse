module

public import QuantitativeMaassSupportedTargetTraceV1
public import QuantitativeMaassApproximateProjectionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open ContinuousLinearMap MeasureTheory
namespace QuantitativeMaass

variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A contractive reconstruction into an orthogonal target gives a
positive lower approximation to that target after any positive contraction
on its source. No convergence to the identity on the source is needed. -/
theorem contractive_target_minorant (Q : H→L[ℂ]H) (hQ : IsSelfAdjoint Q) (hQQ : Q*Q=Q)
    (S : G→L[ℂ]H) (hS : ‖S‖≤1) (hQS : Q.comp S=S)
    (L : G→L[ℂ]G) (hL : 0≤L) (hL1 : L≤1) :
    0≤S.comp (L.comp S.adjoint) ∧ S.comp (L.comp S.adjoint)≤Q := by
  have hp : 0≤S.comp (L.comp S.adjoint) := by
    have hh := (nonneg_iff_isPositive.mp hL).adjoint_conj S.adjoint
    simpa only [adjoint_adjoint] using nonneg_iff_isPositive.mpr hh
  have hc : 0≤S.comp S.adjoint := by
    simpa only [adjoint_adjoint] using
      nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self S.adjoint)
  have hn : ‖S.comp S.adjoint‖≤1 := by
    have hh := opNorm_comp_le S S.adjoint
    rw [adjoint.norm_map] at hh
    exact hh.trans (by nlinarith [norm_nonneg S])
  have hc1 : S.comp S.adjoint≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hc).mp hn
  have hsupp := cogram_supported_of_fixed Q hQ S hQS
  have hcQ : S.comp S.adjoint≤Q := by
    have hh := star_left_conjugate_le_conjugate hc1 Q
    simp only [hQ.star_eq] at hh
    change Q*(S.comp S.adjoint)*Q≤Q*1*Q at hh
    rw [mul_one,hQQ] at hh
    change Q.comp ((S.comp S.adjoint).comp Q)≤Q at hh
    simpa only [hsupp] using hh
  have hdiff : 0≤S.comp ((1-L).comp S.adjoint) := by
    have hh := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hL1)).adjoint_conj S.adjoint
    simpa only [adjoint_adjoint] using nonneg_iff_isPositive.mpr hh
  have hle : S.comp (L.comp S.adjoint)≤S.comp S.adjoint := by
    simpa only [sub_comp,comp_sub,one_def,id_comp,sub_nonneg] using hdiff
  exact ⟨hp,hle.trans hcQ⟩

omit [CompleteSpace H] in
/-- Subtracting such a lower approximation can only increase the excess
trace. This direction avoids any unproved norm approximation to the
cuspidal projection. -/
theorem columnLinearTrace_sub_minorant {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (F Q T : H→L[ℂ]H) (hT : T≤Q) :
    columnLinearTrace μ c (F-Q)≤columnLinearTrace μ c (F-T) :=
  columnLinearTrace_mono μ c hc _ _ (sub_le_sub_left hT F)

#print axioms contractive_target_minorant
#print axioms columnLinearTrace_sub_minorant
end QuantitativeMaass
