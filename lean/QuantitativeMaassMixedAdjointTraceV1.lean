module

public import QuantitativeMaassColumnPairTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open ContinuousLinearMap
namespace QuantitativeMaass

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The sum of two concrete Hilbert-Schmidt operators is Hilbert-Schmidt. -/
theorem hilbertSchmidt_add_summable (b : HilbertBasis ι ℂ V) (A B : V→L[ℂ]V)
    (hA : Summable (fun i => ‖A (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Summable (fun i => ‖(A+B) (b i)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((hA.mul_left 2).add (hB.mul_left 2))
  intro i
  have hh := norm_add_le (A (b i)) (B (b i))
  simp only [add_apply]
  nlinarith [norm_nonneg (A (b i)),norm_nonneg (B (b i)),norm_nonneg (A (b i)+B (b i)),
    sq_nonneg (‖A (b i)‖-‖B (b i)‖)]

theorem hilbertSchmidt_pair_summable (b : HilbertBasis ι ℂ V) (A B : V→L[ℂ]V)
    (hA : Summable (fun i => ‖A (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Summable (fun i => (inner ℂ (A (b i)) (B (b i))).re) := by
  have hh := (((hilbertSchmidt_add_summable b A B hA hB).sub hA).sub hB).div_const 2
  simpa only [add_apply,←re_inner_polarization] using hh

theorem hilbertSchmidt_pair_polarization (b : HilbertBasis ι ℂ V) (A B : V→L[ℂ]V)
    (hA : Summable (fun i => ‖A (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    (∑' i,(inner ℂ (A (b i)) (B (b i))).re)=
      (hilbertSchmidtEnergy b (A+B)-hilbertSchmidtEnergy b A-hilbertSchmidtEnergy b B)/2 := by
  have hab := hilbertSchmidt_add_summable b A B hA hB
  simp_rw [re_inner_polarization,←add_apply]
  rw [tsum_div_const,(hab.sub hA).tsum_sub hB,hab.tsum_sub hA]
  rfl

variable [CompleteSpace V]

/-- Real mixed traces are unchanged by taking both adjoints. This is
proved from actual finite energies, so it does not assume cyclicity of a
possibly non-trace-class formal product. -/
theorem hilbertSchmidt_pair_adjoint (b : HilbertBasis ι ℂ V) (A B : V→L[ℂ]V)
    (hA : Summable (fun i => ‖A (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    (∑' i,(inner ℂ (A (b i)) (B (b i))).re)=
      ∑' i,(inner ℂ (A.adjoint (b i)) (B.adjoint (b i))).re := by
  obtain ⟨hAa,hAe⟩ := adjoint_energy_eq b A hA
  obtain ⟨hBa,hBe⟩ := adjoint_energy_eq b B hB
  have hsum := (adjoint_energy_eq b (A+B) (hilbertSchmidt_add_summable b A B hA hB)).2
  rw [map_add] at hsum
  rw [hilbertSchmidt_pair_polarization b A B hA hB,
    hilbertSchmidt_pair_polarization b A.adjoint B.adjoint hAa hBa,hsum,hAe,hBe]

#print axioms hilbertSchmidt_add_summable
#print axioms hilbertSchmidt_pair_summable
#print axioms hilbertSchmidt_pair_polarization
#print axioms hilbertSchmidt_pair_adjoint
end QuantitativeMaass
