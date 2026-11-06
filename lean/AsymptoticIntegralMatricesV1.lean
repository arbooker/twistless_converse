module

public import AsymptoticIntegralSubgroupV1
public import AsymptoticRamifiedBranchV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticIntegralSubgroup

open Matrix AsymptoticMobiusFold

variable (q : ℕ) [Fact q.Prime]

omit [Fact q.Prime] in
theorem integralEntries_adjugate (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hA : IntegralEntries q A) : IntegralEntries q A.adjugate := by
  intro i j
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simpa using hA _ _

/-- Integral entries and a q-adic unit determinant give an integral
inverse. This criterion applies to the literal rational branch matrices. -/
theorem integralGL_of_entries_det (g : GL (Fin 2) ℚ)
    (he : IntegralEntries q g.val) (hd : padicNorm q g.val.det=1) : g∈integralGL q := by
  refine ⟨he,?_⟩
  have hi : padicNorm q (g.val.det)⁻¹=1 := by
    rw [← one_div,padicNorm.div,padicNorm.one,hd,div_one]
  intro i j
  rw [GeneralLinearGroup.coe_inv,Matrix.inv_def,Ring.inverse_eq_inv]
  change padicNorm q (g.val.det⁻¹*g.val.adjugate i j)≤1
  rw [padicNorm.mul,hi,one_mul]
  exact integralEntries_adjugate q g.val he i j

theorem integer_matrix_integral (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (he : ∀ i j,g.val i j=(A i j:ℚ)) (hd : padicNorm q g.val.det=1) : g∈integralGL q := by
  apply integralGL_of_entries_det q g _ hd
  intro i j
  rw [he]
  exact padicNorm.of_int _

/-- The Fricke matrix is integral at every prime away from its positive
integer parameter. -/
theorem fricke_integral (L : ℕ) (hL : L≠0) (hq : ¬q∣L) :
    AsymptoticReconstructionBranch.branch (L:ℚ) 0 0 (by exact_mod_cast hL)∈integralGL q := by
  apply integralGL_of_entries_det
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [AsymptoticReconstructionBranch.branch,GeneralLinearGroup.mkOfDetNeZero,padicNorm.of_nat]
  · change padicNorm q (AsymptoticReconstructionBranch.branch (L:ℚ) 0 0 _).det.val=1
    rw [AsymptoticReconstructionBranch.branch_det]
    exact (padicNorm.nat_eq_one_iff L).mpr hq

omit [Fact q.Prime] in
theorem reconstruction_factor (L b d : ℚ) (hL : L≠0) :
    AsymptoticReconstructionBranch.branch L b d hL=
      translation d*AsymptoticReconstructionBranch.branch L 0 0 hL*translation b := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AsymptoticReconstructionBranch.branch,translation,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem reconstruction_integral (L : ℕ) (hL : L≠0) (hq : ¬q∣L)
    (b d : ℚ) (hb : padicNorm q b≤1) (hd : padicNorm q d≤1) :
    AsymptoticReconstructionBranch.branch (L:ℚ) b d (by exact_mod_cast hL)∈integralGL q := by
  rw [reconstruction_factor]
  exact (integralGL q).mul_mem
    ((integralGL q).mul_mem ((translation_integral_iff q d).mpr hd) (fricke_integral q L hL hq))
    ((translation_integral_iff q b).mpr hb)

/-- The actual ramified U_p branches are integral at every fresh prime
q different from the primes dividing p. -/
theorem ramified_integral (p a : ℕ) (hp : p≠0) (hq : ¬q∣p) :
    AsymptoticRamifiedBranch.branch (p:ℚ) (a:ℚ) (by exact_mod_cast hp)∈integralGL q := by
  apply integralGL_of_entries_det
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [AsymptoticRamifiedBranch.branch,GeneralLinearGroup.mkOfDetNeZero,padicNorm.of_nat]
  · change padicNorm q (AsymptoticRamifiedBranch.branch (p:ℚ) (a:ℚ) _).det.val=1
    rw [AsymptoticRamifiedBranch.branch_det]
    exact (padicNorm.nat_eq_one_iff p).mpr hq

#print axioms integralEntries_adjugate
#print axioms integralGL_of_entries_det
#print axioms integer_matrix_integral
#print axioms fricke_integral
#print axioms reconstruction_factor
#print axioms reconstruction_integral
#print axioms ramified_integral

end AsymptoticIntegralSubgroup
