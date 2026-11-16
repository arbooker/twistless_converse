module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace QuantitativeMaass

variable {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup J] [NormedSpace ℂ J]

/-- The actual bounded-operator polynomial used in the LV construction;
the intended scale is c=B^{-2}. -/
noncomputable def lvFilter (D : H →L[ℂ] H) (c : ℝ) (d : ℕ) : H →L[ℂ] H :=
  1 - (1 - c • D ^ 2) ^ d

/-- Exact factorization, valid even for d=0, exhibiting the range inclusion
in the range of D rather than merely its closure. -/
theorem lvFilter_factor (D : H →L[ℂ] H) (c : ℝ) (d : ℕ) :
    lvFilter D c d = D * ((c • D) *
      ∑ j ∈ Finset.range d, (1 - c • D ^ 2) ^ j) := by
  unfold lvFilter
  rw [← mul_neg_geom_sum (1 - c • D ^ 2) d, sub_sub_cancel]
  simp only [pow_two, smul_mul_assoc, mul_smul_comm, mul_assoc]

theorem lvFilter_mem_range (D : H →L[ℂ] H) (c : ℝ) (d : ℕ) (x : H) :
    lvFilter D c d x ∈ LinearMap.range D.toLinearMap := by
  rw [lvFilter_factor]
  exact ⟨((c • D) * ∑ j ∈ Finset.range d, (1 - c • D ^ 2) ^ j) x, rfl⟩

/-- Every bounded symmetry commuting with D commutes with the filter. This
applies to parity and to bounded spectral functions once their actual
commutation with the Hecke and wave operators has been established. -/
theorem lvFilter_commute (D K : H →L[ℂ] H) (hKD : Commute K D)
    (c : ℝ) (d : ℕ) : Commute K (lvFilter D c d) := by
  exact (Commute.one_right K).sub_right
    (((Commute.one_right K).sub_right ((hKD.pow_right 2).smul_right c)).pow_right d)

/-- A constant-term map annihilating D annihilates every polynomial
cuspidalizer Q_d. The hypothesis is the genuine intertwining obligation;
this theorem does not claim that it has already been proved at every cusp. -/
theorem lvFilter_constantTerm_zero (D : H →L[ℂ] H) (constantTerm : H →ₗ[ℂ] J)
    (hD : constantTerm.comp D.toLinearMap = 0) (c : ℝ) (d : ℕ) (x : H) :
    constantTerm (lvFilter D c d x) = 0 := by
  obtain ⟨y, hy⟩ := lvFilter_mem_range D c d x
  rw [← hy]
  exact congrArg (fun T : H →ₗ[ℂ] J => T y) hD

/-- The genuine constant-term intertwining hypotheses for the two summands
T and W imply the cuspidalizer conclusion. No quotient spectral decomposition
is assumed here; all three maps and both intertwining identities are explicit. -/
theorem lvFilter_constantTerm_zero_of_intertwining
    (T W : H →L[ℂ] H) (constantTerm : H →ₗ[ℂ] J) (shift : J →ₗ[ℂ] J)
    (hT : constantTerm.comp T.toLinearMap = shift.comp constantTerm)
    (hW : constantTerm.comp W.toLinearMap = shift.comp constantTerm)
    (c : ℝ) (d : ℕ) (x : H) :
    constantTerm (lvFilter (T - W) c d x) = 0 := by
  apply lvFilter_constantTerm_zero
  ext y
  have ht := congrArg (fun A : H →ₗ[ℂ] J => A y) hT
  have hw := congrArg (fun A : H →ₗ[ℂ] J => A y) hW
  change constantTerm (T y - W y) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (ht.trans hw.symm)

/-- Simultaneous zero constant terms at an arbitrary set of cusps. This
states the range conclusion using actual linear kernels, not a presumed
spectral decomposition. -/
theorem lvFilter_mem_cuspidal_kernel {κ : Type*} (D : H →L[ℂ] H)
    (constantTerm : κ → H →ₗ[ℂ] J)
    (hD : ∀ i, (constantTerm i).comp D.toLinearMap = 0)
    (c : ℝ) (d : ℕ) (x : H) :
    lvFilter D c d x ∈ ⨅ i, LinearMap.ker (constantTerm i) := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact fun i => lvFilter_constantTerm_zero D (constantTerm i) (hD i) c d x

theorem operator_power_eigenvector (T : H →L[ℂ] H) (x : H) (z : ℂ)
    (hx : T x = z • x) (d : ℕ) : (T ^ d) x = z ^ d • x := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_succ']
    change T ((T ^ d) x) = (z * z ^ d) • x
    rw [ih, map_smul, hx, smul_smul]
    congr 1
    ring

/-- Exact spectral multiplier of the polynomial filter. -/
theorem lvFilter_eigenvector (D : H →L[ℂ] H) (x : H) (z : ℂ)
    (hx : D x = z • x) (c : ℝ) (d : ℕ) :
    lvFilter D c d x = (1 - (1 - (c : ℂ) * z ^ 2) ^ d) • x := by
  have hsq := operator_power_eigenvector D x z hx 2
  have hbase : (1 - c • D ^ 2 : H →L[ℂ] H) x = (1 - (c : ℂ) * z ^ 2) • x := by
    simp only [sub_apply, one_apply_eq_self, smul_apply, hsq]
    rw [← smul_assoc, Complex.real_smul, sub_smul, one_smul]
  have hp := operator_power_eigenvector (1 - c • D ^ 2) x
    (1 - (c : ℂ) * z ^ 2) hbase d
  simp only [lvFilter, sub_apply, one_apply_eq_self, hp, sub_smul, one_smul]

/-- On the normalized spectral interval the LV polynomial is a positive
contraction. Operator positivity still requires the spectral calculus. -/
theorem lv_multiplier_bounds (d : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ 1 - (1 - z) ^ d ∧ 1 - (1 - z) ^ d ≤ 1 := by
  have hbase : 0 ≤ 1 - z := sub_nonneg.mpr hz1
  have hpow0 := pow_nonneg hbase d
  have hpow1 : (1 - z) ^ d ≤ 1 := pow_le_one₀ hbase (by linarith)
  constructor <;> linarith

#print axioms lvFilter_factor
#print axioms lvFilter_mem_range
#print axioms lvFilter_commute
#print axioms lvFilter_constantTerm_zero
#print axioms lvFilter_constantTerm_zero_of_intertwining
#print axioms lvFilter_mem_cuspidal_kernel
#print axioms operator_power_eigenvector
#print axioms lvFilter_eigenvector
#print axioms lv_multiplier_bounds

end QuantitativeMaass
